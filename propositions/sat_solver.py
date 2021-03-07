from propositions.sat_helper import *
import random

SAT_MSG = "SAT "
UNSAT_MSG = "UNSAT "
BACKTRACK_MSG = "Post Backtrack "

class Sat_Solver:

    VSIDS_dict: {str, int}
    assignment_dict: {}  # T,F, None
    decision_level_history: {int: DecisionLevel}

    def __init__(self, cnf_formula: Formula):
        self.formula = cnf_formula
        self.variables = cnf_formula.variables()
        self.wv_db = WatchVariableDb(self.variables)
        self.VSIDS_dict = {}
        for variable in self.variables:
            self.VSIDS_dict[variable] = 0

        self.assignment_dict = dict.fromkeys(list(self.variables), )
        self.nodes = dict((k, ImplicationNode(k, None)) for k in list(self.variables))  # {var : node}
        self.level = 0
        self.decision_level_history = {self.level: DecisionLevel('start')}

        # unit clauses to propagate by level
        self.l0_unit_clauses = [] # tuple of level unit clauses with itself for propagation
        self.li_unit_clauses = {} # {int: units}

        # insert clauses
        clauses = Formula.get_clauses(cnf_formula)
        for clause in clauses:
            current_clause = Clause(clause)
            self.add_clause_to_db(current_clause)


    def add_clause_to_db(self, current_clause: Clause):
        """add clauses to wv db at l0"""
        for var in current_clause.get_variables():
            self.VSIDS_dict[var] += 1
        self.wv_db.insert_clause_wv_to_wvdict(current_clause, current_clause.get_wv1())
        if not current_clause.is_unit_clause():
            self.wv_db.insert_clause_wv_to_wvdict(current_clause, current_clause.get_wv2())
        else:
            self.l0_unit_clauses.append(
                tuple([current_clause, None]))  # to be dealt with in start_sat() - edge case for convenience

    def add_conflict_clause_to_db(self, current_clause: Clause):
        """add conflict clause to db and update vsids dict"""
        for key in self.VSIDS_dict.keys():
            self.VSIDS_dict[key] /=2
        for var in current_clause.get_variables():
            self.VSIDS_dict[var] += 1
        self.wv_db.insert_clause_wv_to_wvdict(current_clause, current_clause.get_wv1())
        if not current_clause.is_unit_clause():
            self.wv_db.insert_clause_wv_to_wvdict(current_clause, current_clause.get_wv2())

    def update_graph(self, var: str, clause: Union[Clause, None] = None):
        """add node to implication graph"""
        node = self.nodes[var]
        node.value = self.assignment_dict[var]
        node.level = self.level

        # update parents
        if clause:  # clause is None means parent does not exist
            for v in clause.get_variables():
                if v != var:
                    node.parents.append(self.nodes[v])
                    self.nodes[v].children.append(node)
            node.clause = clause

    def start_sat(self):
        """l0 unit propagate"""
        for clause, implication in self.l0_unit_clauses:
            wv = clause.get_wv1()
            if self.assignment_dict[wv] is None:
                self.add_lit_assignment(wv, clause, implication)
                l1 = self.propagate_l0(wv)
                if l1 is False:
                    return UNSAT_MSG, None

            elif self.assignment_dict[wv] == clause.is_positive_variable(wv):
                continue
            else:
                return UNSAT_MSG, None

        return True, None

    def propagate_l0(self, unit_variable: str): # x,y (~x|~y)
        illegal_setting = not self.assignment_dict[unit_variable]

        clauses_to_update = self.wv_db.get_clauses_to_be_fixed(unit_variable, illegal_setting)
        for clause in clauses_to_update:
            if clause.is_unit_clause():  # l0 is false, other cases resolve
                return False

            status = clause.find_legal_wv(unit_variable, self.assignment_dict)
            if status[0] is True and status[1] is None: # already true case
                self.wv_db.insert_clause_wv_to_wvdict(clause, unit_variable)
            elif status[1] is None:  # non unit new wv case
                self.wv_db.insert_clause_wv_to_wvdict(clause, status[0])
            elif status[1] is True: # newly unit case
                self.l0_unit_clauses.append(tuple([clause, clause]))
            elif status[1] is False:  # contradiction case
                self.wv_db.insert_clause_wv_to_wvdict(clause, unit_variable)
                return False  # at l0 false, other levels resolve
        return True

    def decide(self):
        """decide new var,
        -return decision variable if found
        -else; return sat with assignments
        """
        self.level += 1
        self.li_unit_clauses[self.level] = []
        decision_variable = self.__largest_available_vsids_member()
        if decision_variable is True:
            return SAT_MSG, self.assignment_dict
        if self.wv_db.positive_len(decision_variable) > self.wv_db.negative_len(decision_variable):
            decision = True
        else:
            decision = False
        # decision = random.sample([True, False], 1)[0]
        # decision=True

        # update relevant dbs
        self.assignment_dict[decision_variable] = decision
        self.update_graph(decision_variable)
        self.decision_level_history[self.level] = DecisionLevel(decision_variable)

        return decision_variable, None


    def t_update(self, decision_variable, assignment):
        """pretend to decide new var that is updated based on theory solver,
        -return (decision_variable), if not been set yet
        -return (False) if contradicts old setting
        -return (True) if already been set as such
        """

        # not set yet case
        if self.assignment_dict[decision_variable] is None:
            self.level += 1
            self.li_unit_clauses[self.level] = []
        # update relevant dbs
            self.assignment_dict[decision_variable] = assignment
            self.update_graph(decision_variable)
            self.decision_level_history[self.level] = DecisionLevel(decision_variable)
            return decision_variable

        # set true case
        elif self.assignment_dict[decision_variable] == assignment:
            return True
        # contradicting previous assignment case
        else:
            return False

    def propagate(self, unit_variable: str):
        """:returns
        - (True, None) if propagated successfully,
        - (conflict clause, backjump level) if ran into conflict
        - (UNSAT_MSG, None) if conflict at level 0
        """
        # restarted l0
        if self.level == 0:
            return self.start_sat()

        # all other levels
        else:
            # post backtrack check - don't need to prime unit clauses
            if unit_variable is not BACKTRACK_MSG:
                conflict_clause = self.propagate_s1_s3(unit_variable)
                if conflict_clause is not True:
                    conflict_clause = self.get_conflict_clause(conflict_clause)
                    conflict_clause, backjump_level = self.second_highest_node_level(conflict_clause)
                    return conflict_clause, backjump_level

            conflict_clause = self.propagate_s2()
            if conflict_clause is not True:
                conflict_clause = self.get_conflict_clause(conflict_clause)
                conflict_clause, backjump_level = self.second_highest_node_level(conflict_clause)
                return conflict_clause, backjump_level

        return True, None

    def propagate_s2(self):
        """Update forced assignments that follow from clauses in self.li_unit_clauses at current level.
        After each forced assignment call self.propagate_s1_s3 with newly assigned variable. If self.propagate_s1_s3
        returns clause we are in conflict and have found a contradiction clause which we return. Otherwise return True
        unit propagate at current level
        - return True if propagates successfully
        - otherwise return conflict clause
        """
        for clause, implication in self.li_unit_clauses[self.level]:
            wv = clause.get_wv1()
            if self.assignment_dict[wv] is None:  # not set
                self.add_lit_assignment(wv, clause, implication)
                li = self.propagate_s1_s3(wv)
                if li is not True:
                    return li

            elif self.assignment_dict[wv] == clause.is_positive_variable(wv):
                continue
            else:
                assert False, "Shouldn't evaluate to false here"

        return True


    def propagate_s1_s3(self, unit_variable: str): # x,y (~x|~y)
        """ given variable freshly assigned in self.assignment_dict, replace as watch variable from clauses that negate
        variables assignment. If variable is newly unit clause, add to current level's self.li_unit_clauses
        (the forced assignment queue to propagate), if clause is contradicted, return clause
        at all times coherence within self.wv_db is maintained.
        unit propagate at current level
        - return True if propagates successfully
        - otherwise return conflict clause
        """
        illegal_setting = not self.assignment_dict[unit_variable]

        clauses_to_update = self.wv_db.get_clauses_to_be_fixed(unit_variable, illegal_setting)
        for clause in clauses_to_update:

            status = clause.find_legal_wv(unit_variable, self.assignment_dict)
            if status[0] is True and status[1] is None: # already true case
                self.wv_db.insert_clause_wv_to_wvdict(clause, unit_variable)
            elif status[1] is None:  # non unit new wv case
                self.wv_db.insert_clause_wv_to_wvdict(clause, status[0])
            elif status[1] is True: # newly unit case
                self.li_unit_clauses[self.level].append(tuple([clause, clause]))


            elif status[1] is False:  # contradiction case
                self.wv_db.insert_clause_wv_to_wvdict(clause, unit_variable)

                return clause
                # return False  # at l0 false, other levels resolve
        return True

    def get_conflict_clause(self, clause: Clause) -> Clause:
        """resolve conflict clause until uip within then return new conflict clause"""
        uip = self.decision_level_history[self.level].find_first_uip(clause, self.nodes)

        last_assigned = self.decision_level_history[self.level].find_last_assigned_literal(clause)
        c_tag = self.nodes[last_assigned].get_parent_clause()
        current = clause.resolve(c_tag)

        while uip not in current.get_variables():
            last_assigned = self.decision_level_history[self.level].find_last_assigned_literal(current)
            c_tag = self.nodes[last_assigned].get_parent_clause()
            current = clause.resolve(c_tag)

        return current

    def backtrack(self, conflict_clause: Clause, backtrack_level: int,):
        # add clause to wv db
        self.add_conflict_clause_to_db(conflict_clause)

        # add to levels unit clauses
        if backtrack_level == 0:
            if conflict_clause.is_unit_clause():
                self.l0_unit_clauses = [tuple([conflict_clause, None])]
            else:
                self.l0_unit_clauses = [tuple([conflict_clause, conflict_clause])]
        else:
            self.li_unit_clauses[backtrack_level] = [tuple([conflict_clause, conflict_clause])]

        # erase previous levels
        for i in range(self.level, backtrack_level, -1):
            del self.li_unit_clauses[i]
            for var in reversed(self.decision_level_history[i].get_assignment_history()):
                self.reset_current_node(var, backtrack_level)
                self.assignment_dict[var] = None
            del self.decision_level_history[i]
        self.level = backtrack_level


    def reset_current_node(self, var, backjump_level):
        """erase node from implication graph when backjumping"""
        node = self.nodes[var]
        for parent in node.parents:
            self.nodes[parent.variable].children = [child for child in node.children if child.level <= backjump_level]
        node.value = None
        node.level = -1
        node.parents = []
        node.children = []
        node.clause = None


    def add_lit_assignment(self, wv: str, clause: Clause, implication):
        """update assignment that arises from bcp"""

        self.assignment_dict[wv] = clause.is_positive_variable(wv)
        self.decision_level_history[self.level].add_assignment(wv)
        self.update_graph(wv, implication)

    def second_highest_node_level(self, clause: Clause):
        """find second highest assignment level of clause update so first wv is said assignment"""

        variables = clause.get_variables()

        max = -2
        current_var = None
        for variable in variables:
            if self.nodes[variable].level > max:
                max = self.nodes[variable].level
                current_var = variable

        backjump_level = -2
        for variable in variables:
            if max > self.nodes[variable].level > backjump_level:
                backjump_level = self.nodes[variable].level

        if backjump_level != -2:
            if clause.get_wv1() == current_var:
                return clause, backjump_level
            else:
                clause.set_wv2(clause.get_wv1())
                clause.set_wv1(current_var)
                return clause, backjump_level
        else:
            return clause, 0

    def create_clause_jump_level(self, c)->[Clause, int]:
        """generate clause in correct format for theory conflict"""
        c = Clause(c)
        c, jump_level = self.second_highest_node_level(c)
        return c, jump_level

    def __largest_available_vsids_member(self):
        """return best key if remains, else return true, break ties by lexicographically smaller key"""
        max = -1
        best_key = True
        for key in self.VSIDS_dict:
            if self.assignment_dict[key] is None:
                if max < self.VSIDS_dict[key]:
                    best_key = key
                    max = self.VSIDS_dict[key]
                elif max == self.VSIDS_dict[key]:  # key must be an str here
                    if key < best_key:
                        best_key = key
        return best_key
