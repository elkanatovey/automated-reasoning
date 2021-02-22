from propositions.sat_helper import *
import random

SAT_MSG = "SAT "
UNSAT_MSG = "UNSAT "

class Sat_Solver:

    VSIDS_dict: {str, int}
    assignment_dict: {}  # T,F, None
    decision_level_history: {int: DecisionLevel}

    def __init__(self, cnf_formula: Formula):
        self.formula = cnf_formula
        self.wv_db = WatchVariableDb()
        self.variables = cnf_formula.variables()
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
                flag = True
                for key in self.assignment_dict:
                    if self.assignment_dict[key] is None:
                        flag = False
                        break
                if flag:
                    return SAT_MSG, self.assignment_dict

            elif self.assignment_dict[wv] == clause.is_positive_variable(wv):
                continue
            else:
                return UNSAT_MSG, None

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
        self.level += 1
        self.li_unit_clauses[self.level] = []
        decision_variable = self.__largest_available_vsids_member()
        decision = random.sample([True, False], 1)[0]

        # update relevant dbs
        self.assignment_dict[decision_variable] = decision
        self.update_graph(decision_variable)
        self.decision_level_history[self.level] = DecisionLevel(decision_variable)

        return decision_variable

    def propagate(self, unit_variable: str):
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
        """unit propagate at current level
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
        """unit propagate at current level
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
        uip = self.decision_level_history[self.level].find_first_uip(clause, self.nodes)

        last_assigned = self.decision_level_history[self.level].find_last_assigned_literal(clause)
        c_tag = self.nodes[last_assigned].get_parent_clause()
        current = clause.resolve(c_tag)

        while uip not in current.get_variables():
            last_assigned = self.decision_level_history[self.level].find_last_assigned_literal(current)
            c_tag = self.nodes[last_assigned].get_parent_clause()
            current = clause.resolve(c_tag)

        return current


        ## self.li_unit_clauses = {} # {int: units}
        # self.decision_level_history = {self.level: DecisionLevel('start')}
        # self.nodes = dict((k, ImplicationNode(k, None)) for k in list(self.variables))
        # self.assignment_dict = dict.fromkeys(list(self.variables), )
        # self.level = 0

    def backtrack(self, backtrack_level: int, conflict_clause: Clause):
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



    def __largest_available_vsids_member(self):
        max = -1
        best_key = None
        for key in self.VSIDS_dict:
            if self.assignment_dict[key] is None:
                if max < self.VSIDS_dict[key]:
                    best_key = key
                    max = self.VSIDS_dict[key]
        assert best_key is not None # @todo maybe if key wasn't found, we've found good assignment?
        return best_key
