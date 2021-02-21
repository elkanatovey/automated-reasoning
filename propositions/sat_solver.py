from propositions.sat_helper import *
SAT_MSG = "SAT "
UNSAT_MSG = "UNSAT "

class Sat_Solver:

    VSIDS_dict: {str, int}
    assignment_dict: {}  # T,F, None

    def __init__(self, cnf_formula: Formula):
        self.formula = cnf_formula

        self.wv_db = WatchVariableDb()
        self.variables = cnf_formula.variables()
        self.VSIDS_dict = {}
        for variable in self.variables:
            self.VSIDS_dict[variable] = 0

        self.assignment_dict = dict.fromkeys(list(self.variables), )
        self.nodes = dict((k, ImplicationNode(k, None)) for k in list(self.variables))
        self.level = 0

        self.l0_unit_clauses = []

        clauses = Formula.get_clauses(cnf_formula)
        # self.clause_list = []
        for clause in clauses:
            current_clause = Clause(clause)
            for var in current_clause.get_variables():
                self.VSIDS_dict[var] += 1

            self.wv_db.insert_clause_wv_to_wvdict(current_clause, current_clause.get_wv1())
            if not current_clause.is_unit_clause():
                self.wv_db.insert_clause_wv_to_wvdict(current_clause, current_clause.get_wv2())
            else:
                self.l0_unit_clauses.append(tuple([current_clause, None])) # to be dealt with in start_sat() - edge case for convenience

    def update_graph(self, var: str, clause: Union[Clause, None] = None):
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
            if self.assignment_dict[wv] is None or self.assignment_dict[wv] == clause.is_positive_variable(wv):
                self.assignment_dict[wv] = clause.is_positive_variable(wv)
                self.update_graph(wv, implication)
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

            else:
                return UNSAT_MSG, None

    def propagate_l0(self, unit_variable: str): # x,y (~x|~y)
        illegal_setting = not self.assignment_dict[unit_variable]

        clauses_to_update = self.wv_db.get_clauses_to_be_fixed(unit_variable, illegal_setting)
        for clause in clauses_to_update:
            if clause.is_unit_clause(): # l0 is false, other cases resolve
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