import copy
# from typing import MutableMapping

from propositions.syntax import *

# list of positive vars in clause
P_C = List[str]
# tuple of positive vars in clause
Positive_Cvars = Tuple[str]

# list of negative vars in clause
N_C = List[str]
# tuple of negative vars in clause
Negative_Cvars = Tuple[str]


class Clause:
    """If clause is newly unit than wv1 should be updated to contain the unit variable to be propagated"""

    positive_variables: Positive_Cvars
    negative_variables: Negative_Cvars
    first_wv: str
    second_wv: str
    __is_unit_clause: bool

    def __init__(self, clause: Tuple[P_C, N_C]) -> None:
        self.positive_variables = tuple(clause[0])
        self.negative_variables = tuple(clause[1])

        self.first_wv = list(self.positive_variables + self.negative_variables)[0]
        if len(self.positive_variables) + len(self.negative_variables) == 1:
            self.__is_unit_clause = True
            # set second?

        else:
            self.second_wv = list(self.positive_variables + self.negative_variables)[1]
            self.__is_unit_clause = False

    def __eq__(self, other: object) -> bool:
        return isinstance(other, Clause) and str(self) == str(other)

    def __ne__(self, other: object) -> bool:
        return not self == other

    def __hash__(self) -> int:
        return hash(str(self))

    def __repr__(self) -> str:
        return str(sorted(self.positive_variables)) + "  " + "~" + str(sorted(self.negative_variables))

    def is_unit_clause(self) -> bool:
        if self.__is_unit_clause:
            return True
        return False


    def get_wv1(self):
        return self.first_wv

    def set_wv1(self, wv: str):
        assert wv in self.positive_variables or wv in self.negative_variables
        self.first_wv = wv

    def get_wv2(self):
        return self.second_wv

    def set_wv2(self, wv: str):
        assert not self.__is_unit_clause
        assert wv in self.positive_variables or wv in self.negative_variables
        self.second_wv = wv

    def is_positive_variable(self, var: str) -> bool:
        assert var in self.positive_variables or var in self.negative_variables
        return var in self.positive_variables

    def get_variables(self):
        variables = set(self.positive_variables).union(set(self.negative_variables))
        return variables

    def resolve(self, other):
        """resolve current clause with other clause
        - returns new unified clause without conflicting literal
        """
        other_pos = set(other.positive_variables)
        other_neg = set(other.negative_variables)

        local_pos = set(self.negative_variables)
        local_neg = set(self.negative_variables)

        pos = other_pos | local_pos
        neg = other_neg | local_neg
        conflict_literal = pos & neg
        assert len(conflict_literal) == 1
        pos.difference_update(conflict_literal)
        neg.difference_update(conflict_literal)
        pos = list(pos)
        neg = list(neg)
        resolvent = Clause(tuple((pos, neg)))
        return resolvent

    def is_newly_unit(self, assignment_dict: {}, v: str): #@todo may be unnecessary
        """helper function for
        >>>self.find_legal_wv()
         - check if new wv assignment is unit and return accordingly
          - in unit case makes sure that unit wv is in first
        """
        if assignment_dict[v] is not None:
            return [v, None]

        if assignment_dict[self.first_wv] is None and assignment_dict[self.second_wv] is not None:
            return [self.first_wv, True]
        if assignment_dict[self.second_wv] is None and assignment_dict[self.first_wv] is not None:
            var = self.get_wv2()
            self.set_wv2(self.get_wv1())
            self.set_wv1(var)
            return [self.first_wv, True]
        return [v, None]


    def find_legal_wv(self, wv_to_replace: str, assignment_dict: {}):
        """Assumes clause is not unit
        if clause is newly unit -update return variable
        if clause is non unit - update + return true
        if clause is contradiction return false

        """
        assert not self.__is_unit_clause
        assert wv_to_replace == self.second_wv or wv_to_replace == self.first_wv

        # already true case
        if self.is_positive_variable(self.first_wv) is assignment_dict[self.first_wv] or \
                self.is_positive_variable(self.second_wv) is assignment_dict[self.second_wv]:
            return [True, None]

        # non unit new wv case #@todo go over this
        for v in self.negative_variables:
            if assignment_dict[v] is not True or assignment_dict[v] is None:
                if v != self.first_wv and v != self.second_wv:
                    if self.first_wv == wv_to_replace:
                        self.set_wv1(v)
                    else:
                        self.set_wv2(v)
                    return self.is_newly_unit(assignment_dict, v)
        for v in self.positive_variables:
            if assignment_dict[v] is not False or assignment_dict[v] is None:
                if v != self.first_wv and v != self.second_wv:
                    if self.first_wv == wv_to_replace:
                        self.set_wv1(v)
                    else:
                        self.set_wv2(v)
                    return self.is_newly_unit(assignment_dict, v)

        # newly unit case
        if assignment_dict[self.first_wv] is None or \
                assignment_dict[self.second_wv] is None:
            if self.first_wv == wv_to_replace:
                self.first_wv = self.second_wv
                self.second_wv = wv_to_replace
            return [self.first_wv, True]

        # contradiction case
        return [None, False]


# clauses watched by x  accdng to x, ~x
P_Clauses_WATCHED = List[Clause]
N_Clauses_WATCHED = List[Clause]
# all clauses watched by x
# WATCHED_CLAUSES = List[P_Clauses_WATCHED, N_Clauses_WATCHED]

# master dict of watched clauses
# WATCH_VARIABLES_DICT = MutableMapping[str, WATCHED_CLAUSES]
POSITIVES = 0
NEGATIVES = 1


class WatchVariableDb:
    watch_variable_dict: {} #MutableMapping[str, WATCHED_CLAUSES]

    def __init__(self, variables: set) -> None:
        self.watch_variable_dict = {}
        for var in variables:
            self.watch_variable_dict[var] = [[], []]

    def insert_clause_wv_to_wvdict(self, clause: Clause, wv: str):
        """insert clause-wv pair to dict, does not verify correctness or remove old wvs"""
        if wv not in self.watch_variable_dict.keys():
            self.watch_variable_dict[wv] = [[], []]
        if clause.is_positive_variable(wv):
            self.watch_variable_dict[wv][POSITIVES].append(clause)
        else:
            self.watch_variable_dict[wv][NEGATIVES].append(clause)

    def insert_clause_to_wv_db_l0(self, clause: Clause):
        wv1 = clause.get_wv1()
        self.insert_clause_wv_to_wvdict(clause, wv1)

        if not clause.is_unit_clause():
            wv2 = clause.get_wv2()
            self.insert_clause_wv_to_wvdict(clause, wv2)

    def get_clauses_to_be_fixed(self, wv: str, illegal_setting: bool):
        """returns clauses with bad watch variable"""  #@todo clauses here don't get updated when the other wv changes
        if illegal_setting:
            bad_clauses = self.watch_variable_dict[wv][POSITIVES]
            self.watch_variable_dict[wv][POSITIVES] = []
            return bad_clauses
        else:
            bad_clauses = self.watch_variable_dict[wv][NEGATIVES]
            self.watch_variable_dict[wv][NEGATIVES] = []
            return bad_clauses

    def positive_len(self, var):
        return len(self.watch_variable_dict[var][POSITIVES])

    def negative_len(self, var):
        return len(self.watch_variable_dict[var][NEGATIVES])


class ImplicationNode:
    """
    Represents a node in an implication graph. Each node contains
    - its value
    - its implication children (list)
    - parent nodes (list)
    """

    def __init__(self, variable: str, value: Union[bool, None]):
        self.variable = variable
        self.value = value
        self.level = -1
        self.parents = []
        self.children = []
        self.clause = None

    def __str__(self):
        sign = '+' if self.value == True else '-' if self.value == False else '?'
        return "[{}{}:L{}, {}p, {}c, {}]".format(
            sign, self.variable, self.level, len(self.parents), len(self.children), self.clause)

    def __repr__(self):
        return str(self)

    def get_parent_clause(self):
        return self.clause

    def all_paths_to_conflict_clause(self, conflict_variables: set):
        """given set of conflict variables find all paths from current node to
        conflict variables, if empty return []"""
        if self.variable in conflict_variables:
            return [[self.variable]]

        all_paths = []
        for child in self.children:
            child_paths = child.all_paths_to_conflict_clause(conflict_variables)
            for path in child_paths:
                if path:
                    all_paths.append([self.variable] + path)
        return all_paths



class DecisionLevel:
    """
    Represents history in a decision level. Each DecisionLevel contains
    - its decision variable
    - its implication children (list) in order of assignment
    """
    decision_variable: str
    assignment_history: []

    def __init__(self, variable: str):
        self.decision_variable = variable
        self.assignment_history = [self.decision_variable]

    def __str__(self):
        return "dvar: " + str(self.decision_variable) + " hist: " + str(self.assignment_history)

    def __repr__(self):
        return str(self)

    def add_assignment(self, v: str):
        self.assignment_history.append(v)

    def find_last_assigned_literal(self, clause: Clause) -> str:
        clause_vars = clause.get_variables()
        for var in reversed(self.assignment_history):
            if var in clause_vars:
                return var
        assert False

    def find_first_uip(self, clause: Clause, nodes_dict: {}):
        conflict_vars = clause.get_variables()
        all_paths = nodes_dict[self.decision_variable].all_paths_to_conflict_clause(conflict_vars)

        if len(all_paths) == 1:
            return all_paths[0][-1] # single path, last lit  is uip

        p1 = all_paths[0]
        path_intersections = set(p1)
        for path in all_paths:
            path_intersections.intersection_update(set(path))

        for ip in reversed(p1):
            if ip in path_intersections:
                return ip

    def get_assignment_history(self):
        return self.assignment_history


VSIDS_DICT = MutableMapping[str, int]
