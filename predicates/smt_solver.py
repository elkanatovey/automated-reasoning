import predicates.syntax
import networkx as nx
import predicates.syntax as pred
from copy import deepcopy

SAT_MSG = "SAT "
UNSAT_MSG = "UNSAT "
BACKTRACK_MSG = "Post Backtrack "

class SmtSolver:
    dag: nx.DiGraph
    nodes: {}
    positive_equalities: set
    negative_equalities: set

    def __init__(self, formula: str) -> None:
        formula = predicates.syntax.Formula.parse(formula)
        assert formula is not None
        self.propositional_skeleton, self.z2f, self.f2z = formula.propositional_skeleton_mappings()
        pos_prop, negs_prop = set(), set()
        self.formula = formula

        # pos and negative vars
        clauses = self.propositional_skeleton.get_clauses()
        for clause in clauses:
            pos_prop.update(clause[0])
            negs_prop.update(clause[1])

        top_level_terms = set()
        self.positive_equalities, self.negative_equalities = set(), set()
        for pos in pos_prop:
            self.positive_equalities.add(self.z2f[pos])
            top_level_terms.update(self.z2f[pos].arguments)
        for neg in negs_prop:
            self.negative_equalities.add(self.z2f[neg])
            top_level_terms.update(self.z2f[neg].arguments)

        self.dag, self.nodes = build_dag(top_level_terms)
        self.level = 0

    def __repr__(self) -> str:
        return str(self.dag) + " positives: " + str(self.positive_equalities) + " negatives: " + str(
            self.negative_equalities)

    def __eq__(self, other: object) -> bool:
        return isinstance(other, SmtSolver) and str(self) == str(other)

    def __ne__(self, other: object) -> bool:
        return not self == other

    def __hash__(self) -> int:
        return hash(str(self))

    def _get_t1_t2_termclass(self, current_nodes, formula):
        """returns TermClass version of nodes"""
        return  current_nodes[formula.arguments[0]], current_nodes[formula.arguments[1]]

    def _get_t1_t2(self, current_nodes, formula):
        """returns Term version of nodes"""
        return  current_nodes[formula.arguments[0]].term, current_nodes[formula.arguments[1]].term

    def level_up(self):
        self.level += 1
        return self.level

    def t_propagate(self, assignments: {}):
        """
        - return (UNSAT, False) if falsified at level 0
        - return (UNSAT, True) if falsified at other level
        - return (SAT, {}) if finished propagation and no contradiction
        - return (SAT, {var: setting}) if there are new theory lemmas to propagate
        - return (SAT, True) if all settings have been set and suits congruence closure algorithm
        """
        current_nodes = deepcopy(self.nodes)
        to_propagate = {}
        finished_propagation = True

        for var in assignments.keys():
            if assignments[var] is True:
                var_as_f = self.z2f[var]
                t1, t2 = self._get_t1_t2_termclass(current_nodes, var_as_f)
                t1.process_equality(t2, current_nodes)

        for key in assignments.keys():
            key_as_f = self.z2f[key]
            t1, t2 = self._get_t1_t2(current_nodes, key_as_f)

            # check for conflict
            if assignments[key] is False:
                if TermClass.find(t1, current_nodes) == TermClass.find(t2, current_nodes):
                    if self.level == 0:
                        return UNSAT_MSG, False
                    # conflict clause case
                    else:
                        return UNSAT_MSG, True

                # check for stuff to propagate
            elif assignments[key] is None:
                finished_propagation = False
                if TermClass.find(t1, current_nodes) == TermClass.find(t2, current_nodes):
                    to_propagate[key] = True

        if finished_propagation == True:
            return SAT_MSG, finished_propagation
        return SAT_MSG, to_propagate

    def t_explain(self, dpoints_assignments: []):
        pos = []
        neg = []
        for var in dpoints_assignments:
            if var[1] == True:
                neg.append(var[0])
            elif var[1] == False:
                pos.append(var[0])
        dpoints_assignments.pop()
        return tuple([pos, neg])

    def t_backtrack(self, backtrack_level):
        self.level = backtrack_level






def _build_dag_term_helper(g: nx.DiGraph(), term: pred.Term, node_dict):
    # base case
    if not pred.is_function(term.root):
        return

    if term not in node_dict.keys():
        t1 = TermClass(term, parents=set())
        node_dict[term] = t1
    else:
        t1 = node_dict[term]
    for sub_term in term.arguments:
        if sub_term not in node_dict.keys():
            t2 = TermClass(sub_term, parents={t1})
            node_dict[sub_term] = t2
        else:
            t2 = node_dict[sub_term]
            t2.add_parent(t1)

        g.add_edge(t1, t2)
        _build_dag_term_helper(g, sub_term, node_dict)


def build_dag(terms: [pred.Term]) -> [nx.DiGraph, {}]:
    """build a dag from termlist including subterms. Each term is a node with edges to it's subterms.
    :returns an nx.DiGraph() which is the dag"""
    g = nx.DiGraph()
    nodes = {}
    for term in terms:
        _build_dag_term_helper(g, term, nodes)
    return g, nodes


def get_sat_l0():
    pass


from copy import copy

"""
Union-find data structure.
"""


class TermClass:
    parents: set

    def __init__(self, term, parents):
        self.find = self
        self.term = term
        self.parents = parents

    def __repr__(self) -> str:
        return str(self.term)

    def __eq__(self, other: object) -> bool:
        return str(self) == str(other)

    def __ne__(self, other: object) -> bool:
        return not self == other

    def __hash__(self) -> int:
        return hash(str(self))

    def get_representative(self):
        """get representative of current equivalence class - implements find"""
        current_rep = self.find
        current_term = self
        while current_term != current_rep:
            current_term = current_rep
            current_rep = current_rep.find
        return current_rep

    def add_parent(self, p):
        assert isinstance(p, TermClass)
        rep = self.get_representative()
        rep.parents.add(p)

    def merge_classes(self, t2):
        # find reps
        rep = self.get_representative()
        t2_rep = t2.get_representative()

        # update parents
        t1_parents = copy(rep.parents)
        rep.parents = set()
        t2_parents = copy(t2_rep.parents)
        t2_rep.parents = t1_parents.union(t2_rep.parents)

        # change rep of t1 to t2 now t2 reps class
        rep.find = t2_rep

        # return parents for congruence closure
        return t1_parents, t2_parents

    def process_equality(self, t2, node_dict):
        if self.get_representative() == t2.get_representative():
            return

        t1_parents, t2_parents = self.merge_classes(t2)
        for t1_par in t1_parents:
            for t2_par in t2_parents:
                if t1_par.is_congruent(t2_par, node_dict):
                    t1_par.process_equality(t2, node_dict)

    def is_congruent(self, t2, node_dict):
        # comparison against self
        if self == t2:
            return True
        # same function name or same literal name
        if self.term.root == t2.term.root:
            if not pred.is_function(self.term.root):
                return True

            if len(self.term.arguments) == len(t2.term.arguments):
                for i in range(0, len(self.term.arguments)):
                    if TermClass.find(self.term.arguments[i], node_dict) != TermClass.find(self.term.arguments[i], node_dict):
                        return False
                return True
        return False

    @staticmethod
    def find(subterm, node_dict):
        """expects subterm to be of class Term, returns representative of term given node_dict"""
        return node_dict[subterm].get_representative()
