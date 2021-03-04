# propositional imports
from propositions.syntax import Formula as propositional_Formula
import propositions.operators as propositional_operators
import propositions.semantics as propositional_semantics

# predicate imports
from predicates.syntax import Formula as predicate_Formula


# msgs
from propositions.sat_solver import Sat_Solver
from propositions.sat_solver import UNSAT_MSG
from propositions.sat_solver import SAT_MSG
from propositions.sat_solver import BACKTRACK_MSG

BUG_MSG = "This shouldn't be here"

def run_sat_solver(formula: str):
    """preprocess non cnf formula with redundancies and then hand off to sat solver"""
    f_prop = propositional_Formula.parse(formula)

    #tseitin and preprocessing
    f_tseitin = propositional_operators.to_tseitin(f_prop)
    f_tseitin_processed = propositional_operators.preprocess_clauses(f_tseitin)
    if f_tseitin_processed.root == 'F':
        return UNSAT_MSG, None
    elif f_tseitin_processed.root == 'T':
        variables = f_prop.variables()
        if variables == set():
            return SAT_MSG, "Trivial"
        else:
            model = next(propositional_semantics.all_models(list(variables)))
            return SAT_MSG, str(model)

    # deduction steps
    return run_sat_cnf(str(f_tseitin_processed))  # @todo make sure returns only original vars settings


def run_sat_cnf(formula: str):
    """run sat solver on CNF formula without redundancies"""
    f_prop = propositional_Formula.parse(formula)
    to_solve = Sat_Solver(f_prop)

    msg, _ = to_solve.start_sat()
    if msg is not True:
        return msg

    to_decide = True
    decision_var = BUG_MSG

    while True:

        # decide
        if to_decide:
            decision_var, assignments = to_solve.decide()
            if decision_var == SAT_MSG:
                return SAT_MSG, assignments
        else:
            to_decide = True

        # propagate
        assert decision_var != BUG_MSG  # sanity check
        conflict_clause, backjump_level = to_solve.propagate(decision_var)

        # backtrack
        if conflict_clause is not True and conflict_clause != UNSAT_MSG:
            to_solve.backtrack(conflict_clause, backjump_level)
            to_decide = False
            decision_var = BACKTRACK_MSG

        if conflict_clause is UNSAT_MSG:
            return UNSAT_MSG


def run_smt_solver(formula: str):

    # get boolean abstraction
    f_pred = predicate_Formula.parse(formula)
    boolean_abstraction, z2f, f2z = f_pred.propositional_skeleton_mappings()


    # create dag


    to_solve_prop = Sat_Solver(boolean_abstraction)

    msg, _ = to_solve_prop.start_sat()
    if msg is not True:
        return msg

    # to_decide = True
    # decision_var = BUG_MSG
    #
    # while True:
    #
    #     # decide
    #     if to_decide:
    #         decision_var, assignments = to_solve.decide()
    #         if decision_var == SAT_MSG:
    #             return SAT_MSG, assignments
    #     else:
    #         to_decide = True
    #
    #     # propagate
    #     assert decision_var != BUG_MSG  # sanity check
    #     conflict_clause, backjump_level = to_solve.propagate(decision_var)
    #
    #     # backtrack
    #     if conflict_clause is not True and conflict_clause != UNSAT_MSG:
    #         to_solve.backtrack(conflict_clause, backjump_level)
    #         to_decide = False
    #         decision_var = BACKTRACK_MSG
    #
    #     if conflict_clause is UNSAT_MSG:
    #         return UNSAT_MSG

def run_lp_theory_solver():
    pass

if __name__ == "__main__":

    solver = input("Enter 1 for SAT, 2 for SMT, 3 for LP theory")
    f = input("Please enter formula")

    if solver == '1':
        result = run_sat_solver(f)
        print(result)
    elif solver == '2':
        pass
    elif solver == '3':
        pass
    else:
        print("nonexistent solver")