# propositional imports
import propositions.tseitin
from propositions.syntax import Formula as propositional_Formula
import propositions.semantics as propositional_semantics

# predicate imports
import predicates.smt_solver

# msgs
from propositions.sat_solver import Sat_Solver
from propositions.sat_solver import UNSAT_MSG
from propositions.sat_solver import SAT_MSG
from propositions.sat_solver import BACKTRACK_MSG

BUG_MSG = "This shouldn't be here"

from solver_helper import *

def run_sat_solver(formula: str):
    """preprocess non cnf formula with redundancies and then hand off to sat solver"""
    f_prop = propositional_Formula.parse(formula)

    # tseitin and preprocessing
    f_tseitin = propositions.tseitin.to_tseitin(f_prop)
    f_tseitin_processed = propositions.tseitin.preprocess_clauses(f_tseitin)
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
    msg, settings = run_sat_cnf(str(f_tseitin_processed))
    if msg == SAT_MSG:
        original_variables = f_prop.variables()
        original_settings = {key: settings[key] for key in original_variables}
        return msg, original_settings
    else:
        return msg, settings


def run_sat_cnf(formula: str):
    """run sat solver on CNF formula without redundancies"""
    f_prop = propositional_Formula.parse(formula)
    to_solve = Sat_Solver(f_prop)

    msg, _ = to_solve.start_sat()
    if msg is not True:
        return msg, None

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
            return UNSAT_MSG, None


def run_smt_solver(formula: str):
    """run smt solver along with sat solver"""
    smt_solver = predicates.smt_solver.SmtSolver(formula)
    # get boolean abstraction
    prop_f = smt_solver.propositional_skeleton

    sat_solver = Sat_Solver(prop_f)

    msg, _ = sat_solver.start_sat()
    # UNSAT at level 0 by SAT solver
    if msg is not True:
        return msg, None

    sat_smt_level_mappings = {0: 0}  # {SAT_level: SMT_level}
    dpoints_settings = []  # list of tuples (dvar, setting)
    while True:
        sat_assignments_dict = sat_solver.assignment_dict
        # print(sat_assignments_dict)
        msg, assignments = smt_solver.t_propagate(sat_assignments_dict)

        # sat/unsat
        if (msg == SAT_MSG and assignments is True) or (msg == UNSAT_MSG and assignments is False):
            return msg, assignments

        # t-conflict
        elif msg == UNSAT_MSG and assignments is True:
            smt_backjump(sat_solver, dpoints_settings, smt_solver, sat_smt_level_mappings)

            # smt updates sat here
        elif msg == SAT_MSG and bool(assignments) is True:
            for fake_decision in assignments.keys():
                to_do = smt_update_sat(sat_solver, fake_decision, assignments,
                                       smt_solver, sat_smt_level_mappings, dpoints_settings)
                if to_do is True:
                    continue
                elif to_do is False:
                    break
                elif to_do is (UNSAT_MSG, None):
                    return UNSAT_MSG, None

        # decide case
        elif msg == SAT_MSG and bool(assignments) is False:
            if smt_run_decide(sat_solver, dpoints_settings, smt_solver, sat_smt_level_mappings) is (UNSAT_MSG, None):
                return UNSAT_MSG, None


def run_lp_theory_solver():
    pass


if __name__ == "__main__":

    solver = input("Enter 1 for SAT, 2 for SMT, 3 for LP theory")
    f = input("Please enter formula")

    if solver == '1':
        cnf = input("Enter 1 for CNF, 2 for nonCNF")
        if cnf == '1':
            result = run_sat_cnf(f)
            print(result)
        elif solver == '2':
            result = run_sat_solver(f)
            print(result)
        else:
            print("nonexistent solver")
    elif solver == '2':
        result = run_smt_solver(f)
        print(result)
    elif solver == '3':
        pass
    else:
        print("nonexistent solver")
