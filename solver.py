from propositions.syntax import Formula as propositional_Formula
import propositions.operators as propositional_operators
import propositions.semantics as propositional_semantics
from propositions.sat_solver import Sat_Solver
SAT_MSG = "SAT "
UNSAT_MSG = "UNSAT "
def run_sat_solver(formula: str):
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
    return run_sat_cnf(str(f_tseitin_processed))


def run_sat_cnf(formula: str):
    f_prop = propositional_Formula.parse(formula)
    to_solve = Sat_Solver(f_prop)

    msg = to_solve.start_sat()
    if msg is not None:
        return msg

    while True:
        decision_var = to_solve.decide()
        conflict, msg = to_solve.propagate(decision_var)
        #
        # conflict, msg = to_solve.propagate_s2()




def run_smt_solver():
    pass

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