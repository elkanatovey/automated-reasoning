from propositions.syntax import Formula as propositional_Formula
import propositions.operators as propositional_operators

def run_sat_solver(formula: str):
    f_prop = propositional_Formula.parse(formula)

    #tseitin and preprocessing
    f_prop = propositional_operators.to_tseitin(f_prop)
    f_prop = propositional_operators.preprocess_clauses(f_prop)

    # deduction steps



def run_smt_solver():
    pass

def run_lp_theory_solver():
    pass

if __name__ == "__main__":

    solver = input("Enter 1 for SAT, 2 for SMT, 3 for LP theory")
    f = input("Please enter formula")

    if solver == 1:
        result = run_sat_solver(f)
    elif solver == 2:
        pass
    elif solver == 3:
        pass
    else:
        print("nonexistent solver")