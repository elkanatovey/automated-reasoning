from solver import *

cnf_l0_true = ['(~z&x)', '(~z&(x&(~x|y)))','(~z&(x&(~x|(y|z))))', '((x|z)&(~z&(x&(~x|(y|z)))))']
cnf_l0_false = ['(z&(~z&x))']

def test_generate_formula_true(debug=False):
    if debug:
        print()
    for f in cnf_l0_true:
        result = run_sat_cnf(f)
        assert result[0] == "SAT "
        if debug:
            print(f, "    ",result)

def test_generate_formula_false(debug=False):
    if debug:
        print()
    for f in cnf_l0_false:
        result = run_sat_cnf(f)
        assert result[0] == "UNSAT "
        if debug:
            print(f, "    ",result)