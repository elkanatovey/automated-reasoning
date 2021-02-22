from solver import *

cnf_l0_true = ['((~x&z)&(~z|y))', '(~z&x)', '(~z&(x&(~x|y)))','(~z&(x&(~x|(y|z))))', '((x|z)&(~z&(x&(~x|(y|z)))))']
cnf_l0_false = ['(z&(~z&x))', '((~x&z)&(~z|x))']

cnf_l1_true = [  '((z1|z2)|z3)', '((x|y)&(y|z))', '(((x|y)&(y|z))&((z1|z2)|z3))' ]

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
        assert result == "UNSAT "
        if debug:
            print(f, "    ",result)

def test_generate_formula_true_l1(debug=True):
    if debug:
        print()
    for f in cnf_l1_true:
        result = run_sat_cnf(f)
        assert result[0] == "SAT "
        if debug:
            print(f, "    ",result)