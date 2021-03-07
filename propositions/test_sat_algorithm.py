from solver import *
from propositions.tseitin import *

cnf_l0_true = ['((~x&z)&(~z|y))', '(~z&x)', '(~z&(x&(~x|y)))','(~z&(x&(~x|(y|z))))', '((x|z)&(~z&(x&(~x|(y|z)))))']
cnf_l0_false = ['(z&(~z&x))', '((~x&z)&(~z|x))']

cnf_l1_true = ['((((~y|~z)&((x|y)&(y|z)))&(~x|~y))&(~z1|~x))', '((z1|z2)|z3)', '((x|y)&(y|z))', '(((x|y)&(y|z))&((z1|z2)|z3))']
cnf_l1_false = ['(((((((x5|~x1)|x3)&(~x5|~x1))&(~x3|~x4))&(x1|x4))&(x1|~x4))&(~x1|x5))']

tseitin_fs_short = ['(x|(y&z))', '~(~x|~(y|z))']


def test_preprocess_clauses_short(debug=False):
    if debug:
        print()
    for f in tseitin_fs_short:
        f = Formula.parse(f)
        ff = to_tseitin(f)
        fff = preprocess_clauses(ff)
        fff = str(fff)
        result = run_sat_cnf(fff)
        assert result[0] == "SAT "
        if debug:
            print(f, "    ", result)

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

def test_generate_formula_true_l1(debug=False):
    if debug:
        print()
    for f in cnf_l1_true:
        result = run_sat_cnf(f)
        assert result[0] == "SAT "
        if debug:
            print(f, "    ",result)

def test_generate_formula_false_l1(debug=False):
    if debug:
        print()
    for f in cnf_l1_false:
        result = run_sat_cnf(f)
        assert result[0] == "UNSAT "
        if debug:
            print(f, "    ",result)