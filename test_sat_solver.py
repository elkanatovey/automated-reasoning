"""Tests all sat solver related tasks."""

from propositions.test_sat_algorithm import *
from propositions.tseitin_test import test_preprocess_clauses_short, test_to_tseitin_step2_short, test_to_tseitin_short, \
    test_to_tseitin_step1, test_to_NNF_to_CNF, test_to_NNF, test_to_NNF_eliminate_IFF_and_IF, test_to_NNF_push_negations


def test_preprocess(debug=False):
    test_to_NNF_push_negations(debug)
    test_to_NNF_eliminate_IFF_and_IF(debug)
    test_to_NNF(debug)
    test_to_NNF_to_CNF(debug)
    test_to_tseitin_step1(debug)
    test_to_tseitin_step2_short(debug)
    test_to_tseitin_short(debug)
    test_preprocess_clauses_short(debug)


def test_deduction(debug=False):
    test_generate_formula_true(debug)
    test_generate_formula_false(debug)


test_preprocess(True)
test_deduction(True)

