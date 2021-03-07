"""Tests all operator tasks."""

from propositions.syntax_test import *



def test_task1(debug=False):
    test_repr(debug)
    test_repr_all_operators(debug)
    test_variables(debug)
    test_variables_all_operators(debug)
    test_operators(debug)
    test_operators_all_operators(debug)
    test_parse_prefix(debug)
    test_parse_prefix_all_operators(debug)
    test_is_formula(debug)
    test_is_formula_all_operators(debug)
    test_parse(debug)
    test_parse_all_operators(debug)
         


def test_task3(debug=False):
    test_substitute_variables(debug)

def test_task4(debug=False):
    test_substitute_operators(debug)


test_task1(True)
test_task3(True)
test_task4(True)
