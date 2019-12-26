# (c) This file is part of the course
# Mathematical Logic through Programming
# by Gonczarowski and Nisan.
# File name: test_ex9.py

"""Tests all Chapter 9 tasks."""

from predicates.syntax_test import *
from predicates.proofs_test import *

def test_task1(debug=False):
    test_term_substitute(debug)

def test_task2(debug=False):
    test_formula_substitute(debug)

def test_task3(debug=False):
    test_instantiate_helper(debug)

def test_task4(debug=False):
    test_instantiate(debug)

def test_task5(debug=False):
    test_assumption_line_is_valid(debug)

def test_task6(debug=False):
    test_mp_line_is_valid(debug)

def test_task7(debug=False):
    test_ug_line_is_valid(debug)

def test_task8(debug=False):
    test_propositional_skeleton(debug)

def test_task9(debug=False):
    test_tautology_line_is_valid(debug)

def test_combined(debug=False):
    test_is_valid(debug)

def test_task10(debug=False):
    test_from_propositional_skeleton(debug)

def test_task11(debug=False):
    test_axiom_specialization_map_to_schema_instantiation_map(debug)
    test_prove_from_skeleton_proof(debug)

def test_task12(debug=False):
    test_prove_tautology(debug)

test_task1(True)
test_task2(True)
test_task3(True)
test_task4(True)
# test_task5(True)
# test_task6(True)
# test_task7(True)
# test_task8(True)
# test_task9(True)
# test_combined(True)
# test_task10(True)
# test_task11(True)
# test_task12(True)
