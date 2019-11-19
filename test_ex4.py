# (c) This file is part of the course
# Mathematical Logic through Programming
# by Gonczarowski and Nisan.
# File name: test_ex4.py

"""Tests all Chapter 4 tasks."""

from propositions.proofs_test import *
from propositions.semantics_test import *
from propositions.some_proofs_test import *

def test_task1(debug=False):
    test_variables(debug)

def test_task2(debug=False):
    test_evaluate_inference(debug)

def test_task3(debug=False):
    test_is_sound_inference(debug)

def test_task4(debug=False):
    test_specialize(debug)

def test_task5(debug=False):
    test_merge_specialization_maps(debug)
    test_formula_specialization_map(debug)
    test_specialization_map(debug)
    test_is_specialization_of(debug)

def test_task6(debug=False):
    test_rule_for_line(debug)
    test_is_line_valid(debug)
    test_is_valid(debug)
    
def test_task7(debug=False):
    test_prove_and_commutativity(debug)

def test_task8(debug=False):
    test_prove_I0(debug)

test_task1(True)
test_task2(True)
test_task3(True)
test_task4(True)
test_task5(True)
test_task6(True)
test_task7(True)
test_task8(True)
