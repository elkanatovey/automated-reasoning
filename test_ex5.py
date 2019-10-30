# (c) This file is part of the course
# Mathematical Logic through Programming
# by Gonczarowski and Nisan.
# File name: test_ex5.py

"""Tests all Chapter 5 tasks."""

from propositions.proofs_test import *
from propositions.deduction_test import *
from propositions.some_proofs_test import *

def pretest_validity(debug=False):
    test_is_valid(debug)

def test_task1(debug=False):
    test_prove_specialization(debug)

def test_task2(debug=False):
    test_inline_proof_once(debug)
    test_inline_proof(debug)

def test_task3(debug=False):
    test_prove_corollary(debug)
    test_combine_proofs(debug)

def test_task4(debug=False):
    test_remove_assumption(debug)

def test_task5(debug=False):
    test_prove_hypothetical_syllogism(debug)

def test_task6(debug=False):
    test_proof_from_inconsistency(debug)

def test_task7(debug=False):
    test_prove_by_contradiction(debug)

pretest_validity(False)
test_task1(True)
test_task2(True)
test_task3(True)
test_task4(True)
test_task5(True)
test_task6(True)
test_task7(True)
