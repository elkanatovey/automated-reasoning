# (c) This file is part of the course
# Mathematical Logic through Programming
# by Gonczarowski and Nisan.
# File name: test_ex10.py

"""Tests all Chapter 10 tasks."""

from predicates.prover_test import *
from predicates.some_proofs_test import *

def test_skeleton(debug=False):
    test_prover_basic(debug)

def test_task1(debug=False):
    test_add_universal_instantiation(debug)

def test_task2(debug=False):
    test_add_tautological_implication(debug)

def test_task3(debug=False):
    test_add_existential_derivation(debug)

def test_task4(debug=False):
    test_lovers_proof(debug)

def test_task5(debug=False):
    test_homework_proof(debug)

def test_task6(debug=False):
    test_add_flipped_equality(debug)

def test_task7(debug=False):
    test_add_free_instantiation(debug)

def test_task8(debug=False):
    test_add_substituted_equality(debug)

def test_task9(debug=False):
    test_add_chained_equality(debug)

def test_task10(debug=False):
    test_unique_zero_proof(debug)

def test_task11(debug=False):
    test_multiply_zero_proof(debug)

def test_task12(debug=False):
    test_peano_zero_proof(debug)

def test_task13(debug=False):
    test_russell_paradox_proof(debug)

# test_skeleton(True)
# test_task1(True)
# test_task2(True)
# test_task3(True)
# test_task4(True)
# test_task5(True)
# test_task6(True)
# test_task7(True)
# test_task8(True)
# test_task9(True)
test_task10(True)
# test_task11(True)
# test_task12(True)
# test_task13(True)
