"""Tests all syntax tasks."""

from propositions.syntax_test import *

def test_task1(debug=False):
    test_repr(debug)

def test_task2(debug=False):
    test_variables(debug)

def test_task3(debug=False):
    test_operators(debug)

def test_task4(debug=False):
    test_parse_prefix(debug)

def test_task5(debug=False):
    test_is_formula(debug)

def test_task6(debug=False):
    test_parse(debug)

test_task1(True)
test_task2(True)
test_task3(True)
test_task4(True)
test_task5(True)
test_task6(True)