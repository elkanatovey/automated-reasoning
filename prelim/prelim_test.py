# (c) This file is part of the course
# Mathematical Logic through Programming
# by Gonczarowski and Nisan.
# File name: code/prelim/prelim_test.py

"""Tests for the prelim.prelim module."""

from prelim.prelim import half

def test_half(debug=False):
    if debug:
        print("Testing half of 42")
    result = half(42)
    assert type(result) is int
    assert result + result == 42

    if debug:
        print("Testing half of 8")
    result = half(8)
    assert type(result) is int
    assert result + result == 8

def test_all(debug=False):
    test_half(debug)
