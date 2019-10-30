# (c) This file is part of the course
# Mathematical Logic through Programming
# by Gonczarowski and Nisan.
# File name: code/prelim/prelim.py

"""Simple module for checking your Python and logic environment."""

from __future__ import annotations

from logic_utils import *

def half(x: int) -> int:
    """Halves the given even integer.

    Parameters:
        x: an even integer.

    Returns:
        A number `z` so that ``z+z=x``.
    """
    assert x%2 == 0
    # Task 0.1
    return x // 2
