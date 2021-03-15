import numpy as np
from linear_programing.simplex_solver import *
from predicates.syntax import *


TQ_formulas = ['G(plus(plus(x,plus(y,~5)),w),y)','(f(x)=g(y)&g(y)=f(x))', 'f(x)=g(y)']



for f in TQ_formulas:
    formula = Formula.parse(f)
    assert formula is not None



# def test_simplex_solver(debug=False):
#     for f in TQ_formulas:
#         formula = Formula.parse(f)
#         assert formula is not None
#
#     print(6)
#
#
#
#
# def test_simplex_solver(debug=False):
#     # better to hold vars as integers (in Bland's rule we need to choose smallest)
#
#
#
#     X_B = np.array([4, 5, 6])
#     X_N = np.array([1, 2, 3])
#
#     B = np.array([[1, 0, 0], [0, 1, 0], [0, 0, 1]])
#     An = np.array([[1, 1, 2], [2, 0, 3], [2, 1, 3]])
#
#     C_B = np.array([0, 0, 0])
#     C_N = np.array([3, 2, 4])
#     Xb_star = np.array([4, 5, 7])
#
#     # X_B = np.array([5, 6, 7])
#     # X_N = np.array([1, 2, 3, 4])
#     #
#     # B = np.array([[1, 0, 0], [0, 1, 0], [0, 0, 1]])
#     # An = np.array([[3, 2, 1, 2], [1, 1, 1, 1], [4, 3, 3, 4]])
#     #
#     # C_B = np.array([0, 0, 0])
#     # C_N = np.array([19, 13, 12, 17])
#     # Xb_star = np.array([225, 117, 420])
#
#
#     s = LP_Solver()
#     s.revised_simplex()
#
#
