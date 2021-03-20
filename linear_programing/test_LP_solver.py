from predicates.syntax import *
from linear_programing.simplex_solver import *

#     2x + z >= 1                                        -                    SAT
f0 =  'GS(plus(mult(2,x),z),1)'
#     (2x + z >= 1) & (x = 1)                            -                    SAT
f1 =  '(GS(plus(mult(2,x),z),1)&GS(z,1))'
#     (2x + z >= 1) & (z < 1) & (x < 2)                  -                    UNSAT
f2 =  '((GS(plus(mult(2,x),z),1)&~GS(z,1))&~GS(x,2))'
#     (x + z <= 5) & (-x - z <= -5)        -                                  SAT
f3 = '((~GS(plus(x,z),5)|S(plus(x,z),5))&(~GS(minus(minus(0,x),z),minus(0,5))|S(minus(minus(0,x),z),minus(0,5))))'
#     (x + z <= 5) & (-x - z <= -6)        -                                  UNSAT
f4 = '((~GS(plus(x,z),5)|S(plus(x,z),5))&(~GS(minus(minus(0,x),z),minus(0,6))|S(minus(minus(0,x),z),minus(0,6))))'
#     (x + z <= 5) & (-x - z <= -5) & (x + z != 5)                            UNSAT
f5 = '(((~GS(plus(x,z),5)|S(plus(x,z),5))&(~GS(minus(minus(0,x),z),minus(0,5))|S(minus(minus(0,x),z),minus(0,5))))&~S(plus(x,z),5))'



SMT_formulas = [f0, f1, f2, f3, f4, f5]
for f in SMT_formulas:
    # formula = Formula.parse(f)
    solver = run_simplex(f)
    # solver = LP_Solver([{'x': 1, 'y': 1}, {'x': -1, 'y': -1}, {'x': 2, 'y': 1, 'z': 1}], [5, 5, -10], False)
    # solver = LP_Solver([{'x':1, 'y':0,'z':1},{'x':1, 'y':1,'z':0},{'x':2, 'y':1, 'z':1}],[5,5,-10], False)
    # solver.get_all_const()