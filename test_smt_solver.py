import solver

dag_terms = ['plus(plus(x,plus(y,z)),w)']
dag_terms_large = ['a12', 'f(a,g(x))', 's(s(s(0)))', 'plus(x,s(_))',
              'plus(plus(x,plus(y,z)),w)']
smt_formulas = ['(f(x)=g(y)&g(y)=f(x))','plus(plus(x,plus(y,z)),w)=y', 'f(x)=g(y)']

smt_formulas_false = ['(~f(x)=f(y)&(y=x|~x=x))']

smt_formulas_true = ['(~f(x)=f(y)&(y=x|y1=plus(plus(x,plus(y,z)),w)))','((((a=b&(~a=b|(~u=v|b=c)))&(u=v|(~v=w|f(u)=f(v))))&(~b=c|(~v=w|f(u)=f(a))))'
                                                                       '&(~f(u)=f(a)|~f(a)=f(c)))']

# 'a=b'
# '(~a=b|(~s=t|b=c))'
# '(s=t|(~t=r|f(s)=f(t)))'
# '(~b=c|(~t=r|f(s)=f(a)))'
# '(~f(s)=f(a)|~f(a)=f(c))'
#
# "s:u, t:v, r:w "
#
# 'a=b'
# '(~a=b|(~u=v|b=c))'
# '(u=v|(~v=w|f(u)=f(v)))'
# '(~b=c|(~v=w|f(u)=f(a)))'
# '(~f(u)=f(a)|~f(a)=f(c))'
#
# '((((a=b&(~a=b|(~u=v|b=c)))&(u=v|(~v=w|f(u)=f(v))))&(~b=c|(~v=w|f(u)=f(a))))&(~f(u)=f(a)|~f(a)=f(c)))'

def test_smt_solver(debug=False):
    for f in smt_formulas:
        a = solver.run_smt_solver(f)
        assert a[0] == solver.SAT_MSG

def test_smt_false(debug=False):
    for f in smt_formulas_false:
        a = solver.run_smt_solver(f)
        assert a[0] == solver.UNSAT_MSG

def test_smt_true(debug=False):
    for f in smt_formulas_true:
        a = solver.run_smt_solver(f)
        assert a[0] == solver.SAT_MSG