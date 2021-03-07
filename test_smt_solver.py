import solver

dag_terms = ['plus(plus(x,plus(y,z)),w)']
dag_terms_large = ['a12', 'f(a,g(x))', 's(s(s(0)))', 'plus(x,s(_))',
              'plus(plus(x,plus(y,z)),w)']
smt_formulas = ['(f(x)=g(y)&g(y)=f(x))','plus(plus(x,plus(y,z)),w)=y', 'f(x)=g(y)']

smt_formulas_complicated = ['(~f(x)=f(y)&(y=x|y1=plus(plus(x,plus(y,z)),w)))']

def test_smt_solver(debug=False):
    for f in smt_formulas:
        a = solver.run_smt_solver(f)
        assert a[0] == solver.SAT_MSG

def test_smt_complicated(debug=False):
    for f in smt_formulas_complicated:
        a = solver.run_smt_solver(f)
        assert a[0] == solver.UNSAT_MSG