from predicates.smt_solver import *
import matplotlib.pyplot as plt

dag_terms = ['plus(plus(x,plus(y,z)),w)']
dag_terms_large = ['a12', 'f(a,g(x))', 's(s(s(0)))', 'plus(x,s(_))',
              'plus(plus(x,plus(y,z)),w)']


smt_formulas = ['(f(x)=g(y)&g(y)=f(x))','plus(plus(x,plus(y,z)),w)=y', 'f(x)=g(y)']


def test_smt_solver(debug=False):
    import predicates.smt_solver
    import matplotlib.pyplot as plt
    import networkx as nx
    for f in smt_formulas:
        a = predicates.smt_solver.SmtSolver(f)
        nx.draw(a.dag, with_labels=True, cmap=plt.get_cmap('jet'))
        plt.show()


def test_draw_dag(debug=False):
    terms = []
    for s in dag_terms:
        if debug:
            print('Parsing', s, 'as a Term...')
        term = pred.Term.parse(s)
        terms.append(term)
        if debug:
            print('... and got', term)
        assert str(term) == s

    g, nodedict = build_dag(terms)
    a=g.nodes
    nx.draw(g, with_labels=True,cmap=plt.get_cmap('jet'))
    plt.show()

