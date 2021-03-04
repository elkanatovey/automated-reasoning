from predicates.smt_solver import *
import matplotlib.pyplot as plt

dag_terms = ['plus(plus(x,plus(y,z)),w)']
dag_terms_large = ['a12', 'f(a,g(x))', 's(s(s(0)))', 'plus(x,s(_))',
              'plus(plus(x,plus(y,z)),w)']

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

