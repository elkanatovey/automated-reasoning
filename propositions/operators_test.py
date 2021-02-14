"""Tests for the propositions.operators module."""

from propositions.syntax import *
from propositions.semantics import *
from propositions.operators import *


many_fs = ['F', 'T', 'r', '~x', '(x+y)', '(x<->y)', '(x-&y)', '(x-|y)', '(x|y)',
           '(x->y)', '(x&y)', '(x&x)', '(p&q)', '(x|(y&z))', '~(~x|~(y|z))',
           '((p1|~p2)|~(p3|~~p4))', '((x+y)<->(~x+~y))',
           '((x-|~y)&(~F->(z<->T)))', '~~~~F']


nnf_fs = ['F', 'T', 'r', '~x', '(x&y)', '(x<->y)', '(x&y)', '(x|y)', '(x|y)',
           '(x->y)', '(x&y)', '(x&x)', '(p&q)', '(x|(y&z))', '~(~x|~(y|z))','((p1|~p2)|~(p3|~~p4))',
            '((x&y)<->(~x&~y))', '((x|~y)&(~F->(z<->T)))', '~~~~F', '(~~x&~(x&y))']


def test_operators_defined(debug=False):
    if debug:
        print('Verifying that all operators are recognized.')
    for s in {'&', '|',  '->', '+', '<->', '-&', '-|'}:
        assert is_binary(s)
    
def test_to_not_and_or(debug=False):
    if debug:
        print()
    for f in many_fs:
        if debug:
            print('Testing conversion of', f,
                  "to a formula using only '&', '|' and '~'.")
        f = Formula.parse(f)
        ff = to_not_and_or(f)
        assert ff.operators().issubset({'&', '~','|'}), \
               str(ff) + ' contains wrong operators'
        assert is_tautology(Formula('<->', f, ff))

def test_to_not_and(debug=False):
    if debug:
        print()
    for f in many_fs:
        if debug:
            print('Testing conversion of', f,
                  "to a formula using only '&' and '~'.")
        f = Formula.parse(f)
        ff = to_not_and(f)
        assert ff.operators().issubset({'&', '~'}), \
               str(ff) + ' contains wrong operators'
        assert is_tautology(Formula('<->', f, ff))
    
def test_to_nand(debug=False):
    if debug:
        print()
    for f in many_fs:
        if debug:
            print('Testing conversion of', f, "to a formula using only '-&'.")
        f = Formula.parse(f)
        ff = to_nand(f)
        assert ff.operators().issubset({'-&'}), \
               str(ff) + ' contains wrong operators'
        assert is_tautology(Formula('<->', f, ff))

def test_to_implies_not(debug=False):
    if debug:
        print()
    for f in many_fs:
        if debug:
            print('Testing conversion of', f,
                  "to a formula using only '->' and '~'.")
        f = Formula.parse(f)
        ff = to_implies_not(f)
        assert ff.operators().issubset({'->', '~'}), \
               str(ff) + ' contains wrong operators'
        assert is_tautology(Formula('<->', f, ff))

def test_to_implies_false(debug=False):
    if debug:
        print()
    for f in many_fs:
        if debug:
            print('Testing conversion of', f,
                  "to a formula using only '->' and 'F'.")
        f = Formula.parse(f)
        ff = to_implies_false(f)
        assert ff.operators().issubset({'->', 'F'}), \
               str(ff) + ' contains wrong operators'
        assert is_tautology(Formula('<->', f, ff))

def test_to_tseitin_step1():
    for f in many_fs:
        f = Formula.parse(f)
        # ff = to_tseitin_step1(f)
        ff= to_NNF_eliminate_IFF_and_IF(f)
        print(f, "    ", ff)

def test_to_NNF(debug = False):
    if debug:
        print()
    for f in nnf_fs:
        if debug:
            print('Testing conversion of', f,
                  "to an NNF formula")
        f = Formula.parse(f)
        ff = to_NNF(f)
        print(f , "        ", ff)
        assert is_tautology(Formula('<->', f, ff))

def test_to_NNF_eliminate_IFF_and_IF(debug = False):
    if debug:
        print()
    for f in nnf_fs:
        if debug:
            print('Testing conversion of', f,
                  "to a formula without <-> and ->.")
        f = Formula.parse(f)
        ff = (f)
        assert ff.operators().issubset({'&', '~', '|', 'T', 'F'}), \
            str(ff) + ' contains wrong operators'
        assert is_tautology(Formula('<->', f, ff))


def test_to_NNF_push_negations(debug=False):
    if debug:
        print()
    for f in nnf_fs:
        if debug:
            print('Testing conversion of', f,
                  "to a formula after De Morgan laws")
        f = Formula.parse(f)
        ff = to_NNF_push_negations(f)
        assert ff.negation_childrens() == set()
        assert is_tautology(Formula('<->', f, ff))

def test_ex3(debug=False):
    assert is_binary('+'), 'Change is_binary() before testing Chapter 3 tasks.'
    test_operators_defined(debug)
    test_to_not_and_or(debug)
    test_to_not_and(debug)
    test_to_nand(debug)
    test_to_implies_not(debug)
    test_to_implies_false(debug)

def test_all(debug=False):
    test_ex3(debug)
