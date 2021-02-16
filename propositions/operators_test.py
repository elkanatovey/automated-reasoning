"""Tests for the propositions.operators module."""

from propositions.syntax import *
from propositions.semantics import *
from propositions.operators import *


many_fs = ['F', 'T', 'r', '~x', '(x+y)', '(x<->y)', '(x-&y)', '(x-|y)', '(x|y)',
           '(x->y)', '(x&y)', '(x&x)', '(p&q)', '(x|(y&z))', '~(~x|~(y|z))',
           '((p1|~p2)|~(p3|~~p4))', '((x+y)<->(~x+~y))',
           '((x-|~y)&(~F->(z<->T)))', '~~~~F']


nnf_fs = ['F', 'T', 'r', '~x', '(x&y)', '(x<->y)', '(x&y)','(x|y)', '(x|y)',
           '(x->y)', '(x&y)', '(x&x)', '(p&q)', '(x|(y&z))', '~(~x|~(y|z))','((p1|~p2)|~(p3|~~p4))',
            '((x&y)<->(~x&~y))', '((x|~y)&(~F->(z<->T)))', '~~~~F', '(~~x&~(x&y))', '((~p|~q)&x)']

# no literals case
tseitin_fs = ['(x&~x)', '~x', '(x&y)', '(x<->y)', '(x&y)','(x|y)', '(x|y)',
           '(x->y)', '(x&y)', '(x&x)', '(p&q)', '(x|(y&z))', '~(~x|~(y|z))','((p1|~p2)|~(p3|~~p4))',
            '((x&y)<->(~x&~y))', '((x|~y)&(~F->(z<->T)))', '~~~~F', '(~~x&~(x&y))', '((~p|~q)&x)']

tseitin_fs_short = ['(T->(x&~x))', '~~~~F', '(x|(y&z))', '~(~x|~(y|z))']

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


def test_preprocess_clauses(debug=False):
    if debug:
        print()
    for f in tseitin_fs:
        f = Formula.parse(f)
        ff = to_tseitin(f)
        fff = preprocess_clauses(ff)
        assert is_tautology(Formula('<->',ff , fff))
        if debug:
            print(f, "    ", ff ,"       ", fff)


def test_preprocess_clauses_short(debug=False):
    if debug:
        print()
    for f in tseitin_fs_short:
        f = Formula.parse(f)
        ff = to_tseitin(f)
        fff = preprocess_clauses(ff)
        assert is_tautology(Formula('<->',ff , fff))
        if debug:
            print(f, "    ", ff ,"       ", fff)

def test_to_tseitin_step2_short(debug=False):
    if debug:
        print()
    for f in tseitin_fs_short:
        f = Formula.parse(f)
        f_list = to_tseitin_step1(f)
        ff = to_tseitin_step2(f_list)
        assert is_satisfiable(f) == is_satisfiable(ff)
        if debug:
            print(f, "    ", "       ", ff)

def test_to_tseitin_short(debug=False):
    if debug:
        print()
    for f in tseitin_fs_short:
        f = Formula.parse(f)
        ff = to_tseitin(f)
        assert is_satisfiable(f) == is_satisfiable(ff)
        if debug:
            print(f, "    ", "       ", ff)


def test_to_tseitin_step2(debug = False):
    if debug:
        print()
    for f in tseitin_fs:
        f = Formula.parse(f)
        f_list = to_tseitin_step1(f)
        ff = to_tseitin_step2(f_list)
        assert is_satisfiable(f) == is_satisfiable(ff)
        if debug:
            print(f, "    ", "       ", ff)

def test_to_tseitin_step1(debug = False):
    """print middle step of tseitin construction"""
    if debug:
        print()
    for f in nnf_fs:
        f = Formula.parse(f)
        ff = to_tseitin_step1(f)
        if debug:
            print(f, "    ", ff)


def test_to_NNF_to_CNF(debug = False):
    if debug:
        print()
        print('Testing that  and is not child of or in converted formula')
    for f in nnf_fs:
        f = Formula.parse(f)
        ff = to_NNF(f)
        fff = NNF_to_CNF(ff)
        if debug:
            print(f, "    ", fff)
        assert fff.verify_and_not_child_of_or(fff.root)
        assert is_tautology(Formula('<->', ff, fff))

def test_to_NNF(debug = False):
    """check logical equality after to_NNF_push_negations,
    to_NNF_eliminate_IFF_and_IF """
    if debug:
        print()
    for f in nnf_fs:
        if debug:
            print('Testing conversion of', f,
                  "to an NNF formula")
        f = Formula.parse(f)
        ff = to_NNF(f)
        if debug:
            print(f , "        ", ff)
        assert is_tautology(Formula('<->', f, ff))


def test_to_NNF_eliminate_IFF_and_IF(debug = False):
    """check eliminations happened and logical equality"""
    if debug:
        print()
    for f in nnf_fs:
        if debug:
            print('Testing conversion of', f,
                  "to a formula without <-> and ->.")
        f = Formula.parse(f)
        ff = to_NNF_eliminate_IFF_and_IF(f)
        if debug:
            print(f, "        ", ff)
        assert ff.operators().issubset({'&', '~', '|', 'T', 'F'}), \
            str(ff) + ' contains wrong operators'
        assert is_tautology(Formula('<->', f, ff))


def test_to_NNF_push_negations(debug=False):
    """ check logical equality, and check negations pushed"""
    if debug:
        print()
    for f in nnf_fs:
        if debug:
            print('Testing conversion of', f,
                  "to a formula after De Morgan laws")
        f = Formula.parse(f)
        ff = to_NNF_push_negations(f)
        if debug:
            print(f, "        ", ff)
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
