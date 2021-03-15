from propositions.tseitin import to_NNF, to_NNF_eliminate_IFF_and_IF, to_NNF_push_negations, preprocess_clauses, \
    NNF_to_CNF, to_tseitin_step1, to_tseitin_step2, to_tseitin, NNF_to_DNF
from propositions.semantics import is_tautology, is_satisfiable
from propositions.syntax import Formula
from linear_programing.simplex_parser import *

nnf_fs = ['F', 'T', 'r', '~x', '(x&y)', '(x<->y)', '(x&y)', '(x|y)', '(x|y)',
           '(x->y)', '(x&y)', '(x&x)', '(p&q)', '(x|(y&z))', '~(~x|~(y|z))','((p1|~p2)|~(p3|~~p4))',
            '((x&y)<->(~x&~y))', '((x|~y)&(~F->(z<->T)))', '~~~~F', '(~~x&~(x&y))', '((~p|~q)&x)']

dnf_fs = ['F', 'T', 'r', '~x', '(x&y)', '(x<->y)', '(x&y)', '(x|y)', '(x|y)',
           '(x->y)', '(x&y)', '(x&x)', '(p&q)', '(x|(y&z))', '(x|(y|z))','((p1|(((p2&p5)&(p3|p4))|p6))|(p3|p4))',
            '((x&y)<->(x&y))', '((x|y)&(F->(z<->T)))', '~~~~F', '(x&(x&y))', '((p|q)&x)']

tseitin_fs = ['(x&~x)', '~x', '(x&y)', '(x<->y)', '(x&y)','(x|y)', '(x|y)',
           '(x->y)', '(x&y)', '(x&x)', '(p&q)', '(x|(y&z))', '~(~x|~(y|z))','((p1|~p2)|~(p3|~~p4))',
            '((x&y)<->(~x&~y))', '((x|~y)&(~F->(z<->T)))', '~~~~F', '(~~x&~(x&y))', '((~p|~q)&x)']
tseitin_fs_short = ['(T->(x&~x))', '~~~~F', '(x|(y&z))', '~(~x|~(y|z))']


def test_generate_formula(debug=False):
    if debug:
        print()
    for f in tseitin_fs_short:
        f = Formula.parse(f)
        ff = to_tseitin(f)
        fff = preprocess_clauses(ff)
        ffff = fff.get_clauses()
        fffff = Formula.generate_formula(ffff)
        assert is_tautology(Formula('<->', fff, fffff))
        if debug:
            print(ffff, "    ", ffff, "       ", fffff)


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

def test_to_NNF_to_DNF(debug = True):
    if debug:
        print()
        print('Testing that  or is not child of and in converted formula')
    for f in dnf_fs:
        f = Formula.parse(f)
        ff = to_NNF(f)
        fff = NNF_to_DNF(ff)
        if debug:
            print(f, "    ", fff)
        assert fff.verify_or_not_child_of_and(fff.root)
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


def test_to_NNF_eliminate_IFF_and_IF(debug=False):
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