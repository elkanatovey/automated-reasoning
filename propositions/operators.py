"""Syntactic conversion of propositional formulae to use only specific sets of
operators."""

from propositions.syntax import *
from propositions.semantics import *
from logic_utils import fresh_variable_name_generator

def to_not_and_or(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'~'``, ``'&'``, and ``'|'``.

    Parameters:
        formula: formula to convert.

    Return:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'~'``, ``'&'``, and
        ``'|'``.
    """
    # Task 3.5
    return formula.substitute_operators(
        {'+': Formula.parse_prefix('((p&~q)|(~p&q))')[0],
         '->': Formula.parse_prefix('~(p&~q)')[0],
         '<->': Formula.parse_prefix('((p&q)|(~p&~q))')[0],
         '-&': Formula.parse_prefix('~(p&q)')[0],
         '-|': Formula.parse_prefix('~(p|q)')[0],
         'T': Formula.parse_prefix('(p|~p)')[0],
         'F': Formula.parse_prefix('(p&~p)')[0]})

def to_not_and(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'~'`` and ``'&'``.

    Parameters:
        formula: formula to convert.

    Return:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'~'`` and ``'&'``.
    """
    # Task 3.6a
    f = to_not_and_or(formula)
    return f.substitute_operators({'|': Formula.parse_prefix('~(~p&~q)')[0]})


def to_nand(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'-&'``.

    Parameters:
        formula: formula to convert.

    Return:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'-&'``.
    """
    # Task 3.6b
    f = to_not_and_or(formula) # faster than to_not_and
    return f.substitute_operators({'~': Formula.parse_prefix('(p-&p)')[0],
                                   '&': Formula
                                  .parse_prefix('((p-&q)-&(p-&q))')[0],
                                   # speeds up runtime
                                   '|': Formula.
                                  parse_prefix('((p-&p)-&(q-&q))')[0]})


def to_implies_not(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'->'`` and ``'~'``.

    Parameters:
        formula: formula to convert.

    Return:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'->'`` and ``'~'``.
    """
    # Task 3.6c
    f = to_nand(formula)
    return f.substitute_operators({'-&': Formula.parse_prefix('(p->~q)')[0]})


def to_implies_false(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'->'`` and ``'F'``.

    Parameters:
        formula: formula to convert.

    Return:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'->'`` and ``'F'``.
    """
    # Task 3.6d
    f = to_implies_not(formula)
    return f.substitute_operators({'~': Formula.parse_prefix('(p->F)')[0]})


def to_tseitin_step1(formula: Formula) -> list:
    """ return a list of all subformulas reformulated as iff tseitin reps
    """
    representatives = []

    # base case
    if is_variable(formula.root) or is_constant(formula.root):
        return representatives

    current_z = next(fresh_variable_name_generator)
    if is_unary(formula.root):
        child_tseitin = to_tseitin_step1(formula.first)

        if len(child_tseitin) is 0:
            new_representative = Formula('<->', Formula(current_z), formula)  #z<->~q
            representatives.append(new_representative)
            return representatives

        new_representative = Formula('<->', Formula(current_z), Formula('~', child_tseitin[0].first))
        representatives.append(new_representative)
        representatives.extend(child_tseitin)
        return representatives

    if is_binary(formula.root):
        l_child_tseitin = to_tseitin_step1(formula.first)
        r_child_tseitin = to_tseitin_step1(formula.second)

        if len(l_child_tseitin) is 0:
            l_rep = formula.first
        else:
            l_rep = l_child_tseitin[0].first

        if len(l_child_tseitin) is 0:
            r_rep = formula.second
        else:
            r_rep = r_child_tseitin[0].first

        repped_formula = Formula(formula.root, l_rep, r_rep)
        new_representative = Formula('<->', Formula(current_z), repped_formula)
        representatives.append(new_representative)

        representatives.extend(l_child_tseitin)
        representatives.extend(r_child_tseitin)
        return representatives


# def to_tseitin_step2(formula: Formula) -> Formula:
#     """return full tseitin formula before cnf"""
#     formula_list = to_tseitin_step1(formula)
#
#     for i in range(len(formula_list), 0):
#         current_f = Formula('&',)
