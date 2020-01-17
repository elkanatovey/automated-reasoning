# (c) This file is part of the course
# Mathematical Logic through Programming
# by Gonczarowski and Nisan.
# File name: predicates/prenex.py

"""Conversion of predicate-logic formulas into prenex normal form."""

from typing import Tuple

from logic_utils import fresh_variable_name_generator

from predicates.syntax import *
from predicates.proofs import *
from predicates.prover import *

#: Additional axioms of quantification for first-order predicate logic.
ADDITIONAL_QUANTIFICATION_AXIOMS = (
    Schema(Formula.parse('((~Ax[R(x)]->Ex[~R(x)])&(Ex[~R(x)]->~Ax[R(x)]))'),
           {'x', 'R'}),
    Schema(Formula.parse('((~Ex[R(x)]->Ax[~R(x)])&(Ax[~R(x)]->~Ex[R(x)]))'),
           {'x', 'R'}),
    Schema(Formula.parse('(((Ax[R(x)]&Q())->Ax[(R(x)&Q())])&'
                         '(Ax[(R(x)&Q())]->(Ax[R(x)]&Q())))'), {'x', 'R', 'Q'}),
    Schema(Formula.parse('(((Ex[R(x)]&Q())->Ex[(R(x)&Q())])&'
                         '(Ex[(R(x)&Q())]->(Ex[R(x)]&Q())))'), {'x', 'R', 'Q'}),
    Schema(Formula.parse('(((Q()&Ax[R(x)])->Ax[(Q()&R(x))])&'
                         '(Ax[(Q()&R(x))]->(Q()&Ax[R(x)])))'), {'x', 'R', 'Q'}),
    Schema(Formula.parse('(((Q()&Ex[R(x)])->Ex[(Q()&R(x))])&'
                         '(Ex[(Q()&R(x))]->(Q()&Ex[R(x)])))'), {'x', 'R', 'Q'}),
    Schema(Formula.parse('(((Ax[R(x)]|Q())->Ax[(R(x)|Q())])&'
                         '(Ax[(R(x)|Q())]->(Ax[R(x)]|Q())))'), {'x', 'R', 'Q'}),
    Schema(Formula.parse('(((Ex[R(x)]|Q())->Ex[(R(x)|Q())])&'
                         '(Ex[(R(x)|Q())]->(Ex[R(x)]|Q())))'), {'x', 'R', 'Q'}),
    Schema(Formula.parse('(((Q()|Ax[R(x)])->Ax[(Q()|R(x))])&'
                         '(Ax[(Q()|R(x))]->(Q()|Ax[R(x)])))'), {'x', 'R', 'Q'}),
    Schema(Formula.parse('(((Q()|Ex[R(x)])->Ex[(Q()|R(x))])&'
                         '(Ex[(Q()|R(x))]->(Q()|Ex[R(x)])))'), {'x', 'R', 'Q'}),
    Schema(Formula.parse('(((Ax[R(x)]->Q())->Ex[(R(x)->Q())])&'
                         '(Ex[(R(x)->Q())]->(Ax[R(x)]->Q())))'), {'x', 'R', 'Q'}),
    Schema(Formula.parse('(((Ex[R(x)]->Q())->Ax[(R(x)->Q())])&'
                         '(Ax[(R(x)->Q())]->(Ex[R(x)]->Q())))'), {'x', 'R', 'Q'}),
    Schema(Formula.parse('(((Q()->Ax[R(x)])->Ax[(Q()->R(x))])&'
                         '(Ax[(Q()->R(x))]->(Q()->Ax[R(x)])))'), {'x', 'R', 'Q'}),
    Schema(Formula.parse('(((Q()->Ex[R(x)])->Ex[(Q()->R(x))])&'
                         '(Ex[(Q()->R(x))]->(Q()->Ex[R(x)])))'), {'x', 'R', 'Q'}),
    Schema(Formula.parse('(((R(x)->Q(x))&(Q(x)->R(x)))->'
                         '((Ax[R(x)]->Ay[Q(y)])&(Ay[Q(y)]->Ax[R(x)])))'),
           {'x', 'y', 'R', 'Q'}),
    Schema(Formula.parse('(((R(x)->Q(x))&(Q(x)->R(x)))->'
                         '((Ex[R(x)]->Ey[Q(y)])&(Ey[Q(y)]->Ex[R(x)])))'),
           {'x', 'y', 'R', 'Q'}))


def is_quantifier_free(formula: Formula) -> bool:
    """Checks if the given formula contains any quantifiers.

    Parameters:
        formula: formula to check.

    Returns:
        ``False`` if the given formula contains any quantifiers, ``True``
        otherwise.
    """
    # Task 11.3.1

    if is_quantifier(formula.root):
        return False

    if is_binary(formula.root):
        return is_quantifier_free(formula.first) and is_quantifier_free(formula.second)

    if is_unary(formula.root):
        return is_quantifier_free(formula.first)

    return True


def is_in_prenex_normal_form(formula: Formula) -> bool:
    """Checks if the given formula is in prenex normal form.

    Parameters:
        formula: formula to check.

    Returns:
        ``True`` if the given formula in prenex normal form, ``False``
        otherwise.
    """
    # Task 11.3.2

    if is_quantifier(formula.root):
        return is_in_prenex_normal_form(formula.predicate)

    return is_quantifier_free(formula)


def equivalence_of(formula1: Formula, formula2: Formula) -> Formula:
    """States the equivalence of the two given formulas as a formula.

    Parameters:
        formula1: first of the formulas the equivalence of which is to be
            stated.
        formula2: second of the formulas the equivalence of which is to be
            stated.

    Returns:
        The formula ``'((``\ `formula1`\ ``->``\ `formula2`\ ``)&(``\ `formula2`\ ``->``\ `formula1`\ ``))'``.
    """
    return Formula('&', Formula('->', formula1, formula2),
                   Formula('->', formula2, formula1))


def has_uniquely_named_variables(formula: Formula) -> bool:
    """Checks if the given formula has uniquely named variables.

    Parameters:
        formula: formula to check.

    Returns:
        ``False`` if in the given formula some variable name has both quantified
        and free occurrences or is quantified by more than one quantifier,
        ``True`` otherwise.
    """
    forbidden_variables = set(formula.free_variables())

    def has_uniquely_named_variables_helper(formula: Formula) -> bool:
        if is_unary(formula.root):
            return has_uniquely_named_variables_helper(formula.first)
        elif is_binary(formula.root):
            return has_uniquely_named_variables_helper(formula.first) and \
                   has_uniquely_named_variables_helper(formula.second)
        elif is_quantifier(formula.root):
            if formula.variable in forbidden_variables:
                return False
            forbidden_variables.add(formula.variable)
            return has_uniquely_named_variables_helper(formula.predicate)
        else:
            assert is_relation(formula.root) or is_equality(formula.root)
            return True

    return has_uniquely_named_variables_helper(formula)


def uniquely_rename_quantified_variables(formula: Formula) -> \
        Tuple[Formula, Proof]:
    """Converts the given formula to an equivalent formula with uniquely named
    variables, and proves the equivalence of these two formulas.

    Parameters:
        formula: formula to convert, which contains no variable names starting
            with ``z``.

    Returns:
        A pair. The first element of the pair is a formula equivalent to the
        given formula, with the exact same structure but with the additional
        property of having uniquely named variables, obtained by consistently
        replacing each variable name that is bound in the given formula with a
        new variable name obtained by calling
        `next`\ ``(``\ `~logic_utils.fresh_variable_name_generator`\ ``)``. The
        second element of the pair is a proof of the equivalence of the given
        formula and the returned formula (i.e., a proof of
        `equivalence_of`\ ``(``\ `formula`\ ``,``\ `returned_formula`\ ``)``)
        via `~predicates.prover.Prover.AXIOMS` and
        `ADDITIONAL_QUANTIFICATION_AXIOMS`.
    """
    # Task 11.5

    prover = Prover(ADDITIONAL_QUANTIFICATION_AXIOMS)

    # case quantifier
    if is_quantifier(formula.root):
        z_curr = next(fresh_variable_name_generator)
        f_pred_new, to_inline = uniquely_rename_quantified_variables(formula.predicate)
        antecedent = prover.add_proof(to_inline.conclusion, to_inline)

        x = formula.variable
        y = z_curr
        R = formula.predicate.substitute({formula.variable: Term('_')})
        Q = f_pred_new.substitute({formula.variable: Term('_')})

        # case A
        if formula.root is 'A':
            f_imp_fnew = ADDITIONAL_QUANTIFICATION_AXIOMS[14].instantiate({'R': R, 'Q': Q, 'y': y, 'x':x})
            conditional = prover.add_instantiated_assumption(f_imp_fnew, ADDITIONAL_QUANTIFICATION_AXIOMS[14], {'R': R,
                                                                                                            'Q': Q, 'y': y,
                                                                                                                'x':x})
        # case E
        else:
            f_imp_fnew = ADDITIONAL_QUANTIFICATION_AXIOMS[15].instantiate({'R': R, 'Q': Q, 'y': y, 'x': x})
            conditional = prover.add_instantiated_assumption(f_imp_fnew, ADDITIONAL_QUANTIFICATION_AXIOMS[15], {'R': R,
                                                                                                            'Q': Q,'y':y, 'x':x})
        conclusion = f_imp_fnew.second
        prover.add_mp(conclusion, antecedent, conditional)
        f = Formula(formula.root, z_curr, f_pred_new.substitute({formula.variable: Term(z_curr)}))
        p = prover.qed()
        return f, p

    # case all unique
    if has_uniquely_named_variables(formula):
        f_imp_f = Schema(Formula.parse('((R()->Q())&(Q()->R()))'), {'R', 'Q'}).instantiate({'R': formula, 'Q': formula})
        prover.add_tautology(f_imp_f)
        return formula, prover.qed()

    # case ~
    if is_unary(formula.root):
        not_f, to_inline = uniquely_rename_quantified_variables(formula.first)
        step0 = prover.add_proof(to_inline.conclusion, to_inline)

        new_f = Formula('~', not_f)
        f_imp_fchanged = Schema(Formula.parse('((R()->Q())&(Q()->R()))'), {'R', 'Q'}).instantiate(
            {'R': formula, 'Q': new_f})
        prover.add_tautological_implication(f_imp_fchanged, {step0})
        return new_f, prover.qed()

    # case binary
    if is_binary(formula.root):
        f1, to_inline1 = uniquely_rename_quantified_variables(formula.first)
        f2, to_inline2 = uniquely_rename_quantified_variables(formula.second)
        step0 = prover.add_proof(to_inline1.conclusion, to_inline1)
        step1 = prover.add_proof(to_inline2.conclusion, to_inline2)
        f_new = Formula(formula.root, f1, f2)
        f_imp_fchanged = Schema(Formula.parse('((R()->Q())&(Q()->R()))'), {'R', 'Q'}).instantiate(
            {'R': formula, 'Q': f_new})
        prover.add_tautological_implication(f_imp_fchanged, {step0, step1})
        return f_new, prover.qed()


def pull_out_quantifications_across_negation(formula: Formula) -> \
        Tuple[Formula, Proof]:
    """Converts the given formula with uniquely named variables of the form
    ``'~``\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_formula`\ ``]``...\ ``]]'``
    to an equivalent formula of the form
    ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[~``\ `inner_formula`\ ``]``...\ ``]]'``,
    and proves the equivalence of these two formulas.

    Parameters:
        formula: formula to convert, whose root is a negation, i.e., which is of
            the form
            ``'~``\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_formula`\ ``]``...\ ``]]'``
            where `n`>=0, each `Qi` is a quantifier, each `xi` is a variable
            name, and `inner_formula` does not start with a quantifier.

    Returns:
        A pair. The first element of the pair is a formula equivalent to the
        given formula, but of the form
        ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[~``\ `inner_formula`\ ``]``...\ ``]]'``
        where each `Q'i` is a quantifier, and where the `xi` variable names and
        `inner_formula` are the same as in the given formula. The second element
        of the pair is a proof of the equivalence of the given formula and the
        returned formula (i.e., a proof of
        `equivalence_of`\ ``(``\ `formula`\ ``,``\ `returned_formula`\ ``)``)
        via `~predicates.prover.Prover.AXIOMS` and
        `ADDITIONAL_QUANTIFICATION_AXIOMS`.

    Examples:
        >>> formula = Formula.parse('~Ax[Ey[R(x,y)]]')
        >>> returned_formula, proof = pull_out_quantifications_across_negation(
        ...     formula)
        >>> returned_formula
        Ex[Ay[~R(x,y)]]
        >>> proof.is_valid()
        True
        >>> proof.conclusion == equivalence_of(formula, returned_formula)
        True
        >>> proof.assumptions == Prover.AXIOMS.union(
        ...     ADDITIONAL_QUANTIFICATION_AXIOMS)
        True
    """
    assert is_unary(formula.root)
    # Task 11.6

    prover = Prover(ADDITIONAL_QUANTIFICATION_AXIOMS)

    #base case
    if is_quantifier_free(formula):
        equality = equivalence_of(formula, formula)
        prover.add_tautology(equality)
        return formula, prover.qed()

    not_formula = formula.first
    R = not_formula.predicate
    not_r = Formula('~', R)
    R_sub = not_formula.predicate.substitute({not_formula.variable: Term('_')})
    not_r_sub = Formula('~', R_sub)
    x = not_formula.variable


    # if root is 'E'
    if not_formula.root is 'E':
        internal_formula, to_inline = pull_out_quantifications_across_negation(not_r)
        switched_f = Formula('A', x, internal_formula)
        proof_line = ADDITIONAL_QUANTIFICATION_AXIOMS[1].instantiate({'R': R_sub, 'x': x})
        step0 = prover.add_instantiated_assumption(proof_line, ADDITIONAL_QUANTIFICATION_AXIOMS[1], {'R': R_sub, 'x': x})

        Q_sub = internal_formula.substitute({not_formula.variable: Term('_')})
        conditional = ADDITIONAL_QUANTIFICATION_AXIOMS[14].instantiate({'R': not_r_sub, 'Q': Q_sub,
                                                                        'y': x, 'x': x})
        step1 = prover.add_instantiated_assumption(conditional, ADDITIONAL_QUANTIFICATION_AXIOMS[14], {'R': not_r_sub,
                                                                'Q': Q_sub, 'y': x, 'x': x})

    # if root is 'A'
    else:
        internal_formula, to_inline = pull_out_quantifications_across_negation(not_r)
        switched_f = Formula('E', x, internal_formula)
        proof_line = ADDITIONAL_QUANTIFICATION_AXIOMS[0].instantiate({'R': R_sub, 'x': x})
        step0 = prover.add_instantiated_assumption(proof_line, ADDITIONAL_QUANTIFICATION_AXIOMS[0], {'R': R_sub, 'x': x})

        Q_sub = internal_formula.substitute({not_formula.variable: Term('_')})
        conditional = ADDITIONAL_QUANTIFICATION_AXIOMS[15].instantiate({'R': not_r_sub, 'Q': Q_sub,
                                                          'y': x, 'x': x})
        step1 = prover.add_instantiated_assumption(conditional, ADDITIONAL_QUANTIFICATION_AXIOMS[15], {'R': not_r_sub,
                                                                'Q': Q_sub, 'y': x, 'x': x})

    final_formula = Formula(switched_f.root, x, internal_formula)

    step2 = prover.add_proof(to_inline.conclusion, to_inline)
    step3 = prover.add_mp(conditional.second, step2, step1)
    step4 = prover.add_tautological_implication(equivalence_of(formula, final_formula), {step0, step3})
    return final_formula, prover.qed()


def pull_out_quantifications_from_left_across_binary_operator(formula:
Formula) -> \
        Tuple[Formula, Proof]:
    """Converts the given formula with uniquely named variables of the form
    ``'(``\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_first`\ ``]``...\ ``]]``\ `*`\ `second`\ ``)'``
    to an equivalent formula of the form
    ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[(``\ `inner_first`\ `*`\ `second`\ ``)]``...\ ``]]'``
    and proves the equivalence of these two formulas.

    Parameters:
        formula: formula with uniquely named variables to convert, whose root
            is a binary operator, i.e., which is of the form
            ``'(``\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_first`\ ``]``...\ ``]]``\ `*`\ `second`\ ``)'``
            where `*` is a binary operator, `n`>=0, each `Qi` is a quantifier,
            each `xi` is a variable name, and `inner_first` does not start with
            a quantifier.

    Returns:
        A pair. The first element of the pair is a formula equivalent to the
        given formula, but of the form
        ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[(``\ `inner_first`\ `*`\ `second`\ ``)]``...\ ``]]'``
        where each `Q'i` is a quantifier, and where the operator `*`, the `xi`
        variable names, `inner_first`, and `second` are the same as in the given
        formula. The second element of the pair is a proof of the equivalence of
        the given formula and the returned formula (i.e., a proof of
        `equivalence_of`\ ``(``\ `formula`\ ``,``\ `returned_formula`\ ``)``)
        via `~predicates.prover.Prover.AXIOMS` and
        `ADDITIONAL_QUANTIFICATION_AXIOMS`.

    Examples:
        >>> formula = Formula.parse('(Ax[Ey[R(x,y)]]&Ez[P(1,z)])')
        >>> returned_formula, proof = pull_out_quantifications_from_left_across_binary_operator(
        ...     formula)
        >>> returned_formula
        Ax[Ey[(R(x,y)&Ez[P(1,z)])]]
        >>> proof.is_valid()
        True
        >>> proof.conclusion == equivalence_of(formula, returned_formula)
        True
        >>> proof.assumptions == Prover.AXIOMS.union(
        ...     ADDITIONAL_QUANTIFICATION_AXIOMS)
        True
    """
    assert has_uniquely_named_variables(formula)
    assert is_binary(formula.root)
    # Task 11.7.1
    # Schema(Formula.parse('(((Ax[R(x)]&Q())->Ax[(R(x)&Q())])&'
    #                      '(Ax[(R(x)&Q())]->(Ax[R(x)]&Q())))'), {'x', 'R', 'Q'}),
    # Schema(Formula.parse('(((Ex[R(x)]&Q())->Ex[(R(x)&Q())])&'
    #                      '(Ex[(R(x)&Q())]->(Ex[R(x)]&Q())))'), {'x', 'R', 'Q'}),
    prover = Prover(ADDITIONAL_QUANTIFICATION_AXIOMS)


    # base case
    if is_quantifier_free(formula.first):
        equality = equivalence_of(formula, formula)
        prover.add_tautology(equality)
        return formula, prover.qed()

    x_y_dict = {formula.first.variable: Term('_')}
    first_parametrised = formula.first.substitute(x_y_dict)
    axiom_line_dict = {'x': formula.first.variable, 'R':first_parametrised, 'Q': formula.second}

    # recursion case
    if formula.first.root is 'A':
        axiom_line = ADDITIONAL_QUANTIFICATION_AXIOMS[2].instantiate(axiom_line_dict)
        i=2
        j=14

    else:
        axiom_line = ADDITIONAL_QUANTIFICATION_AXIOMS[3].instantiate(axiom_line_dict)
        i=3
        j=15

    step0 = prover.add_instantiated_assumption(axiom_line, ADDITIONAL_QUANTIFICATION_AXIOMS[i], axiom_line_dict)

    internal_f_original = axiom_line.first.second.predicate  # R(x)&Q()
    internal_formula_equivalent, to_inline = pull_out_quantifications_across_binary_operator(internal_f_original)
    step1 = prover.add_proof(to_inline.conclusion, to_inline)  # new internal = old internal

    p_internal_f_original = internal_f_original.substitute(x_y_dict)
    p_internal_formula_equivalent = internal_formula_equivalent.substitute(x_y_dict)
    add_quant_dict = {'R':p_internal_f_original,
                      'Q':p_internal_formula_equivalent,
                      'x':formula.first.variable, 'y': formula.first.variable}

    add_quant_back = ADDITIONAL_QUANTIFICATION_AXIOMS[j].instantiate(add_quant_dict)
    step2 = prover.add_instantiated_assumption(add_quant_back, ADDITIONAL_QUANTIFICATION_AXIOMS[j], add_quant_dict)
    step3 = prover.add_mp(add_quant_back.second, step1, step2)

    step4 = prover.add_tautological_implication(equivalence_of(formula, add_quant_back.second.first.second),{step0, step3})
    return add_quant_back.second.first.second, prover.qed()


    # Schema(Formula.parse('(((R(x)->Q(x))&(Q(x)->R(x)))->'
    #                      '((Ax[R(x)]->Ay[Q(y)])&(Ay[Q(y)]->Ax[R(x)])))'),
    #        {'x', 'y', 'R', 'Q'}),
    # Schema(Formula.parse('(((R(x)->Q(x))&(Q(x)->R(x)))->'
    #                      '((Ex[R(x)]->Ey[Q(y)])&(Ey[Q(y)]->Ex[R(x)])))'),
    #        {'x', 'y', 'R', 'Q'}))





def pull_out_quantifications_from_right_across_binary_operator(formula:
Formula) -> \
        Tuple[Formula, Proof]:
    """Converts the given formula with uniquely named variables of the form
    ``'(``\ `first`\ `*`\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_second`\ ``]``...\ ``]])'``
    to an equivalent formula of the form
    ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[(``\ `first`\ `*`\ `inner_second`\ ``)]``...\ ``]]'``
    and proves the equivalence of these two formulas.

    Parameters:
        formula: formula with uniquely named variables to convert, whose root
            is a binary operator, i.e., which is of the form
            ``'(``\ `first`\ `*`\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_second`\ ``]``...\ ``]])'``
            where `*` is a binary operator, `n`>=0, each `Qi` is a quantifier,
            each `xi` is a variable name, and `inner_second` does not start with
            a quantifier.

    Returns:
        A pair. The first element of the pair is a formula equivalent to the
        given formula, but of the form
        ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[(``\ `first`\ `*`\ `inner_second`\ ``)]``...\ ``]]'``
        where each `Q'i` is a quantifier, and where the operator `*`, the `xi`
        variable names, `first`, and `inner_second` are the same as in the given
        formula. The second element of the pair is a proof of the equivalence of
        the given formula and the returned formula (i.e., a proof of
        `equivalence_of`\ ``(``\ `formula`\ ``,``\ `returned_formula`\ ``)``)
        via `~predicates.prover.Prover.AXIOMS` and
        `ADDITIONAL_QUANTIFICATION_AXIOMS`.

    Examples:
        >>> formula = Formula.parse('(Ax[Ey[R(x,y)]]|Ez[P(1,z)])')
        >>> returned_formula, proof = pull_out_quantifications_from_right_across_binary_operator(
        ...     formula)
        >>> returned_formula
        Ez[(Ax[Ey[R(x,y)]]|P(1,z))]
        >>> proof.is_valid()
        True
        >>> proof.conclusion == equivalence_of(formula, returned_formula)
        True
        >>> proof.assumptions == Prover.AXIOMS.union(
        ...     ADDITIONAL_QUANTIFICATION_AXIOMS)
        True
    """
    assert has_uniquely_named_variables(formula)
    assert is_binary(formula.root)
    # Task 11.7.2


def pull_out_quantifications_across_binary_operator(formula: Formula) -> \
        Tuple[Formula, Proof]:
    """Converts the given formula with uniquely named variables of the form
    ``'(``\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_first`\ ``]``...\ ``]]``\ `*`\ `P1`\ `y1`\ ``[``\ `P2`\ `y2`\ ``[``...\ `Pm`\ `ym`\ ``[``\ `inner_second`\ ``]``...\ ``]])'``
    to an equivalent formula of the form
    ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[``\ `P'1`\ `y1`\ ``[``\ `P'2`\ `y2`\ ``[``...\ `P'm`\ `ym`\ ``[(``\ `inner_first`\ `*`\ `inner_second`\ ``)]``...\ ``]]]``...\ ``]]'``
    and proves the equivalence of these two formulas.

    Parameters:
        formula: formula with uniquely named variables to convert, whose root
            is a binary operator, i.e., which is of the form
            ``'(``\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_first`\ ``]``...\ ``]]``\ `*`\ `P1`\ `y1`\ ``[``\ `P2`\ `y2`\ ``[``...\ `Pm`\ `ym`\ ``[``\ `inner_second`\ ``]``...\ ``]])'``
            where `*` is a binary operator, `n`>=0, `m`>=0, each `Qi` and `Pi`
            is a quantifier, each `xi` and `yi` is a variable name, and neither
            `inner_first` nor `inner_second` starts with a quantifier.

    Returns:
        A pair. The first element of the pair is a formula equivalent to the
        given formula, but of the form
        ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[``\ `P'1`\ `y1`\ ``[``\ `P'2`\ `y2`\ ``[``...\ `P'm`\ `ym`\ ``[(``\ `inner_first`\ `*`\ `inner_second`\ ``)]``...\ ``]]]``...\ ``]]'``
        where each `Q'i` and `P'i` is a quantifier, and where the operator `*`,
        the `xi` and `yi` variable names, `inner_first`, and `inner_second` are
        the same as in the given formula. The second element of the pair is a
        proof of the equivalence of the given formula and the returned formula
        (i.e., a proof of
        `equivalence_of`\ ``(``\ `formula`\ ``,``\ `returned_formula`\ ``)``)
        via `~predicates.prover.Prover.AXIOMS` and
        `ADDITIONAL_QUANTIFICATION_AXIOMS`.

    Examples:
        >>> formula = Formula.parse('(Ax[Ey[R(x,y)]]->Ez[P(1,z)])')
        >>> returned_formula, proof = pull_out_quantifications_across_binary_operator(
        ...     formula)
        >>> returned_formula
        Ex[Ay[Ez[(R(x,y)->P(1,z))]]]
        >>> proof.is_valid()
        True
        >>> proof.conclusion == equivalence_of(formula, returned_formula)
        True
        >>> proof.assumptions == Prover.AXIOMS.union(
        ...     ADDITIONAL_QUANTIFICATION_AXIOMS)
        True
    """
    assert has_uniquely_named_variables(formula)
    assert is_binary(formula.root)
    # Task 11.8


def to_prenex_normal_form_from_uniquely_named_variables(formula: Formula) -> \
        Tuple[Formula, Proof]:
    """Converts the given formula with uniquely named variables to an equivalent
    formula in prenex normal form, and proves the equivalence of these two
    formulas.

    Parameters:
        formula: formula with uniquely named variables to convert.

    Returns:
        A pair. The first element of the pair is a formula equivalent to the
        given formula, but in prenex normal form. The second element of the pair
        is a proof of the equivalence of the given formula and the returned
        formula (i.e., a proof of
        `equivalence_of`\ ``(``\ `formula`\ ``,``\ `returned_formula`\ ``)``)
        via `~predicates.prover.Prover.AXIOMS` and
        `ADDITIONAL_QUANTIFICATION_AXIOMS`.

    Examples:
        >>> formula = Formula.parse('(~(Ax[Ey[R(x,y)]]->Ez[P(1,z)])|S(w))')
        >>> returned_formula, proof = to_prenex_normal_form_from_uniquely_named_variables(
        ...     formula)
        >>> returned_formula
        Ax[Ey[Az[(~(R(x,y)->P(1,z))|S(w))]]]
        >>> proof.is_valid()
        True
        >>> proof.conclusion == equivalence_of(formula, returned_formula)
        True
        >>> proof.assumptions == Prover.AXIOMS.union(
        ...     ADDITIONAL_QUANTIFICATION_AXIOMS)
        True
    """
    assert has_uniquely_named_variables(formula)
    # Task 11.9


def to_prenex_normal_form(formula: Formula) -> Tuple[Formula, Proof]:
    """Converts the given formula to an equivalent formula in prenex normal
    form, and proves the equivalence of these two formulas.

    Parameters:
        formula: formula to convert, which contains no variable names starting
            with ``z``.

    Returns:
        A pair. The first element of the pair is a formula equivalent to the
        given formula, but in prenex normal form. The second element of the pair
        is a proof of the equivalence of the given formula and the returned
        formula (i.e., a proof of
        `equivalence_of`\ ``(``\ `formula`\ ``,``\ `returned_formula`\ ``)``)
        via `~predicates.prover.Prover.AXIOMS` and
        `ADDITIONAL_QUANTIFICATION_AXIOMS`.
    """
    # Task 11.10
