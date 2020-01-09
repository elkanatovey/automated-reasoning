# (c) This file is part of the course
# Mathematical Logic through Programming
# by Gonczarowski and Nisan.
# File name: propositions/tautology.py

"""The Tautology Theorem and its implications."""

from typing import List, Union

from logic_utils import frozendict

from propositions.syntax import *
from propositions.proofs import *
from propositions.deduction import *
from propositions.semantics import *
# from propositions.operators import *
from propositions.axiomatic_systems import *

def formula_comparer(f)-> str:
    "Compares formulas alphabetically without taking into account leading ~"
    f2s = str(f)
    if f2s[0] == '~':
        return f2s[1:]
    else:
        return f2s

def formulae_capturing_model(model: Model) -> List[Formula]:
    """Computes the formulae that capture the given model: ``'``\ `x`\ ``'``
    for each variable `x` that is assigned the value ``True`` in the given
    model, and ``'~``\ `x`\ ``'`` for each variable x that is assigned the value
    ``False``.

    Parameters:
        model: model to construct the formulae for.

    Returns:
        A list of the constructed formulae, ordered alphabetically by variable
        name.

    Examples:
        >>> formulae_capturing_model({'p2': False, 'p1': True, 'q': True})
        [p1, ~p2, q]
    """
    assert is_model(model)
    # Task 6.1a
    formula_list = []
    for k, v in model.items():
        if v:
            formula_list.append(Formula.parse(k))
        else:
            formula_list.append(Formula.parse('~' + k))
    formula_list.sort(key=formula_comparer)
    return formula_list

def prove_in_model(formula: Formula, model:Model) -> Proof:
    """Either proves the given formula or proves its negation, from the formulae
    that capture the given model.

    Parameters:
        formula: formula that contains no constants or operators beyond ``'->'``
            and ``'~'``, whose affirmation or negation is to prove.
        model: model from whose formulae to prove.

    Returns:
        If the given formula evaluates to ``True`` in the given model, then
        a proof of the formula, otherwise a proof of ``'~``\ `formula`\ ``'``.
        The returned proof is from the formulae that capture the given model, in
        the order returned by `formulae_capturing_model`\ ``(``\ `model`\ ``)``,
        via `~propositions.axiomatic_systems.AXIOMATIC_SYSTEM`.
    """
    assert formula.operators().issubset({'->', '~'})
    assert is_model(model)
    # Task 6.1b

    # init proof stuff
    proof_assumptions = formulae_capturing_model(model)
    proof_rules = AXIOMATIC_SYSTEM
    version_true = evaluate(formula, model)
    if version_true:
        #prove true
        proof_conclusion = formula
    else:
        # prove false
        proof_conclusion = Formula('~', formula)

    proof_statement = InferenceRule(proof_assumptions, proof_conclusion)

    # variable case
    if is_variable(str(formula)):
        return Proof(proof_statement, proof_rules, [Proof.Line(
            proof_conclusion, None, None)])

    # case phi1 -> phi2
    elif formula.root == '->':
        if version_true:
            # second true
            if evaluate(formula.second, model):
                proof_start = prove_in_model(formula.second, model)
                return prove_corollary(proof_start, proof_conclusion, I1)

            # first false
            else:
                proof_start = prove_in_model(formula.first, model)
                return prove_corollary(proof_start, proof_conclusion, I2)

        # formula evaluates to false
        else:
            phi1_proof = prove_in_model(formula.first, model)
            phi2_proof = prove_in_model(formula.second, model)
            return combine_proofs(phi1_proof, phi2_proof, proof_conclusion, NI)

    elif formula.root == '~':

        # ~phi evaluates to true
        if version_true:
            return prove_in_model(formula.first, model)

        # ~phi evaluates to false
        else:
            double_neg_removed = prove_in_model(formula.first, model)
            return prove_corollary(double_neg_removed, proof_conclusion, NN)


def reduce_assumption(proof_from_affirmation: Proof,
                      proof_from_negation: Proof) -> Proof:
    """Combines the given two proofs, both of the same formula `conclusion` and
    from the same assumptions except that the last assumption of the latter is
    the negation of that of the former, into a single proof of `conclusion` from
    only the common assumptions.

    Parameters:
        proof_from_affirmation: valid proof of `conclusion` from one or more
            assumptions, the last of which is an assumption `assumption`.
        proof_of_negation: valid proof of `conclusion` from the same assumptions
            and inference rules of `proof_from_affirmation`, but with the last
            assumption being ``'~``\ `assumption` ``'`` instead of `assumption`.

    Returns:
        A valid proof of `conclusion` from only the assumptions common to the
        given proofs (i.e., without the last assumption of each), via the same
        inference rules of the given proofs and in addition
        `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`,
        `~propositions.axiomatic_systems.D`, and
        `~propositions.axiomatic_systems.R`.

    Examples:
        If the two given proofs are of ``['p', 'q'] ==> '(q->p)'`` and of
        ``['p', '~q'] ==> ('q'->'p')``, then the returned proof is of
        ``['p'] ==> '(q->p)'``.
    """
    assert proof_from_affirmation.is_valid()
    assert proof_from_negation.is_valid()
    assert proof_from_affirmation.statement.conclusion == \
           proof_from_negation.statement.conclusion
    assert len(proof_from_affirmation.statement.assumptions) > 0
    assert len(proof_from_negation.statement.assumptions) > 0
    assert proof_from_affirmation.statement.assumptions[:-1] == \
           proof_from_negation.statement.assumptions[:-1]
    assert Formula('~', proof_from_affirmation.statement.assumptions[-1]) == \
           proof_from_negation.statement.assumptions[-1]
    assert proof_from_affirmation.rules == proof_from_negation.rules
    # Task 6.2
    conclusion = proof_from_affirmation.statement.conclusion

    updated_affirmation = remove_assumption(proof_from_affirmation)
    updated_negation = remove_assumption(proof_from_negation)
    combo_proof = combine_proofs(updated_affirmation, updated_negation,
                                 conclusion, R)
    return combo_proof


def prove_tautology(tautology: Formula, model: Model = frozendict()) -> Proof:
    """Proves the given tautology from the formulae that capture the given
    model.

    Parameters:
        tautology: tautology that contains no constants or operators beyond
            ``'->'`` and ``'~'``, to prove.
        model: model over a (possibly empty) prefix (with respect to the
            alphabetical order) of the variables of `tautology`, from whose
            formulae to prove.

    Returns:
        A valid proof of the given tautology from the formulae that capture the
        given model, in the order returned by
        `formulae_capturing_model`\ ``(``\ `model`\ ``)``, via
        `~propositions.axiomatic_systems.AXIOMATIC_SYSTEM`.

    Examples:
        If the given model is the empty dictionary, then the returned proof is
        of the given tautology from no assumptions.
    """
    assert is_tautology(tautology)
    assert tautology.operators().issubset({'->', '~'})
    assert is_model(model)
    assert sorted(tautology.variables())[:len(model)] == sorted(model.keys())
    # Task 6.3a
    model_pos = {}
    model_neg = {}

    # base case
    if model.keys() == tautology.variables():
        return prove_in_model(tautology, model)

    tautology_model_dif = tautology.variables().difference(model.keys())
    missing_vars = sorted(list(tautology_model_dif))

    model_pos.update(model)
    model_neg.update(model)
    model_pos[missing_vars[0]] = True
    model_neg[missing_vars[0]] = False

    # one difference case
    if len(tautology_model_dif) == 1:
        proved_for_model_pos = prove_in_model(tautology, model_pos)
        proved_for_model_neg = prove_in_model(tautology, model_neg)
        return reduce_assumption(proved_for_model_pos, proved_for_model_neg)

    proved_for_model_pos = prove_tautology(tautology, model_pos)
    proved_for_model_neg = prove_tautology(tautology, model_neg)
    return reduce_assumption(proved_for_model_pos, proved_for_model_neg)


def proof_or_counterexample(formula: Formula) -> Union[Proof, Model]:
    """Either proves the given formula or finds a model in which it does not
    hold.

    Parameters:
        formula: formula that contains no constants or operators beyond ``'->'``
            and ``'~'``, to either prove or find a counterexample for.

    Returns:
        If the given formula is a tautology, then an assumptionless proof of the
        formula via `~propositions.axiomatic_systems.AXIOMATIC_SYSTEM`,
        otherwise a model in which the given formula does not hold.
    """
    assert formula.operators().issubset({'->', '~'})
    # Task 6.3b
    atomic_vars = list(formula.variables())
    models = all_models(atomic_vars)

    # look for counterexample
    for model in models:
        if not evaluate(formula, model):
            return model

    # prove tautology
    return prove_tautology(formula, {})




def encode_as_formula(rule: InferenceRule) -> Formula:
    """Encodes the given inference rule as a formula consisting of a chain of
    implications.

    Parameters:
        rule: inference rule to encode.

    Returns:
        The formula encoding the given rule.

    Examples:
        >>> encode_as_formula(InferenceRule([Formula('p1'), Formula('p2'),
        ...                                  Formula('p3'), Formula('p4')],
        ...                                 Formula('q')))
        (p1->(p2->(p3->(p4->q))))
        >>> encode_as_formula(InferenceRule([], Formula('q')))
        q
    """
    # Task 6.4a
    if not len(rule.assumptions):
        return rule.conclusion
    return encode_as_formula(InferenceRule(rule.assumptions[:-1], Formula(
        '->', rule.assumptions[-1], rule.conclusion)))

def prove_sound_inference(rule: InferenceRule) -> Proof:
    """Proves the given sound inference rule.

    Parameters:
        rule: sound inference rule whose assumptions and conclusion that contain
            no constants or operators beyond ``'->'`` and ``'~'``, to prove.

    Returns:
        A valid assumptionless proof of the given sound inference rule via
        `~propositions.axiomatic_systems.AXIOMATIC_SYSTEM`.
    """
    assert is_sound_inference(rule)
    for formula in rule.assumptions + (rule.conclusion,):
        assert formula.operators().issubset({'->', '~'})
    # Task 6.4b

    # encode as tautology
    encoded_irule = encode_as_formula(rule)
    rule_as_tautology = proof_or_counterexample(encoded_irule)
    if not len(rule.assumptions):
        return rule_as_tautology

    proof_assumptions = rule.assumptions
    proof_lines = []
    proof_lines.extend(rule_as_tautology.lines)
    current_conclusion = rule_as_tautology.statement.conclusion
    for assumption in proof_assumptions:
        new_line1 = Proof.Line(assumption, None, None)
        proof_lines.append(new_line1)

        new_line2 = Proof.Line(current_conclusion.second, MP,
                               [len(proof_lines)-1, len(proof_lines)-2])
        proof_lines.append(new_line2)
        current_conclusion = current_conclusion.second

    new_proof = Proof(rule, AXIOMATIC_SYSTEM, proof_lines)

    return new_proof



def model_or_inconsistency(formulae: List[Formula]) -> Union[Model, Proof]:
    """Either finds a model in which all the given formulae hold, or proves
    ``'~(p->p)'`` from these formula.

    Parameters:
        formulae: formulae that use only the operators ``'->'`` and ``'~'``, to
            either find a model for or prove ``'~(p->p)'`` from.

    Returns:
        A model in which all of the given formulae hold if such exists,
        otherwise a proof of '~(p->p)' from the given formulae via
        `~propositions.axiomatic_systems.AXIOMATIC_SYSTEM`.
    """
    for formula in formulae:
        assert formula.operators().issubset({'->', '~'})
    # Task 6.5
    i0_neg = Formula.parse('~(p->p)')
    statement_to_check = InferenceRule(formulae, i0_neg)

    # this means the rules assumptions don't have a joint model
    if is_sound_inference(statement_to_check):
        return prove_sound_inference(statement_to_check)
    else:
        s_vars = statement_to_check.variables()
        models = all_models(list(s_vars))
        for model in models:
            good_setting = True
            for f in formulae:
                if not evaluate(f, model):
                    good_setting = False
                    break
            if good_setting:
                return model

def prove_in_model_full(formula: Formula, model: Model) -> Proof:
    """Either proves the given formula or proves its negation, from the formulae
    that capture the given model.

    Parameters:
        formula: formula that contains no operators beyond ``'->'``, ``'~'``,
            ``'&'``, and ``'|'``, whose affirmation or negation is to prove.
        model: model from whose formulae to prove.

    Returns:
        If the given formula evaluates to ``True`` in the given model, then
        a proof of the formula, otherwise a proof of ``'~``\ `formula`\ ``'``.
        The returned proof is from the formulae that capture the given model, in
        the order returned by `formulae_capturing_model`\ ``(``\ `model`\ ``)``,
        via `~propositions.axiomatic_systems.AXIOMATIC_SYSTEM_FULL`.
    """
    assert formula.operators().issubset({'T', 'F', '->', '~', '&', '|'})
    assert is_model(model)
    # Optional Task 6.6
