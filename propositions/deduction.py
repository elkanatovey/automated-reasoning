# (c) This file is part of the course
# Mathematical Logic through Programming
# by Gonczarowski and Nisan.
# File name: propositions/deduction.py

"""Useful proof manipulation maneuvers in propositional logic."""

from propositions.syntax import *
from propositions.proofs import *
from propositions.axiomatic_systems import *

def prove_corollary(antecedent_proof: Proof, consequent: Formula,
                    conditional: InferenceRule) -> Proof:
    """Converts the given proof of a formula `antecedent` into a proof of the
    given formula `consequent` by using the given assumptionless inference rule
    of which ``'(``\ `antecedent`\ ``->``\ `consequent`\ ``)'`` is a
    specialization.

    Parameters:
        antecedent_proof: valid proof of `antecedent`.
        consequent: formula to prove.
        conditional: assumptionless inference rule of which the assumptionless
            inference rule with conclusion
            ``'(``\ `antecedent`\ ``->``\ `consequent`\ ``)'`` is a
            specialization.

    Returns:
        A valid proof of `consequent` from the same assumptions as the given
        proof, via the same inference rules as the given proof and in addition
        `~propositions.axiomatic_systems.MP` and `conditional`.
    """
    assert antecedent_proof.is_valid()
    assert InferenceRule([],
                         Formula('->', antecedent_proof.statement.conclusion,
                                 consequent)).is_specialization_of(conditional)
    # Task 5.3a
    assumptions = antecedent_proof.statement.assumptions
    statement = InferenceRule(assumptions, consequent)

    rules = set()
    rules = rules.union(antecedent_proof.rules)
    rules.add(conditional)
    lines = []
    lines.extend(antecedent_proof.lines)

    f = Formula('->', antecedent_proof.statement.conclusion, consequent)
    new_line1 = Proof.Line(f, conditional, [])
    lines.append(new_line1)
    new_line2 = Proof.Line(consequent, MP, [len(lines)-2, len(lines)-1])
    lines.append(new_line2)
    main_proof = Proof(statement, rules, lines)
    return main_proof

def combine_proofs(antecedent1_proof: Proof, antecedent2_proof: Proof,
                   consequent: Formula, double_conditional: InferenceRule) -> \
        Proof:
    """Combines the given proofs of two formulae `antecedent1` and `antecedent2`
    into a proof of the given formula `consequent` by using the given
    assumptionless inference rule of which
    ``('``\ `antecedent1`\ ``->(``\ `antecedent2`\ ``->``\ `consequent`\ ``))'``
    is a specialization.

    Parameters:
        antecedent1_proof: valid proof of `antecedent1`.
        antecedent2_proof: valid proof of `antecedent2` from the same
            assumptions and inference rules as `antecedent1_proof`.
        consequent: formula to prove.
        double_conditional: assumptionless inference rule of which the
            assumptionless inference rule with conclusion
            ``'(``\ `antecedent1`\ ``->(``\ `antecedent2`\ ``->``\ `consequent`\ ``))'``
            is a specialization.

    Returns:
        A valid proof of `consequent` from the same assumptions as the given
        proofs, via the same inference rules as the given proofs and in addition
        `~propositions.axiomatic_systems.MP` and `conditional`.
    """
    assert antecedent1_proof.is_valid()
    assert antecedent2_proof.is_valid()
    assert antecedent1_proof.statement.assumptions == \
           antecedent2_proof.statement.assumptions
    assert antecedent1_proof.rules == antecedent2_proof.rules
    assert InferenceRule(
        [], Formula('->', antecedent1_proof.statement.conclusion,
        Formula('->', antecedent2_proof.statement.conclusion, consequent))
        ).is_specialization_of(double_conditional)
    # Task 5.3b

    # calc nested rule
    nested_rule = InferenceRule([], double_conditional.conclusion.second)
    nested_claim = prove_corollary(antecedent2_proof, consequent, nested_rule)
    p2_implies_q = nested_claim.lines[-2].formula

    # calc outer layer rule
    top_claim = prove_corollary(antecedent1_proof, p2_implies_q,
                                double_conditional)

    # join proofs
    next_level_lines = []
    next_level_lines.extend(top_claim.lines)
    for line in nested_claim.lines:
        if line.formula == top_claim.statement.conclusion:
            next_level_lines.append(top_claim.lines[-1])
        else:
            if hasattr(line, 'assumptions'):
                current = line
                assumptions = list(current.assumptions)
                for i in range(len(current.assumptions)):
                    assumptions[i] += len(top_claim.lines)
                next_level_lines.append(Proof.Line(current.formula,
                                                   current.rule, assumptions))
            else:
                next_level_lines.append(line)

    next_level_assumptions = InferenceRule(
        antecedent1_proof.statement.assumptions, consequent)
    next_level = Proof(next_level_assumptions, top_claim.rules, next_level_lines)
    return next_level

def remove_assumption(proof: Proof) -> Proof:
    """Converts a proof of some `conclusion` formula, the last assumption of
    which is an assumption `assumption`, into a proof of
    ``'(``\ `assumption`\ ``->``\ `conclusion`\ ``)'`` from the same assumptions
    except `assumption`.

    Parameters:
        proof: valid proof to convert, with at least one assumption, via some
            set of inference rules all of which have no assumptions except
            perhaps `~propositions.axiomatic_systems.MP`.

    Return:
        A valid proof of ``'(``\ `assumptions`\ ``->``\ `conclusion`\ ``)'``
        from the same assumptions as the given proof except the last one, via
        the same inference rules as the given proof and in addition
        `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`, and
        `~propositions.axiomatic_systems.D`.
    """        
    assert proof.is_valid()
    assert len(proof.statement.assumptions) > 0
    for rule in proof.rules:
        assert rule == MP or len(rule.assumptions) == 0
    # Task 5.4
    new_assumptions = proof.statement.assumptions[:-1]
    disallowed_assumption = proof.statement.assumptions[-1]
    new_conclusion = Formula('->', disallowed_assumption,
                             proof.statement.conclusion)
    new_statement = InferenceRule(new_assumptions, new_conclusion)
    new_rules = set()
    new_rules.update(proof.rules)
    new_rules.update([MP, I0, I1, D])
    new_lines = []
    updated_line_location = []
    current_location = 0
    for line in proof.lines:

        # case line is disallowed_assumption
        if line.formula == disallowed_assumption:
            new_lines.append(Proof.Line(Formula('->', line.formula,
                                                line.formula), I0, []))
            updated_line_location.append(current_location)
            current_location += 1

        # case line is proved with MP
        elif line.rule is MP:
            new_assumption_locations = []
            for assumption in line.assumptions:
                new_assumption_locations.append(updated_line_location[assumption])

            p1 = new_lines[new_assumption_locations[1]].formula
            updated_conclusion = Formula('->', disallowed_assumption,
                                      line.formula)
            q1 = Formula('->', new_lines[new_assumption_locations[
                0]].formula, updated_conclusion)
            p1_imp_q1 = Formula('->', p1, q1)

            d_line = Proof.Line(p1_imp_q1, D, [])
            new_lines.append(d_line)

            q1_line = Proof.Line(q1, MP, [new_assumption_locations[1],
                                          len(new_lines)-1])
            new_lines.append(q1_line)

            result_line = Proof.Line(updated_conclusion, MP,
                                     [new_assumption_locations[0],
                                      len(new_lines)-1])
            new_lines.append(result_line)

            updated_line_location.append(current_location + 2)
            current_location += 3

        # case other inference rule or assumption
        else:
            new_lines.append(line)  # allowed

            disallowed_imp_allowed = Formula('->', disallowed_assumption,
                                             line.formula)
            i1_line_formula = Formula('->', line.formula,
                                      disallowed_imp_allowed)
            new_lines.append(Proof.Line(i1_line_formula, I1, []))  # i1 line

            new_lines.append(Proof.Line(disallowed_imp_allowed, MP, [len(
                new_lines)-2, len(new_lines)-1]))

            updated_line_location.append(current_location + 2)
            current_location += 3

    updated_proof = Proof(new_statement, new_rules, new_lines)
    return updated_proof




def proof_from_inconsistency(proof_of_affirmation: Proof,
                             proof_of_negation: Proof, conclusion: Formula) -> \
        Proof:
    """Combines the given proofs of a formula `affirmation` and its negation
    ``'~``\ `affirmation`\ ``'`` into a proof of the given formula.

    Parameters:
        proof_of_affirmation: valid proof of `affirmation`.
        proof_of_negation: valid proof of ``'~``\ `affirmation`\ ``'`` from the
            same assumptions and inference rules of `proof_of_affirmation`.

    Returns:
        A valid proof of `conclusion` from the same assumptions as the given
        proofs, via the same inference rules as the given proofs and in addition
        `~propositions.axiomatic_systems.MP` and
        `~propositions.axiomatic_systems.I2`.
    """
    assert proof_of_affirmation.is_valid()
    assert proof_of_negation.is_valid()
    assert proof_of_affirmation.statement.assumptions == \
           proof_of_negation.statement.assumptions
    assert Formula('~', proof_of_affirmation.statement.conclusion) == \
           proof_of_negation.statement.conclusion
    assert proof_of_affirmation.rules == proof_of_negation.rules
    # Task 5.6

def prove_by_contradiction(proof: Proof) -> Proof:
    """Converts the given proof of ``'~(p->p)'``, the last assumption of which
    is an assumption ``'~``\ `formula`\ ``'``, into a proof of `formula` from
    the same assumptions except ``'~``\ `formula`\ ``'``.

    Parameters:
        proof: valid proof of ``'~(p->p)'`` to convert, the last assumption of
            which is of the form ``'~``\ `formula`\ ``'``, via some set of
            inference rules all of which have no assumptions except perhaps
            `~propositions.axiomatic_systems.MP`.

    Return:
        A valid proof of `formula` from the same assumptions as the given proof
        except the last one, via the same inference rules as the given proof and
        in addition `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`,
        `~propositions.axiomatic_systems.D`, and
        `~propositions.axiomatic_systems.N`.
    """
    assert proof.is_valid()
    assert proof.statement.conclusion == Formula.parse('~(p->p)')
    assert len(proof.statement.assumptions) > 0
    assert proof.statement.assumptions[-1].root == '~'
    for rule in proof.rules:
        assert rule == MP or len(rule.assumptions) == 0
    # Task 5.7
