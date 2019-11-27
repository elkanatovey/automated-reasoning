# (c) This file is part of the course
# Mathematical Logic through Programming
# by Gonczarowski and Nisan.
# File name: propositions/some_proofs.py

"""Some proofs in propositional logic."""

from propositions.syntax import *
from propositions.proofs import *
from propositions.axiomatic_systems import *
from propositions.deduction import *

# Some inference rules that only use conjunction.

#: Conjunction introduction inference rule
A_RULE = InferenceRule([Formula.parse('x'), Formula.parse('y')],
                       Formula.parse('(x&y)'))
#: Conjunction elimination (right) inference rule
AE1_RULE = InferenceRule([Formula.parse('(x&y)')],Formula.parse('y'))
#: Conjunction elimination (left) inference rule
AE2_RULE = InferenceRule([Formula.parse('(x&y)')],Formula.parse('x'))

def prove_and_commutativity() -> Proof:
    """Proves ``'(q&p)'`` from ``'(p&q)'`` via `A_RULE`, `AE2_RULE`, and
    `AE1_RULE`.

    Returns:
        A valid proof of ``'(q&p)'`` from the single assumption ``'(p&q)'`` via
        the inference rules `A_RULE`, `AE2_RULE`, and `AE1_RULE`.
    """
    # Task 4.7
    formula_pandq = Formula.parse_prefix('(p&q)')[0]
    formula_qandp = Formula.parse_prefix('(q&p)')[0]
    formula_xandy = Formula.parse_prefix('(x&y)')[0]


    proof_assumptions = [formula_pandq]
    proof_conclusion = formula_qandp
    proof_claim = InferenceRule(proof_assumptions, proof_conclusion)

    # rules
    proof_rule1 = InferenceRule([Formula('x'), Formula('y')],
                                         formula_xandy)
    proof_rule2 = InferenceRule([formula_xandy], Formula('x'))
    proof_rule3 = InferenceRule([formula_xandy], Formula('y'))
    rule_set = set()
    rule_set.add(proof_rule1)
    rule_set.add(proof_rule2)
    rule_set.add(proof_rule3)

    # create lines
    line0 = Proof.Line(formula_pandq)
    line1 = Proof.Line(Formula('q'), proof_rule3, [0])
    line2 = Proof.Line(Formula('p'), proof_rule2, [0])
    line3 = Proof.Line(formula_qandp, proof_rule1, [1, 2])
    lines = [line0, line1, line2, line3]

    return Proof(proof_claim, rule_set, lines)

def prove_I0() -> Proof:
    """Proves `~propositions.axiomatic_systems.I0` via
    `~propositions.axiomatic_systems.MP`, `~propositions.axiomatic_systems.I1`,
    and `~propositions.axiomatic_systems.D`.

    Returns:
        A valid proof of `~propositions.axiomatic_systems.I0` from no
        assumptions via the inference rules
        `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I1`, and
        `~propositions.axiomatic_systems.D`.
    """
    # Task 4.8
    p_implies_p = Formula.parse('(p->p)')

    proof_assumptions = []
    proof_conclusion = p_implies_p
    proof_claim = InferenceRule(proof_assumptions, proof_conclusion)

    # rules
    rule_set = set()
    rule_set.add(MP)
    rule_set.add(I1)
    rule_set.add(D)

    # create proof lines
    pqr_sub = Formula.parse('((p->((p->p)->p))->((p->(p->p))->(p->p)))')
    line0 = Proof.Line(pqr_sub, D, [])


    formula_qpq_sub = Formula.parse('(p->((p->p)->p))')
    line1 = Proof.Line(formula_qpq_sub, I1, [])

    formula_qpq_sub2 = Formula.parse('((p->(p->p))->(p->p))')
    line2 = Proof.Line(formula_qpq_sub2, MP, [1, 0])

    specialized_i1 = Formula.parse('(p->(p->p))')
    line3 = Proof.Line(specialized_i1, I1, [])

    line4 = Proof.Line(p_implies_p, MP, [3, 2])

    lines = [line0, line1, line2, line3, line4]

    return Proof(proof_claim, rule_set, lines)

# ((p->((p->p)->p))->((p->(p->p))->(p->p)))
#
# (p->(p->p))
#
#
# stage 0'((p->((p->p)->p))->((p->(p->p))->(p->p)))' Rule D
#
# stage 1 '(p->((p->p)->p))'  Rule I1
#
# stage 2 '(p->((p->p)->p))' + '((p->((p->p)->p))->((p->(p->p))->(p->p)))'
# gives '((p->(p->p))->(p->p))' by rule MP
# stage 3 '(p->(p->p))' by rule I1
# stage 4 '(p->(p->p))' + '((p->(p->p))->(p->p))' gives '(p->p)' by rule MP





#: Hypothetical syllogism
HS = InferenceRule([Formula.parse('(p->q)'), Formula.parse('(q->r)')],
                   Formula.parse('(p->r)'))

def prove_hypothetical_syllogism() -> Proof:
    """Proves `HS` via `~propositions.axiomatic_systems.MP`,
    `~propositions.axiomatic_systems.I0`, `~propositions.axiomatic_systems.I1`,
    and `~propositions.axiomatic_systems.D`.

    Returns:
        A valid proof of `HS` from no assumptions via the inference rules
        `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`, and
        `~propositions.axiomatic_systems.D`.
    """
    # Task 5.5
    p_implies_q = Formula.parse('(p->q)')
    q_implies_r = Formula.parse('(q->r)')
    r = Formula.parse('r')
    p = Formula.parse('p')

    proof_assumptions = [p_implies_q, q_implies_r, p]
    proof_conclusion = r
    proof_claim = InferenceRule(proof_assumptions, proof_conclusion)

    # rules
    rule_set = set()
    rule_set.update([MP, I0, I1, D])

    # create proof lines
    line0 = Proof.Line(p, None, None)
    line1 = Proof.Line(p_implies_q, None, None)
    line2 = Proof.Line(Formula.parse('q'), MP, [0, 1])
    line3 = Proof.Line(q_implies_r, None, None)
    line4 = Proof.Line(Formula.parse('r'), MP, [2, 3])
    proof_lines = [line0, line1, line2, line3, line4]

    # create equivalency
    equivalent_proof = Proof(proof_claim, rule_set, proof_lines)
    updated_proof = remove_assumption(equivalent_proof)
    return updated_proof

def prove_I2() -> Proof:
    """Proves `~propositions.axiomatic_systems.I2` via
    `~propositions.axiomatic_systems.MP`, `~propositions.axiomatic_systems.I0`,
    `~propositions.axiomatic_systems.I1`, `~propositions.axiomatic_systems.D`,
    and `~propositions.axiomatic_systems.N`.

    Returns:
        A valid proof of `~propositions.axiomatic_systems.I2` from no
        assumptions via the inference rules
        `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`,
        `~propositions.axiomatic_systems.D`, and
        `~propositions.axiomatic_systems.N`.
    """
    # Optional Task 6.7a

#: Double-negation elimination
NNE = InferenceRule([], Formula.parse('(~~p->p)'))

def prove_NNE() -> Proof:
    """Proves `NNE` via `~propositions.axiomatic_systems.MP`,
    `~propositions.axiomatic_systems.I0`, `~propositions.axiomatic_systems.I1`,
    `~propositions.axiomatic_systems.D`, and
    `~propositions.axiomatic_systems.N`.

    Returns:
        A valid proof of `NNE` from no assumptions via the inference rules
        `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`,
        `~propositions.axiomatic_systems.D`, and
        `~propositions.axiomatic_systems.N`.
    """
    # Optional Task 6.7b

def prove_NN() -> Proof:
    """Proves `~propositions.axiomatic_systems.NN` via
    `~propositions.axiomatic_systems.MP`, `~propositions.axiomatic_systems.I0`,
    `~propositions.axiomatic_systems.I1`, `~propositions.axiomatic_systems.D`,
    and `~propositions.axiomatic_systems.N`.

    Returns:
        A valid proof of `~propositions.axiomatic_systems.NN` from no
        assumptions via the inference rules
        `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`,
        `~propositions.axiomatic_systems.D`, and
        `~propositions.axiomatic_systems.N`.
    """
    # Optional Task 6.7c

#: Contraposition
CP = InferenceRule([], Formula.parse('((p->q)->(~q->~p))'))

def prove_CP() -> Proof:
    """Proves `CP` via `~propositions.axiomatic_systems.MP`,
    `~propositions.axiomatic_systems.I0`, `~propositions.axiomatic_systems.I1`,
    `~propositions.axiomatic_systems.D`, and
    `~propositions.axiomatic_systems.N`.

    Returns:
        A valid proof of `CP` from no assumptions via the inference rules
        `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`,
        `~propositions.axiomatic_systems.D`, and
        `~propositions.axiomatic_systems.N`.
    """
    # Optional Task 6.7d

def prove_NI() -> Proof:
    """Proves `~propositions.axiomatic_systems.NI` via
    `~propositions.axiomatic_systems.MP`, `~propositions.axiomatic_systems.I0`,
    `~propositions.axiomatic_systems.I1`, `~propositions.axiomatic_systems.D`,
    and `~propositions.axiomatic_systems.N`.

    Returns:
        A valid proof of `~propositions.axiomatic_systems.NI` from no
        assumptions via the inference rules
        `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`,
        `~propositions.axiomatic_systems.D`, and
        `~propositions.axiomatic_systems.N`.
    """
    # Optional Task 6.7e

#: Consequentia mirabilis
CM = InferenceRule([Formula.parse('(~p->p)')], Formula.parse('p'))

def prove_CM() -> Proof:
    """Proves `CM` via `~propositions.axiomatic_systems.MP`,
    `~propositions.axiomatic_systems.I0`, `~propositions.axiomatic_systems.I1`,
    `~propositions.axiomatic_systems.D`, and
    `~propositions.axiomatic_systems.N`.

    Returns:
        A valid proof of `CM` from no assumptions via the inference rules
        `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`,
        `~propositions.axiomatic_systems.D`, and
        `~propositions.axiomatic_systems.N`.
    """
    # Optional Task 6.7f

def prove_R() -> Proof:
    """Proves `~propositions.axiomatic_systems.R` via
    `~propositions.axiomatic_systems.MP`, `~propositions.axiomatic_systems.I0`,
    `~propositions.axiomatic_systems.I1`, `~propositions.axiomatic_systems.D`,
    and `~propositions.axiomatic_systems.N`.

    Returns:
        A valid proof of `~propositions.axiomatic_systems.R` from no assumptions
        via the inference rules `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`,
        `~propositions.axiomatic_systems.D`, and
        `~propositions.axiomatic_systems.N`.
    """
    # Optional Task 6.7g

def prove_N() -> Proof:
    """Proves `~propositions.axiomatic_systems.N` via
    `~propositions.axiomatic_systems.MP`, `~propositions.axiomatic_systems.I0`,
    `~propositions.axiomatic_systems.I1`, `~propositions.axiomatic_systems.D`,
    and `~propositions.axiomatic_systems.N_ALTERNATIVE`.

    Returns:
        A valid proof of `~propositions.axiomatic_systems.N` from no assumptions
        via the inference rules `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`,
        `~propositions.axiomatic_systems.D`, and
        `~propositions.axiomatic_systems.N_ALTERNATIVE`.
    """
    # Optional Task 6.8

def prove_NA1() -> Proof:
    """Proves `~propositions.axiomatic_systems.NA1` via
    `~propositions.axiomatic_systems.MP`, `~propositions.axiomatic_systems.I0`,
    `~propositions.axiomatic_systems.I1`, `~propositions.axiomatic_systems.D`,
    `~propositions.axiomatic_systems.N`, and
    `~propositions.axiomatic_systems.AE1`.

    Returns:
        A valid proof of `~propositions.axiomatic_systems.NA1` from no
        assumptions via the inference rules
        `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`,
        `~propositions.axiomatic_systems.D`, and
        `~propositions.axiomatic_systems.AE1`.
    """
    # Optional Task 6.9a

def prove_NA2() -> Proof:
    """Proves `~propositions.axiomatic_systems.NA2` via
    `~propositions.axiomatic_systems.MP`, `~propositions.axiomatic_systems.I0`,
    `~propositions.axiomatic_systems.I1`, `~propositions.axiomatic_systems.D`,
    `~propositions.axiomatic_systems.N`, and
    `~propositions.axiomatic_systems.AE2`.

    Returns:
        A valid proof of `~propositions.axiomatic_systems.NA2` from no
        assumptions via the inference rules
        `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`,
        `~propositions.axiomatic_systems.D`, and
        `~propositions.axiomatic_systems.AE2`.
    """
    # Optional Task 6.9b

def prove_NO() -> Proof:
    """Proves `~propositions.axiomatic_systems.NO` via
    `~propositions.axiomatic_systems.MP`, `~propositions.axiomatic_systems.I0`,
    `~propositions.axiomatic_systems.I1`, `~propositions.axiomatic_systems.D`,
    `~propositions.axiomatic_systems.N`, and
    `~propositions.axiomatic_systems.OE`.

    Returns:
        A valid proof of `~propositions.axiomatic_systems.NO` from no
        assumptions via the inference rules
        `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`,
        `~propositions.axiomatic_systems.D`, and
        `~propositions.axiomatic_systems.OE`.
    """
    # Optional Task 6.9c
