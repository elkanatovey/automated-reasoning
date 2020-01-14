# (c) This file is part of the course
# Mathematical Logic through Programming
# by Gonczarowski and Nisan.
# File name: predicates/deduction.py

"""Useful proof manipulation maneuvers in predicate logic."""

from predicates.syntax import *
from predicates.proofs import *
from predicates.prover import *

def remove_assumption(proof: Proof, assumption: Formula,
                      print_as_proof_forms: bool = False) -> Proof:
    """Converts the given proof of some `conclusion` formula, an assumption of
    which is `assumption`, to a proof of
    ``'(``\ `assumption`\ ``->``\ `conclusion`\ ``)'`` from the same assumptions
    except `assumption`.

    Parameters:
        proof: valid proof to convert, from assumptions/axioms that include
            `~predicates.prover.Prover.AXIOMS`.
        assumption: formula that is a simple assumption (i.e., without any
            templates) of the given proof, such that no line of the given proof
            is a UG line over a variable that is free in this assumption.

    Returns:
        A valid proof of ``'(``\ `assumption`\ ``->``\ `conclusion`\ ``)'``
        from the same assumptions/axioms as the given proof except `assumption`.
    """        
    assert proof.is_valid()
    assert Schema(assumption) in proof.assumptions
    assert proof.assumptions.issuperset(Prover.AXIOMS)
    for line in proof.lines:
        if isinstance(line, Proof.UGLine):
            assert line.formula.variable not in assumption.free_variables()
    # Task 11.1

    updated_assumptions = set()
    updated_assumptions.update(proof.assumptions)
    updated_assumptions.remove(Schema(assumption))
    updated_proof = Prover(updated_assumptions, print_as_proof_forms)
    line_dict = dict()
    current_line = -1

    for line in proof.lines:
        current_line += 1

        # tautologyLine case
        if isinstance(line, Proof.TautologyLine):
            tautology = Formula('->', assumption, line.formula)
            new_line_num = updated_proof.add_tautology(tautology)
            line_dict[current_line] = new_line_num
            continue

        # assumptionLine case
        if isinstance(line, Proof.AssumptionLine):

            # illegal assumption case
            if line.assumption == Schema(assumption):

                bad_assump_imp_bad_assump = Formula('->', assumption, assumption)
                new_line_num = updated_proof.add_tautology(bad_assump_imp_bad_assump)
                line_dict[current_line] = new_line_num
                continue

            # all other assumptions
            step0 = updated_proof.add_instantiated_assumption(line.formula, line.assumption, line.instantiation_map)

            conc_line = Formula('->', assumption, line.formula)
            i1_line = Formula('->', line.formula, conc_line)

            step1 = updated_proof.add_tautology(i1_line)
            step2 = updated_proof.add_mp(conc_line, step0, step1)
            line_dict[current_line] = step2
            continue

        # ugLine case
        if isinstance(line, Proof.UGLine):
            remapped_line = line_dict[line.predicate_line_number]

            # formulas
            step1_formula = updated_proof._lines[remapped_line].formula

            step1_quantified = Formula('A', line.formula.variable, step1_formula)
            conclusion = Formula('->', assumption, line.formula)
            step2_formula = Formula('->', step1_quantified, conclusion)

            # mappings
            R = step1_formula.second.substitute({
                step1_quantified.variable: Term('_')}, set())
            inst_map = {'R': R, 'Q': assumption, 'x': line.formula.variable}

            # steps
            #Ax[(Q()->R(x))]'
            step1 = updated_proof.add_ug(step1_quantified, remapped_line)
            # Ax[(Q()->R(x))]->(Q()->Ax[R(x)]))'
            step2 = updated_proof.add_instantiated_assumption(step2_formula, updated_proof.US, inst_map)
            # (Q()->Ax[R(x)]))'
            step3 = updated_proof.add_mp(conclusion, step1, step2)
            line_dict[current_line] = step3
            continue

        # MPline case
        if isinstance(line, Proof.MPLine):
            antecedent, conditional = line_dict[line.antecedent_line_number], line_dict[line.conditional_line_number]
            # formulas
            conclusion = Formula('->', assumption, line.formula)
            phi_imp_p = updated_proof._lines[antecedent].formula
            pip_imp_conc = Formula('->', phi_imp_p, conclusion)
            phi_imp_piq = updated_proof._lines[conditional].formula
            d__formula = Formula('->', phi_imp_piq, pip_imp_conc)

            #steps
            step1 = updated_proof.add_tautology(d__formula)
            step2 = updated_proof.add_mp(pip_imp_conc, conditional, step1)
            step3 = updated_proof.add_mp(conclusion, antecedent, step2)
            line_dict[current_line] = step3
            continue

    return updated_proof.qed()

def proof_by_way_of_contradiction(proof: Proof, assumption: Formula,
                                  print_as_proof_forms: bool = False) -> Proof:
    """Converts the given proof of a contradiction, an assumption of which is
    `assumption`, to a proof of ``'~``\ `assumption`\ ``'`` from the same
    assumptions except `assumption`.

    Parameters:
        proof: valid proof of a contradiction (i.e., a formula whose negation is
            a tautology) to convert, from assumptions/axioms that include
            `~predicates.prover.Prover.AXIOMS`.
        assumption: formula that is a simple assumption (i.e., without any
            templates) of the given proof, such that no line of the given proof
            is a UG line over a variable that is free in this assumption.

    Return:
        A valid proof of ``'~``\ `assumption`\ ``'`` from the same
        assumptions/axioms as the given proof except `assumption`.
    """
    assert proof.is_valid()
    assert Schema(assumption) in proof.assumptions
    assert proof.assumptions.issuperset(Prover.AXIOMS)
    for line in proof.lines:
        if isinstance(line, Proof.UGLine):
            assert line.formula.variable not in assumption.free_variables()
    # Task 11.2
