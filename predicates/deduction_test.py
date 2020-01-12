# (c) This file is part of the course
# Mathematical Logic through Programming
# by Gonczarowski and Nisan.
# File name: predicates/deduction_test.py

"""Tests for the predicates.deduction module."""

from predicates.deduction import *

def test_remove_assumption(debug=False):
    from predicates.some_proofs import \
         syllogism_proof, syllogism_proof_with_universal_instantiation,\
         syllogism_all_all_proof,\
         syllogism_all_all_proof_with_tautological_implication,\
         syllogism_all_exists_proof,\
         syllogism_all_exists_proof_with_existential_derivation,\
         GROUP_AXIOMS, unique_zero_proof, lovers_proof, homework_proof
    from predicates.some_proofs_test import \
         test_unique_zero_proof, test_lovers_proof, test_homework_proof

    # Test one invocation
    test_unique_zero_proof()
    proof = unique_zero_proof()
    if (debug):
        print("Testing remove_assumption with assumption 'plus(a,c)=a' for the "
              'following proof:\n' + str(proof))
    result = remove_assumption(proof, Formula.parse('plus(a,c)=a'), debug)
    assert result.assumptions == \
           Prover.AXIOMS.union({Schema(Formula.parse(a)) for a in GROUP_AXIOMS})
    assert str(result.conclusion) == '(plus(a,c)=a->c=0)'
    assert result.is_valid()

    # Test two concurrent invocations
    test_lovers_proof()
    test_homework_proof()
    for proof,assumption1,assumption2 in [
            (syllogism_proof(), 'Ax[(Man(x)->Mortal(x))]', 'Man(aristotle)'),
            (syllogism_proof(), 'Man(aristotle)', 'Ax[(Man(x)->Mortal(x))]'),
            (syllogism_proof_with_universal_instantiation(),
             'Ax[(Man(x)->Mortal(x))]', 'Man(aristotle)'),
            (syllogism_proof_with_universal_instantiation(),
             'Man(aristotle)', 'Ax[(Man(x)->Mortal(x))]'),
            (syllogism_all_all_proof(),
             'Ax[(Greek(x)->Human(x))]', 'Ax[(Human(x)->Mortal(x))]'),
            (syllogism_all_all_proof(),
             'Ax[(Human(x)->Mortal(x))]', 'Ax[(Greek(x)->Human(x))]'),
            (syllogism_all_all_proof_with_tautological_implication(),
             'Ax[(Greek(x)->Human(x))]', 'Ax[(Human(x)->Mortal(x))]'),
            (syllogism_all_all_proof_with_tautological_implication(),
             'Ax[(Human(x)->Mortal(x))]', 'Ax[(Greek(x)->Human(x))]'),
            (syllogism_all_exists_proof(),
             'Ax[(Man(x)->Mortal(x))]', 'Ex[Man(x)]'),
            (syllogism_all_exists_proof(),
             'Ex[Man(x)]', 'Ax[(Man(x)->Mortal(x))]'),
            (syllogism_all_exists_proof_with_existential_derivation(),
             'Ax[(Man(x)->Mortal(x))]', 'Ex[Man(x)]'),
            (syllogism_all_exists_proof_with_existential_derivation(),
             'Ex[Man(x)]', 'Ax[(Man(x)->Mortal(x))]'),
            (lovers_proof(),
             'Ax[Ey[Loves(x,y)]]', 'Ax[Az[Ay[(Loves(x,y)->Loves(z,x))]]]'),
            (lovers_proof(),
             'Ax[Az[Ay[(Loves(x,y)->Loves(z,x))]]]', 'Ax[Ey[Loves(x,y)]]'),
            (homework_proof(),
             '~Ex[(Homework(x)&Fun(x))]', 'Ex[(Homework(x)&Reading(x))]'),
            (homework_proof(),
             'Ex[(Homework(x)&Reading(x))]', '~Ex[(Homework(x)&Fun(x))]')]:
        if (debug):
            print("Testing remove_assumption with assumption '" + assumption1 +
                  "' for the following proof:\n" + str(proof))
        assumption1 = Formula.parse(assumption1)
        assumption2 = Formula.parse(assumption2)
        result1 = remove_assumption(proof, assumption1)
        assert result1.assumptions == Prover.AXIOMS.union({Schema(assumption2)})
        assert result1.conclusion == Formula('->', assumption1,
                                             proof.conclusion)
        assert result1.is_valid()

        if (debug):
            print("Testing remove_assumption with assumption '" +
                  str(assumption2) + "'for the following proof:\n" +
                  str(result1))
        result2 = remove_assumption(result1, assumption2)
        assert result2.assumptions == Prover.AXIOMS
        assert result2.conclusion == Formula('->', assumption2,
                                             Formula('->', assumption1,
                                                     proof.conclusion))
        assert result2.is_valid()
        
def test_proof_by_way_of_contradiction(debug=False):
    # Test on a simple nontautological proof
    prover = Prover(['Ax[x=c]', 'Ax[~x=c]'], debug)
    step1 = prover.add_assumption('Ax[x=c]')
    step2 = prover.add_universal_instantiation('x=c', step1, 'x')
    step3 = prover.add_assumption('Ax[~x=c]')
    step4 = prover.add_universal_instantiation('~x=c', step3, 'x')
    step5 = prover.add_tautological_implication('(z=z&~z=z)', {step2, step4})
    proof = prover.qed()
    if (debug):
        print("Testing proof_by_way_of_contradiction with assumption 'Ax[~x=c]'"
              ' for the following proof:\n' + str(proof))
    result = proof_by_way_of_contradiction(proof, Formula.parse('Ax[~x=c]'),
                                           debug)
    assert result.assumptions == Prover.AXIOMS.union(
        {Schema(Formula.parse('Ax[x=c]'))})
    assert str(result.conclusion) == '~Ax[~x=c]'
    assert result.is_valid()

    if (debug):
        print("Testing proof_by_way_of_contradiction with assumption 'Ax[x=c]' "
              'for the following proof:\n' + str(proof))
    result = proof_by_way_of_contradiction(proof, Formula.parse('Ax[x=c]'),
                                           debug)
    assert result.assumptions == Prover.AXIOMS.union(
        {Schema(Formula.parse('Ax[~x=c]'))})
    assert str(result.conclusion) == '~Ax[x=c]'
    assert result.is_valid()

    # Test on Russell's Paradox proof, when replacing the Axiom Schema of
    # Comprehension with its instance that is actually used.
    from predicates.some_proofs import \
         COMPREHENSION_AXIOM, russell_paradox_proof
    from predicates.some_proofs_test import test_russell_paradox_proof
    test_russell_paradox_proof()
    assumption = Formula.parse(
        'Ey[Ax[((In(x,y)->~In(x,x))&(~In(x,x)->In(x,y)))]]')
    proof = russell_paradox_proof()
    assert COMPREHENSION_AXIOM in proof.assumptions
    new_lines = []
    for line in proof.lines:
        if isinstance(line, Proof.AssumptionLine) and \
           line.assumption == COMPREHENSION_AXIOM:
            assert line.formula == assumption, \
                   'Unexpected instance of COMPREHENSION_AXIOM found in proof' \
                   " of Russell's Paradox. Cannot test " \
                   'proof_by_way_of_contradiction'
            new_lines.append(Proof.AssumptionLine(assumption,
                                                  Schema(assumption), {}))
        else:
            new_lines.append(line)
    new_assumptions = proof.assumptions.union(
        {Schema(assumption)}).difference({COMPREHENSION_AXIOM})
    new_proof = Proof(new_assumptions, proof.conclusion, new_lines)
    assert new_proof.is_valid()

    if debug:
        print("Testing proof_by_way_of_contradiction with assumption '" +
              str(assumption) + "' for the following proof:\n" + str(new_proof))
    result = proof_by_way_of_contradiction(new_proof, assumption, debug)
    assert result.assumptions == Prover.AXIOMS
    assert str(result.conclusion) == \
           '~Ey[Ax[((In(x,y)->~In(x,x))&(~In(x,x)->In(x,y)))]]'
    assert result.is_valid()

def test_ex11(debug=False):
    test_remove_assumption(debug)
    test_proof_by_way_of_contradiction(debug)

def test_all(debug=False):
    test_ex11(debug)
