# (c) This file is part of the course
# Mathematical Logic through Programming
# by Gonczarowski and Nisan.
# File name: predicates/completeness_test.py

"""Tests for the predicates.completeness module."""

from propositions.semantics import is_tautology
from predicates.syntax import *
from predicates.semantics import *
from predicates.completeness import *

# Tests for is_***_closed functions

def test_is_primitively_closed(debug=False):
    _test_is_closed(test_primitively=True,debug=debug)
    
def test_is_universally_closed(debug=False):
    _test_is_closed(test_universally=True,debug=debug)

def test_is_existentially_closed(debug=False):
    _test_is_closed(test_existentially=True,debug=debug)

def _test_is_closed(test_primitively=False, test_universally=False,
                    test_existentially=False, debug=False):
    def _test_closures(sentences, primitively, universally, existentially):
        sentences = frozenset(sentences)
        if test_primitively:
            assert is_primitively_closed(sentences) == primitively
        if test_universally:
            assert is_universally_closed(sentences) == universally
        if test_existentially:
            assert is_existentially_closed(sentences) == existentially

    # Test on closed sets
    for six_element_group_primitives in [
            SIX_ELEMENT_COMMUTATIVE_GROUP_PRIMITIVES,
            SIX_ELEMENT_NONCOMMUTATIVE_GROUP_PRIMITIVES]:
        if debug:
            print('Testing is_closed for the six-element',
                  'noncommutative'
                  if six_element_group_primitives ==
                     SIX_ELEMENT_NONCOMMUTATIVE_GROUP_PRIMITIVES
                  else 'commutative',
                  'group...')
        if debug:
            print('Testing on primitives')
        _test_closures(six_element_group_primitives, True, True, True)
        
        if debug:
            print('Testing on primitives + zero axiom')
        _test_closures(six_element_group_primitives.union({ZERO_AXIOM}),
                       True, True, True)
        if debug:
            print('Testing on primitives + zero axiom + commutativity')
        _test_closures(six_element_group_primitives.union(
                           {ZERO_AXIOM, COMMUTATIVITY_AXIOM},
                           SIX_ELEMENT_COMMUTATIVITY_CLOSURE),
                       True, True, True)
        if debug:
            print('Testing on primitives + negation closure')
        _test_closures(six_element_group_primitives.union(
                           SIX_ELEMENT_NEGATION_CLOSURE),
                       True, True, True)
        if debug:
            print('Testing on primitives + negation')
        _test_closures(six_element_group_primitives.union(
                           {NEGATION_AXIOM}, SIX_ELEMENT_NEGATION_CLOSURE),
                       True, True, True)
        if debug:
            print('Testing on primitives + noncommutativity closure')
        _test_closures(
            six_element_group_primitives.union(
                SIX_ELEMENT_NONCOMMUTATIVE_GROUP_NONCOMMUTATIVITY_CLOSURE),
            True, True, True)
        if debug:
            print('Testing on primitives + noncommutativity')
        _test_closures(
            six_element_group_primitives.union(
                {NONCOMMUTATIVITY},
                SIX_ELEMENT_NONCOMMUTATIVE_GROUP_NONCOMMUTATIVITY_CLOSURE),
            True, True, True)
        if debug:
            print('Testing on primitives + zero axiom + negation + '
                  'commutativity + noncommutativity')
        _test_closures(
            six_element_group_primitives.union(
                {ZERO_AXIOM, NEGATION_AXIOM, COMMUTATIVITY_AXIOM,
                 NONCOMMUTATIVITY},
                SIX_ELEMENT_NEGATION_CLOSURE, SIX_ELEMENT_COMMUTATIVITY_CLOSURE,
                SIX_ELEMENT_NONCOMMUTATIVE_GROUP_NONCOMMUTATIVITY_CLOSURE),
            True, True, True)

    # Test on closed but inconsistent set
    if (debug):
        print('Testing on closed but inconsistent set')
        _test_closures(
            SIX_ELEMENT_COMMUTATIVE_GROUP_PRIMITIVES.union(
                SIX_ELEMENT_NONCOMMUTATIVE_GROUP_PRIMITIVES), True, True, True)

    # Test on nonclosed sets
    for six_element_group_primitives in [
            SIX_ELEMENT_COMMUTATIVE_GROUP_PRIMITIVES,
            SIX_ELEMENT_NONCOMMUTATIVE_GROUP_PRIMITIVES]:
        if debug:
            print('Testing is_closed for the six-element',
                  'noncommutative'
                  if six_element_group_primitives ==
                     SIX_ELEMENT_NONCOMMUTATIVE_GROUP_PRIMITIVES
                  else 'commutative',
                  'group...')
        if debug:
            print('Testing on closed except primitively')
        # '~Plus(4,3,5)' is in the primitives of both groups
        _test_closures(six_element_group_primitives -
                       {Formula.parse('~Plus(4,3,5)')},
                       False, True, True)
        # Check that repetitions are covered:
        # 'Plus(0,0,0)' is in the primitives of both groups
        _test_closures(six_element_group_primitives -
                       {Formula.parse('Plus(0,0,0)')},
                       False, True, True)
        # '~Plus(1,3,3)' is in the primitives of both groups
        _test_closures(six_element_group_primitives -
                       {Formula.parse('~Plus(1,3,3)')},
                       False, True, True)
        # 'Plus(2,3,5)' is in SIX_ELEMENT_COMMUTATIVE_GROUP_PRIMITIVES,
        # 'Plus(1,3,5)' is in SIX_ELEMENT_NONCOMMUTATIVE_GROUP_PRIMITIVES
        _test_closures(six_element_group_primitives -
                       {Formula.parse('Plus(2,3,5)'),
                        Formula.parse('Plus(1,3,5)')},
                       False, True, True)
        if debug:
            print('Testing on closed except universally')
        _test_closures((six_element_group_primitives -
                        {Formula.parse('Plus(3,0,3)')}).union(
                            {Formula.parse('~Plus(3,0,3)'),
                             ZERO_AXIOM}),
                       True, False, True)
        _test_closures(six_element_group_primitives.union(
            {ZERO_AXIOM, NEGATION_AXIOM, COMMUTATIVITY_AXIOM},
            SIX_ELEMENT_NEGATION_CLOSURE,
                SIX_ELEMENT_COMMUTATIVITY_CLOSURE -
                {Formula.parse('Ay[Az[(Plus(z,2,y)->Plus(z,y,2))]]')}),
            True, False, True)
        _test_closures(six_element_group_primitives.union(
                           {ZERO_AXIOM, NEGATION_AXIOM, COMMUTATIVITY_AXIOM},
                           SIX_ELEMENT_NEGATION_CLOSURE,
                           SIX_ELEMENT_COMMUTATIVITY_CLOSURE -
                           {Formula.parse('Az[(Plus(z,5,4)->Plus(z,4,5))]')}),
                       True, False, True)
        _test_closures(six_element_group_primitives.union(
                           {ZERO_AXIOM, NEGATION_AXIOM, COMMUTATIVITY_AXIOM},
                           SIX_ELEMENT_NEGATION_CLOSURE,
                           SIX_ELEMENT_COMMUTATIVITY_CLOSURE -
                           {Formula.parse('(Plus(4,3,1)->Plus(4,1,3))')}),
                       True, False, True)
        _test_closures(six_element_group_primitives.union(
                           {ZERO_AXIOM, NEGATION_AXIOM, COMMUTATIVITY_AXIOM},
                           SIX_ELEMENT_NEGATION_CLOSURE -
                           {Formula.parse('Ey[Plus(0,y,3)]')},
                           SIX_ELEMENT_COMMUTATIVITY_CLOSURE),
                       True, False, True)
        if debug:
            print('Testing on closed except existentially')
        _test_closures((six_element_group_primitives -
                        {Formula.parse('Plus(0,4,2)'),
                         Formula.parse('Plus(0,4,5)')}).union(
                             {Formula.parse('~Plus(0,4,2)'),
                              Formula.parse('~Plus(0,4,5)')},
                             SIX_ELEMENT_NEGATION_CLOSURE),
                       True, True, False)
        _test_closures(
            six_element_group_primitives.union(
                {ZERO_AXIOM, NEGATION_AXIOM, NONCOMMUTATIVITY},
                SIX_ELEMENT_NEGATION_CLOSURE,
                SIX_ELEMENT_NONCOMMUTATIVE_GROUP_NONCOMMUTATIVITY_CLOSURE -
                    {Formula.parse('Ey[Ez[(Plus(z,1,y)&~Plus(z,y,1))]]')}),
            True, True, False)
        _test_closures(
            six_element_group_primitives.union(
                {ZERO_AXIOM, NEGATION_AXIOM, NONCOMMUTATIVITY},
                SIX_ELEMENT_NEGATION_CLOSURE,
                SIX_ELEMENT_NONCOMMUTATIVE_GROUP_NONCOMMUTATIVITY_CLOSURE -
                    {Formula.parse('Ez[(Plus(z,1,2)&~Plus(z,2,1))]')}),
            True, True, False)
        _test_closures(
            six_element_group_primitives.union(
                {ZERO_AXIOM, NEGATION_AXIOM, NONCOMMUTATIVITY},
                SIX_ELEMENT_NEGATION_CLOSURE,
                SIX_ELEMENT_NONCOMMUTATIVE_GROUP_NONCOMMUTATIVITY_CLOSURE -
                    {Formula.parse('(Plus(5,1,2)&~Plus(5,2,1))')}),
            True, True, False)

def test_find_unsatisfied_quantifier_free_sentence(debug=False):
    class noniterable_collection:
        def __init__(self, set_):
            self._contains = lambda x:x in set_
        def __contains__(self, a):
            return self._contains(a)

    assert SIX_ELEMENT_NONCOMMUTATIVE_GROUP_MODEL.is_model_of(
        SIX_ELEMENT_NONCOMMUTATIVE_GROUP_PRIMITIVES)
    sentences = SIX_ELEMENT_NONCOMMUTATIVE_GROUP_PRIMITIVES.union(
                    {COMMUTATIVITY_AXIOM}, SIX_ELEMENT_COMMUTATIVITY_CLOSURE)
    assert is_closed(sentences)
    if debug:
        print('Testing find_unsatisfied_quantifier_free_sentence for the '
              'six-element noncommutative group and the commutativity axiom')
    quantifier_free = find_unsatisfied_quantifier_free_sentence(
        noniterable_collection(sentences),
        SIX_ELEMENT_NONCOMMUTATIVE_GROUP_MODEL, COMMUTATIVITY_AXIOM)
    assert is_quantifier_free(quantifier_free)
    assert quantifier_free in sentences
    assert not SIX_ELEMENT_NONCOMMUTATIVE_GROUP_MODEL.evaluate_formula(
        quantifier_free)

    assert SIX_ELEMENT_COMMUTATIVE_GROUP_MODEL.is_model_of(
        SIX_ELEMENT_COMMUTATIVE_GROUP_PRIMITIVES)
    sentences = SIX_ELEMENT_COMMUTATIVE_GROUP_PRIMITIVES.union(
                    {NONCOMMUTATIVITY},
                    SIX_ELEMENT_NONCOMMUTATIVE_GROUP_NONCOMMUTATIVITY_CLOSURE)
    assert is_closed(sentences)
    if debug:
        print('Testing find_unsatisfied_quantifier_free_sentence for the '
              'six-element commutative group and the noncommutativity axiom')
    quantifier_free = find_unsatisfied_quantifier_free_sentence(
        noniterable_collection(sentences), SIX_ELEMENT_COMMUTATIVE_GROUP_MODEL,
        NONCOMMUTATIVITY)
    assert is_quantifier_free(quantifier_free)
    assert quantifier_free in sentences
    assert not is_quantifier(quantifier_free.root)
    assert not SIX_ELEMENT_COMMUTATIVE_GROUP_MODEL.evaluate_formula(
        quantifier_free)

def test_model_or_inconsistency(debug=False):
    for six_element_group_primitives in [
            SIX_ELEMENT_COMMUTATIVE_GROUP_PRIMITIVES,
            SIX_ELEMENT_NONCOMMUTATIVE_GROUP_PRIMITIVES]:
        for commutativity in [
            {COMMUTATIVITY_AXIOM}.union(SIX_ELEMENT_COMMUTATIVITY_CLOSURE),
            {NONCOMMUTATIVITY}.union(
                SIX_ELEMENT_NONCOMMUTATIVE_GROUP_NONCOMMUTATIVITY_CLOSURE)]:
            sentences = six_element_group_primitives.union(
                            {ZERO_AXIOM, NEGATION_AXIOM},
                            SIX_ELEMENT_NEGATION_CLOSURE, commutativity)
            if (debug):
                print('Testing model_or_inconsistency for the six-element',
                      'noncommutative'
                      if six_element_group_primitives ==
                         SIX_ELEMENT_NONCOMMUTATIVE_GROUP_PRIMITIVES
                      else 'commutative',
                      'group with the zero, negation, and ',
                      'commutativity'
                      if COMMUTATIVITY_AXIOM in commutativity
                      else 'noncommutativity',
                      'axioms')
            result = model_or_inconsistency(frozenset(sentences))
            if type(result) is Model:
                if debug:
                    print('Verifying returned model:', result)
                assert result.is_model_of(sentences)
            else:
                assert type(result) is Proof
                assert set(result.assumptions).issubset(
                    {Schema(s) for s in sentences}.union(Prover.AXIOMS))
                assert is_tautology(
                    Formula('~', result.conclusion).propositional_skeleton()[0])
                if debug:
                    print('Verifying returned proof (' +
                          '{:,}'.format(len(result.lines)),
                          'lines) of', result.conclusion)
                assert result.is_valid()

def test_combine_contradictions(debug=False):
    schema = Schema(Formula.parse('(~Ax[R(x)]->Ex[~R(x)])'), {'x', 'R'})
    common_assumptions = {
        schema, Schema(Formula.parse('Ex[~R(x)]')),
        Schema(Formula.parse('Ax[R(x)]'))}

    # Contradiction from 'Ex[~R(x)]' and 'Ax[(~R(x)->(Q()&~Q()))]'
    prover_from_affirmation = \
        Prover(common_assumptions.union({'Ax[(~R(x)->(Q()&~Q()))]'}))
    step1 = prover_from_affirmation.add_assumption('Ex[~R(x)]')
    step2 = prover_from_affirmation.add_assumption('Ax[(~R(x)->(Q()&~Q()))]')
    step3 = prover_from_affirmation.add_instantiated_assumption(
        '((Ax[(~R(x)->(Q()&~Q()))]&Ex[~R(x)])->(Q()&~Q()))', Prover.ES,
        {'R':'~R(_)', 'Q':'(Q()&~Q())'})
    prover_from_affirmation.add_tautological_implication(
        '(Q()&~Q())', {step1, step2, step3})
    proof_from_affirmation = prover_from_affirmation.qed()

    # Contradiction from 'Ax[R(x)]' and '~Ax[(~R(x)->(Q()&~Q()))]'
    prover_from_negation = \
        Prover(common_assumptions.union({'~Ax[(~R(x)->(Q()&~Q()))]'}))
    step1 = prover_from_negation.add_assumption('Ax[R(x)]')
    step2 = prover_from_negation.add_assumption('~Ax[(~R(x)->(Q()&~Q()))]')
    step3 = prover_from_negation.add_instantiated_assumption(
        '(~Ax[(~R(x)->(Q()&~Q()))]->Ex[~(~R(x)->(Q()&~Q()))])', schema,
        {'R':'(~R(_)->(Q()&~Q()))'})
    step4 = prover_from_negation.add_tautological_implication(
        'Ex[~(~R(x)->(Q()&~Q()))]', {step2, step3})
    step5 = prover_from_negation.add_instantiated_assumption(
        '(Ax[R(x)]->R(x))', Prover.UI, {'c':'x'})
    step6 = prover_from_negation.add_tautological_implication(
        '(~(~R(x)->(Q()&~Q()))->~Ax[R(x)])', {step5})
    step7 = prover_from_negation.add_existential_derivation(
        '~Ax[R(x)]', step4, step6)
    step8 = prover_from_negation.add_tautological_implication(
        '(Ax[R(x)]&~Ax[R(x)])', {step1, step7})
    proof_from_negation = prover_from_negation.qed()

    if (debug):
        print('Testing combine_contradictions for the following two proofs:\n',
              proof_from_affirmation, '\n', proof_from_negation)
    combined = combine_contradictions(proof_from_affirmation,
                                      proof_from_negation)
    assert combined.assumptions == Prover.AXIOMS.union(common_assumptions)
    assert is_tautology(
        Formula('~', combined.conclusion).propositional_skeleton()[0])
    if debug:
        print('Verifying returned proof (' +
              '{:,}'.format(len(combined.lines)),
              'lines) of', combined.conclusion)
    assert combined.is_valid()

def test_eliminate_universal_instantiation_assumption(debug=False):
    assumptions = [Schema(Formula.parse('~R(c)')),
                   Schema(Formula.parse('Ax[R(x)]')),
                   Schema(Formula.parse('R(c)'))]
    prover = Prover(assumptions)
    step1 = prover.add_assumption('~R(c)')
    step2 = prover.add_assumption('R(c)')
    prover.add_tautological_implication('(R(c)&~R(c))', {step1, step2})
    proof = prover.qed()

    if (debug):
        print('Testing eliminate_universal_instantiation_assumption for the '
              'following proof:\n', proof)
    eliminated = eliminate_universal_instantiation_assumption(
        proof, 'c', Formula.parse('R(c)'), Formula.parse('Ax[R(x)]'))
    assert eliminated.assumptions == \
           Prover.AXIOMS.union(assumptions) - {Schema(Formula.parse('R(c)'))}
    assert is_tautology(
        Formula('~', eliminated.conclusion).propositional_skeleton()[0])
    if debug:
        print('Verifying returned proof (' +
              '{:,}'.format(len(eliminated.lines)),
              'lines) of', eliminated.conclusion)
    assert eliminated.is_valid()

def test_universal_closure_step(debug=False):
    if debug:
        print('Testing universal_closure_step on zero axiom with six '
              'elements...')
    augmented = universal_closure_step(frozenset(
        {ZERO_AXIOM}.union(SENTENCES_WITH_SIX_ELEMENTS)))
    assert augmented == {ZERO_AXIOM}.union(
        SENTENCES_WITH_SIX_ELEMENTS, SIX_ELEMENT_ZERO_AXIOM_CLOSURE)
    assert is_universally_closed(augmented)
    if debug:
        print('Testing universal_closure_step on result...')
    assert universal_closure_step(augmented) == augmented

    if debug:
        print('Testing universal_closure_step on negation axiom with six '
              'elements...')
    augmented = universal_closure_step(frozenset(
        {NEGATION_AXIOM}.union(SENTENCES_WITH_SIX_ELEMENTS)))
    assert augmented == {NEGATION_AXIOM}.union(
        SENTENCES_WITH_SIX_ELEMENTS, SIX_ELEMENT_NEGATION_CLOSURE)
    assert is_universally_closed(augmented)
    if debug:
        print('Testing universal_closure_step on result...')
    assert universal_closure_step(augmented) == augmented

    if debug:
        print('Testing universal_closure_step on commutativity axiom with six '
              'elements...')
    augmented = universal_closure_step(frozenset(
        {COMMUTATIVITY_AXIOM}.union(SENTENCES_WITH_SIX_ELEMENTS)))
    assert augmented == {COMMUTATIVITY_AXIOM}.union(
        SENTENCES_WITH_SIX_ELEMENTS, SIX_ELEMENT_COMMUTATIVITY_CLOSURE1)
    assert not is_universally_closed(augmented)
    if debug:
        print('Testing universal_closure_step on result...')
    augmented = universal_closure_step(augmented)
    assert augmented == {COMMUTATIVITY_AXIOM}.union(
        SENTENCES_WITH_SIX_ELEMENTS, SIX_ELEMENT_COMMUTATIVITY_CLOSURE1,
        SIX_ELEMENT_COMMUTATIVITY_CLOSURE2)
    assert not is_universally_closed(augmented)
    if debug:
        print('Testing universal_closure_step on result...')
    augmented = universal_closure_step(augmented)
    assert augmented == {COMMUTATIVITY_AXIOM}.union(
        SENTENCES_WITH_SIX_ELEMENTS, SIX_ELEMENT_COMMUTATIVITY_CLOSURE1,
        SIX_ELEMENT_COMMUTATIVITY_CLOSURE2, SIX_ELEMENT_COMMUTATIVITY_CLOSURE3)
    assert is_universally_closed(augmented)
    if debug:
        print('Testing universal_closure_step on result...')
    assert universal_closure_step(augmented) == augmented

    if debug:
        print('Testing universal_closure_step on zero axiom + negation + '
              'commutativity with six elements...')
    augmented = universal_closure_step(frozenset(
        {ZERO_AXIOM, NEGATION_AXIOM, COMMUTATIVITY_AXIOM}.union(
            SENTENCES_WITH_SIX_ELEMENTS)))
    assert {ZERO_AXIOM, NEGATION_AXIOM, COMMUTATIVITY_AXIOM}.union(
        SENTENCES_WITH_SIX_ELEMENTS).issubset(augmented)
    assert len(augmented) == 9+6+6+6
    assert not is_universally_closed(augmented)
    if debug:
        print('Testing universal_closure_step on result...')
    augmented = universal_closure_step(augmented)
    assert len(augmented) == 9+6+6+6+6*6
    assert not is_universally_closed(augmented)
    if debug:
        print('Testing universal_closure_step on result...')
    augmented = universal_closure_step(augmented)
    assert len(augmented) == 9+6+6+6+6*6+6*6*6
    assert is_universally_closed(augmented)
    assert SIX_ELEMENT_COMMUTATIVE_GROUP_MODEL.is_model_of(augmented)
    if debug:
        print('Testing universal_closure_step on result...')
    assert universal_closure_step(augmented) == augmented

    if debug:
        print('Testing universal_closure_step on zero axiom + negation + '
              'commutativity with ten elements...')
    sentences_with_ten_elements = {Formula.parse(s) for s in {
        'SAME(0,0)', 'SAME(1,1)', 'SAME(2,2)', 'SAME(3,3)', 'SAME(4,4)',
        'SAME(5,5)', 'SAME(6,6)', 'SAME(7,7)', 'SAME(8,8)', 'SAME(9,9)'}}
    augmented = universal_closure_step(frozenset(
        {ZERO_AXIOM, NEGATION_AXIOM, COMMUTATIVITY_AXIOM}.union(
            sentences_with_ten_elements)))
    assert {ZERO_AXIOM, NEGATION_AXIOM, COMMUTATIVITY_AXIOM}.union(
        sentences_with_ten_elements).issubset(augmented)
    assert len(augmented) == 13+10+10+10
    assert not is_universally_closed(augmented)
    if debug:
        print('Testing universal_closure_step on result...')
    augmented = universal_closure_step(augmented)
    assert len(augmented) == 13+10+10+10+10*10
    assert not is_universally_closed(augmented)
    if debug:
        print('Testing universal_closure_step on result...')
    augmented = universal_closure_step(augmented)
    assert len(augmented) == 13+10+10+10+10*10+10*10*10
    assert is_universally_closed(augmented)
    if debug:
        print('Testing universal_closure_step on result...')
    assert universal_closure_step(augmented) == augmented

    #if debug:
    #    print('Testing universally_close on associativity axiom with six '
    #          'elements...')
    #augmented = universal_closure_step(frozenset({ASSOCIATIVITY_AXIOM}.union(
    #    SENTENCES_WITH_SIX_ELEMENTS)))
    #assert {ASSOCIATIVITY_AXIOM}.union(SENTENCES_WITH_SIX_ELEMENTS).issubset(
    #    augmented)
    #assert len(augmented) == 7+6
    #assert not is_universally_closed(augmented)
    #if debug:
    #    print('Testing universal_closure_step on result...')
    #augmented = universal_closure_step(augmented)
    #assert len(augmented) == 7+6+6*6
    #assert not is_universally_closed(augmented)
    #if debug:
    #    print('Testing universal_closure_step on result...')
    #augmented = universal_closure_step(augmented)
    #assert len(augmented) == 7+6+6*6+6*6*6
    #assert not is_universally_closed(augmented)
    #if debug:
    #    print('Testing universal_closure_step on result...')
    #augmented = universal_closure_step(augmented)
    #assert len(augmented) == 7+6+6*6+6*6*6+6*6*6*6
    #assert not is_universally_closed(augmented)
    #if debug:
    #    print('Testing universal_closure_step on result...')
    #augmented = universal_closure_step(augmented)
    #assert len(augmented) == 7+6+6*6+6*6*6+6*6*6*6+6*6*6*6*6
    #assert not is_universally_closed(augmented)
    #if debug:
    #    print('Testing universal_closure_step on result...')
    #augmented = universal_closure_step(augmented)
    #assert len(augmented) == 7+6+6*6+6*6*6+6*6*6*6+6*6*6*6*6+6*6*6*6*6*6
    #assert is_universally_closed(augmented)
    #if debug:
    #    print('Testing universal_closure_step on result...')
    #assert universal_closure_step(augmented) == augmented

    if debug:
        print('Testing universal_closure_step on group axioms with six '
              'elements...')
    augmented = universal_closure_step(frozenset(
        {ZERO_AXIOM, NEGATION_AXIOM, ASSOCIATIVITY_AXIOM}.union(
            SENTENCES_WITH_SIX_ELEMENTS)))
    assert {ZERO_AXIOM, NEGATION_AXIOM, ASSOCIATIVITY_AXIOM}.union(
        SENTENCES_WITH_SIX_ELEMENTS).issubset(augmented)
    assert len(augmented) == 9+6+6+6
    assert not is_universally_closed(augmented)
    if debug:
        print('Testing universal_closure_step on result...')
    augmented = universal_closure_step(augmented)
    assert len(augmented) == 9+6+6+6+6*6
    assert not is_universally_closed(augmented)
    if debug:
        print('Testing universal_closure_step on result...')
    augmented = universal_closure_step(augmented)
    assert len(augmented) == 9+6+6+6+6*6+6*6*6
    assert not is_universally_closed(augmented)
    if debug:
        print('Testing universal_closure_step on result...')
    augmented = universal_closure_step(augmented)
    assert len(augmented) == 9+6+6+6+6*6+6*6*6+6*6*6*6
    assert not is_universally_closed(augmented)
    if debug:
        print('Testing universal_closure_step on result...')
    augmented = universal_closure_step(augmented)
    assert len(augmented) == 9+6+6+6+6*6+6*6*6+6*6*6*6+6*6*6*6*6
    assert not is_universally_closed(augmented)
    if debug:
        print('Testing universal_closure_step on result...')
    augmented = universal_closure_step(augmented)
    assert len(augmented) == 9+6+6+6+6*6+6*6*6+6*6*6*6+6*6*6*6*6+6*6*6*6*6*6
    assert is_universally_closed(augmented)
    if debug:
        print('Testing universal_closure_step on result...')
    assert universal_closure_step(augmented) == augmented
    for model in [SIX_ELEMENT_COMMUTATIVE_GROUP_MODEL,
                  SIX_ELEMENT_NONCOMMUTATIVE_GROUP_MODEL]:
        assert model.is_model_of(augmented)

def test_replace_constant(debug=False):
    from predicates.some_proofs import \
         syllogism_proof, syllogism_proof_with_universal_instantiation,\
         GROUP_AXIOMS, unique_zero_proof

    # Replace in assumptions formulas, constant instantiation maps, mp
    if debug:
        print('Testing replace_constant for replacing aristotle with z in '
              'syllogism proof')
    for proof in [syllogism_proof(),
                  syllogism_proof_with_universal_instantiation()]:
        replaced = replace_constant(proof, 'aristotle', 'z')
        assert replaced.assumptions == Prover.AXIOMS.union(
            {Schema(Formula.parse('Ax[(Man(x)->Mortal(x))]')),
             Schema(Formula.parse('Man(z)'))})
        assert str(replaced.conclusion) == 'Mortal(z)'
        if debug:
            print('Verifying returned proof (' +
                  '{:,}'.format(len(replaced.lines)),
                  'lines) of', replaced.conclusion)
        assert replaced.is_valid()

    # Replace in ug, tautology, relation instantiation maps
    proof = unique_zero_proof()
    if debug:
        print('Testing replace_constant for replacing a with zz in '
              'unique-zero proof')
    replaced = replace_constant(proof, 'a')
    assert replaced.assumptions == Prover.AXIOMS.union(
        {Schema(Formula.parse(a)) for a in GROUP_AXIOMS},
        {Schema(Formula.parse('plus(zz,c)=zz'))})
    assert str(replaced.conclusion) == 'c=0'
    if debug:
        print('Verifying returned proof (' +
              '{:,}'.format(len(replaced.lines)),
              'lines) of', replaced.conclusion)
    assert replaced.is_valid()

def test_eliminate_existential_witness_assumption(debug=False):
    assumptions = {Schema(Formula.parse('Ax[(R(x)->(Q(x)&~Q(x)))]')),
                   Schema(Formula.parse('Ex[R(x)]')),
                   Schema(Formula.parse('R(c17)'))}
    prover = Prover(assumptions)
    step1 = prover.add_assumption('R(c17)')
    step2 = prover.add_assumption('Ax[(R(x)->(Q(x)&~Q(x)))]')
    step3 = prover.add_universal_instantiation(
        '(R(c17)->(Q(c17)&~Q(c17)))', step2, 'c17')
    prover.add_tautological_implication('(Q(c17)&~Q(c17))', {step1, step3})
    proof = prover.qed()

    if (debug):
        print('Testing eliminate_existential_witness_assumption for the '
              'following proof:\n', proof)
    eliminated = eliminate_existential_witness_assumption(
        proof, 'c17', Formula.parse('R(c17)'), Formula.parse('Ex[R(x)]'))
    assert eliminated.assumptions == \
           Prover.AXIOMS.union(assumptions - {Schema(Formula.parse('R(c17)'))})
    assert is_tautology(
        Formula('~', eliminated.conclusion).propositional_skeleton()[0])
    if debug:
        print('Verifying returned proof (' +
              '{:,}'.format(len(eliminated.lines)),
              'lines) of', eliminated.conclusion)
    assert eliminated.is_valid()

def test_existential_closure_step(debug=False):
    from logic_utils import fresh_constant_name_generator
    fresh_constant_name_generator._reset_for_test()

    if debug:
        print('Testing existential_closure_step on negation axiom universal '
              'closure with six elements...')
    augmented = existential_closure_step(SIX_ELEMENT_NEGATION_CLOSURE)
    assert get_constants(augmented) == SIX_ELEMENTS.union(
        {'c1', 'c2', 'c3', 'c4', 'c5', 'c6'})
    assert len(augmented) == 12
    assert SIX_ELEMENT_NEGATION_CLOSURE.issubset(augmented)
    witnessed = set()
    witnessing_constants = []
    for sentence in augmented:
        if sentence.root == 'E':
            continue
        assert sentence.root == 'Plus'
        assert sentence.arguments[0] == Term('0')
        witnessed.add(sentence.arguments[2])
        witnessing_constants.append(sentence.arguments[1])
    assert witnessed == {Term(c) for c in SIX_ELEMENTS}
    assert set(witnessing_constants) == {Term(c) for c in
                                         {'c1', 'c2', 'c3', 'c4', 'c5', 'c6'}}
    assert is_existentially_closed(augmented)
    if debug:
        print('Testing existential_closure_step on result...')
    assert existential_closure_step(augmented) == augmented

    if debug:
        print('Testing existential_closure_step on noncommutativity axiom with '
              'six elements...')
    augmented1 = existential_closure_step(frozenset(
        {ZERO_AXIOM, NEGATION_AXIOM, ASSOCIATIVITY_AXIOM, NONCOMMUTATIVITY}))
    assert augmented1 == {ZERO_AXIOM, NEGATION_AXIOM, ASSOCIATIVITY_AXIOM,
                          NONCOMMUTATIVITY,
                          Formula.parse('Ey[Ez[(Plus(z,c7,y)&~Plus(z,y,c7))]]')}
    assert not is_existentially_closed(augmented1)
    if debug:
        print('Testing existential_closure_step on result...')
    augmented2 = existential_closure_step(augmented1)
    assert augmented2 == {ZERO_AXIOM, NEGATION_AXIOM, ASSOCIATIVITY_AXIOM,
                          NONCOMMUTATIVITY,
                          Formula.parse('Ey[Ez[(Plus(z,c7,y)&~Plus(z,y,c7))]]'),
                          Formula.parse('Ez[(Plus(z,c7,c8)&~Plus(z,c8,c7))]')}
    assert not is_existentially_closed(augmented2)
    if debug:
        print('Testing existential_closure_step on result...')
    augmented3 = existential_closure_step(augmented2)
    assert augmented3 == {ZERO_AXIOM, NEGATION_AXIOM, ASSOCIATIVITY_AXIOM,
                          NONCOMMUTATIVITY,
                          Formula.parse('Ey[Ez[(Plus(z,c7,y)&~Plus(z,y,c7))]]'),
                          Formula.parse('Ez[(Plus(z,c7,c8)&~Plus(z,c8,c7))]'),
                          Formula.parse('(Plus(c9,c7,c8)&~Plus(c9,c8,c7))')}
    assert is_existentially_closed(augmented3)
    if debug:
        print('Testing existential_closure_step on result...')
    assert existential_closure_step(augmented3) == augmented3

ZERO_AXIOM = Formula.parse('Ax[Plus(x,0,x)]')
NEGATION_AXIOM = Formula.parse('Ax[Ey[Plus(0,y,x)]]')
ASSOCIATIVITY_AXIOM = \
    Formula.parse('Ax[Ay[Az[Axy[Ayz[Axyz[((Plus(xy,x,y)&Plus(yz,y,z))->'
                  '((Plus(xyz,xy,z)->Plus(xyz,x,yz))&'
                  '(Plus(xyz,x,yz)->Plus(xyz,xy,z))))]]]]]]')
COMMUTATIVITY_AXIOM = Formula.parse('Ax[Ay[Az[(Plus(z,x,y)->Plus(z,y,x))]]]')
NONCOMMUTATIVITY = Formula.parse('Ex[Ey[Ez[(Plus(z,x,y)&~Plus(z,y,x))]]]')

SIX_ELEMENTS = frozenset({'0', '1', '2', '3', '4', '5'})
SENTENCES_WITH_SIX_ELEMENTS = frozenset({Formula.parse(s) for s in {
    'SAME(0,0)', 'SAME(1,1)', 'SAME(2,2)',
    'SAME(3,3)', 'SAME(4,4)', 'SAME(5,5)'}})
SIX_ELEMENT_ZERO_AXIOM_CLOSURE = frozenset({Formula.parse(s) for s in {
    'Plus(0,0,0)', 'Plus(1,0,1)', 'Plus(2,0,2)',
    'Plus(3,0,3)', 'Plus(4,0,4)', 'Plus(5,0,5)'}})
SIX_ELEMENT_NEGATION_CLOSURE = frozenset({Formula.parse(s) for s in {
    'Ey[Plus(0,y,0)]', 'Ey[Plus(0,y,1)]', 'Ey[Plus(0,y,2)]',
    'Ey[Plus(0,y,3)]', 'Ey[Plus(0,y,4)]', 'Ey[Plus(0,y,5)]'}})
SIX_ELEMENT_COMMUTATIVITY_CLOSURE1 = frozenset({Formula.parse(s) for s in {
    'Ay[Az[(Plus(z,0,y)->Plus(z,y,0))]]', 'Ay[Az[(Plus(z,1,y)->Plus(z,y,1))]]',
    'Ay[Az[(Plus(z,2,y)->Plus(z,y,2))]]', 'Ay[Az[(Plus(z,3,y)->Plus(z,y,3))]]',
    'Ay[Az[(Plus(z,4,y)->Plus(z,y,4))]]',
    'Ay[Az[(Plus(z,5,y)->Plus(z,y,5))]]'}})
SIX_ELEMENT_COMMUTATIVITY_CLOSURE2 = frozenset({Formula.parse(s) for s in {
    'Az[(Plus(z,0,0)->Plus(z,0,0))]', 'Az[(Plus(z,0,1)->Plus(z,1,0))]',
    'Az[(Plus(z,0,2)->Plus(z,2,0))]', 'Az[(Plus(z,0,3)->Plus(z,3,0))]',
    'Az[(Plus(z,0,4)->Plus(z,4,0))]', 'Az[(Plus(z,0,5)->Plus(z,5,0))]', 
    'Az[(Plus(z,1,0)->Plus(z,0,1))]', 'Az[(Plus(z,1,1)->Plus(z,1,1))]',
    'Az[(Plus(z,1,2)->Plus(z,2,1))]', 'Az[(Plus(z,1,3)->Plus(z,3,1))]',
    'Az[(Plus(z,1,4)->Plus(z,4,1))]', 'Az[(Plus(z,1,5)->Plus(z,5,1))]', 
    'Az[(Plus(z,2,0)->Plus(z,0,2))]', 'Az[(Plus(z,2,1)->Plus(z,1,2))]',
    'Az[(Plus(z,2,2)->Plus(z,2,2))]', 'Az[(Plus(z,2,3)->Plus(z,3,2))]',
    'Az[(Plus(z,2,4)->Plus(z,4,2))]', 'Az[(Plus(z,2,5)->Plus(z,5,2))]', 
    'Az[(Plus(z,3,0)->Plus(z,0,3))]', 'Az[(Plus(z,3,1)->Plus(z,1,3))]',
    'Az[(Plus(z,3,2)->Plus(z,2,3))]', 'Az[(Plus(z,3,3)->Plus(z,3,3))]',
    'Az[(Plus(z,3,4)->Plus(z,4,3))]', 'Az[(Plus(z,3,5)->Plus(z,5,3))]', 
    'Az[(Plus(z,4,0)->Plus(z,0,4))]', 'Az[(Plus(z,4,1)->Plus(z,1,4))]',
    'Az[(Plus(z,4,2)->Plus(z,2,4))]', 'Az[(Plus(z,4,3)->Plus(z,3,4))]',
    'Az[(Plus(z,4,4)->Plus(z,4,4))]', 'Az[(Plus(z,4,5)->Plus(z,5,4))]', 
    'Az[(Plus(z,5,0)->Plus(z,0,5))]', 'Az[(Plus(z,5,1)->Plus(z,1,5))]',
    'Az[(Plus(z,5,2)->Plus(z,2,5))]', 'Az[(Plus(z,5,3)->Plus(z,3,5))]',
    'Az[(Plus(z,5,4)->Plus(z,4,5))]', 'Az[(Plus(z,5,5)->Plus(z,5,5))]'}})
SIX_ELEMENT_COMMUTATIVITY_CLOSURE3 = frozenset({Formula.parse(s) for s in {
    '(Plus(0,0,0)->Plus(0,0,0))', '(Plus(1,0,0)->Plus(1,0,0))',
    '(Plus(2,0,0)->Plus(2,0,0))', '(Plus(3,0,0)->Plus(3,0,0))',
    '(Plus(4,0,0)->Plus(4,0,0))', '(Plus(5,0,0)->Plus(5,0,0))',
    '(Plus(0,0,1)->Plus(0,1,0))', '(Plus(1,0,1)->Plus(1,1,0))',
    '(Plus(2,0,1)->Plus(2,1,0))', '(Plus(3,0,1)->Plus(3,1,0))',
    '(Plus(4,0,1)->Plus(4,1,0))', '(Plus(5,0,1)->Plus(5,1,0))', 
    '(Plus(0,0,2)->Plus(0,2,0))', '(Plus(1,0,2)->Plus(1,2,0))',
    '(Plus(2,0,2)->Plus(2,2,0))', '(Plus(3,0,2)->Plus(3,2,0))',
    '(Plus(4,0,2)->Plus(4,2,0))', '(Plus(5,0,2)->Plus(5,2,0))', 
    '(Plus(0,0,3)->Plus(0,3,0))', '(Plus(1,0,3)->Plus(1,3,0))',
    '(Plus(2,0,3)->Plus(2,3,0))', '(Plus(3,0,3)->Plus(3,3,0))',
    '(Plus(4,0,3)->Plus(4,3,0))', '(Plus(5,0,3)->Plus(5,3,0))', 
    '(Plus(0,0,4)->Plus(0,4,0))', '(Plus(1,0,4)->Plus(1,4,0))',
    '(Plus(2,0,4)->Plus(2,4,0))', '(Plus(3,0,4)->Plus(3,4,0))',
    '(Plus(4,0,4)->Plus(4,4,0))', '(Plus(5,0,4)->Plus(5,4,0))', 
    '(Plus(0,0,5)->Plus(0,5,0))', '(Plus(1,0,5)->Plus(1,5,0))',
    '(Plus(2,0,5)->Plus(2,5,0))', '(Plus(3,0,5)->Plus(3,5,0))',
    '(Plus(4,0,5)->Plus(4,5,0))', '(Plus(5,0,5)->Plus(5,5,0))', 
    '(Plus(0,1,0)->Plus(0,0,1))', '(Plus(1,1,0)->Plus(1,0,1))',
    '(Plus(2,1,0)->Plus(2,0,1))', '(Plus(3,1,0)->Plus(3,0,1))',
    '(Plus(4,1,0)->Plus(4,0,1))', '(Plus(5,1,0)->Plus(5,0,1))', 
    '(Plus(0,1,1)->Plus(0,1,1))', '(Plus(1,1,1)->Plus(1,1,1))',
    '(Plus(2,1,1)->Plus(2,1,1))', '(Plus(3,1,1)->Plus(3,1,1))',
    '(Plus(4,1,1)->Plus(4,1,1))', '(Plus(5,1,1)->Plus(5,1,1))', 
    '(Plus(0,1,2)->Plus(0,2,1))', '(Plus(1,1,2)->Plus(1,2,1))',
    '(Plus(2,1,2)->Plus(2,2,1))', '(Plus(3,1,2)->Plus(3,2,1))',
    '(Plus(4,1,2)->Plus(4,2,1))', '(Plus(5,1,2)->Plus(5,2,1))', 
    '(Plus(0,1,3)->Plus(0,3,1))', '(Plus(1,1,3)->Plus(1,3,1))',
    '(Plus(2,1,3)->Plus(2,3,1))', '(Plus(3,1,3)->Plus(3,3,1))',
    '(Plus(4,1,3)->Plus(4,3,1))', '(Plus(5,1,3)->Plus(5,3,1))', 
    '(Plus(0,1,4)->Plus(0,4,1))', '(Plus(1,1,4)->Plus(1,4,1))',
    '(Plus(2,1,4)->Plus(2,4,1))', '(Plus(3,1,4)->Plus(3,4,1))',
    '(Plus(4,1,4)->Plus(4,4,1))', '(Plus(5,1,4)->Plus(5,4,1))', 
    '(Plus(0,1,5)->Plus(0,5,1))', '(Plus(1,1,5)->Plus(1,5,1))',
    '(Plus(2,1,5)->Plus(2,5,1))', '(Plus(3,1,5)->Plus(3,5,1))',
    '(Plus(4,1,5)->Plus(4,5,1))', '(Plus(5,1,5)->Plus(5,5,1))', 
    '(Plus(0,2,0)->Plus(0,0,2))', '(Plus(1,2,0)->Plus(1,0,2))',
    '(Plus(2,2,0)->Plus(2,0,2))', '(Plus(3,2,0)->Plus(3,0,2))',
    '(Plus(4,2,0)->Plus(4,0,2))', '(Plus(5,2,0)->Plus(5,0,2))', 
    '(Plus(0,2,1)->Plus(0,1,2))', '(Plus(1,2,1)->Plus(1,1,2))',
    '(Plus(2,2,1)->Plus(2,1,2))', '(Plus(3,2,1)->Plus(3,1,2))',
    '(Plus(4,2,1)->Plus(4,1,2))', '(Plus(5,2,1)->Plus(5,1,2))', 
    '(Plus(0,2,2)->Plus(0,2,2))', '(Plus(1,2,2)->Plus(1,2,2))',
    '(Plus(2,2,2)->Plus(2,2,2))', '(Plus(3,2,2)->Plus(3,2,2))',
    '(Plus(4,2,2)->Plus(4,2,2))', '(Plus(5,2,2)->Plus(5,2,2))', 
    '(Plus(0,2,3)->Plus(0,3,2))', '(Plus(1,2,3)->Plus(1,3,2))',
    '(Plus(2,2,3)->Plus(2,3,2))', '(Plus(3,2,3)->Plus(3,3,2))',
    '(Plus(4,2,3)->Plus(4,3,2))', '(Plus(5,2,3)->Plus(5,3,2))', 
    '(Plus(0,2,4)->Plus(0,4,2))', '(Plus(1,2,4)->Plus(1,4,2))',
    '(Plus(2,2,4)->Plus(2,4,2))', '(Plus(3,2,4)->Plus(3,4,2))',
    '(Plus(4,2,4)->Plus(4,4,2))', '(Plus(5,2,4)->Plus(5,4,2))', 
    '(Plus(0,2,5)->Plus(0,5,2))', '(Plus(1,2,5)->Plus(1,5,2))',
    '(Plus(2,2,5)->Plus(2,5,2))', '(Plus(3,2,5)->Plus(3,5,2))',
    '(Plus(4,2,5)->Plus(4,5,2))', '(Plus(5,2,5)->Plus(5,5,2))', 
    '(Plus(0,3,0)->Plus(0,0,3))', '(Plus(1,3,0)->Plus(1,0,3))',
    '(Plus(2,3,0)->Plus(2,0,3))', '(Plus(3,3,0)->Plus(3,0,3))',
    '(Plus(4,3,0)->Plus(4,0,3))', '(Plus(5,3,0)->Plus(5,0,3))', 
    '(Plus(0,3,1)->Plus(0,1,3))', '(Plus(1,3,1)->Plus(1,1,3))',
    '(Plus(2,3,1)->Plus(2,1,3))', '(Plus(3,3,1)->Plus(3,1,3))',
    '(Plus(4,3,1)->Plus(4,1,3))', '(Plus(5,3,1)->Plus(5,1,3))', 
    '(Plus(0,3,2)->Plus(0,2,3))', '(Plus(1,3,2)->Plus(1,2,3))',
    '(Plus(2,3,2)->Plus(2,2,3))', '(Plus(3,3,2)->Plus(3,2,3))',
    '(Plus(4,3,2)->Plus(4,2,3))', '(Plus(5,3,2)->Plus(5,2,3))', 
    '(Plus(0,3,3)->Plus(0,3,3))', '(Plus(1,3,3)->Plus(1,3,3))',
    '(Plus(2,3,3)->Plus(2,3,3))', '(Plus(3,3,3)->Plus(3,3,3))',
    '(Plus(4,3,3)->Plus(4,3,3))', '(Plus(5,3,3)->Plus(5,3,3))', 
    '(Plus(0,3,4)->Plus(0,4,3))', '(Plus(1,3,4)->Plus(1,4,3))',
    '(Plus(2,3,4)->Plus(2,4,3))', '(Plus(3,3,4)->Plus(3,4,3))',
    '(Plus(4,3,4)->Plus(4,4,3))', '(Plus(5,3,4)->Plus(5,4,3))', 
    '(Plus(0,3,5)->Plus(0,5,3))', '(Plus(1,3,5)->Plus(1,5,3))',
    '(Plus(2,3,5)->Plus(2,5,3))', '(Plus(3,3,5)->Plus(3,5,3))',
    '(Plus(4,3,5)->Plus(4,5,3))', '(Plus(5,3,5)->Plus(5,5,3))', 
    '(Plus(0,4,0)->Plus(0,0,4))', '(Plus(1,4,0)->Plus(1,0,4))',
    '(Plus(2,4,0)->Plus(2,0,4))', '(Plus(3,4,0)->Plus(3,0,4))',
    '(Plus(4,4,0)->Plus(4,0,4))', '(Plus(5,4,0)->Plus(5,0,4))', 
    '(Plus(0,4,1)->Plus(0,1,4))', '(Plus(1,4,1)->Plus(1,1,4))',
    '(Plus(2,4,1)->Plus(2,1,4))', '(Plus(3,4,1)->Plus(3,1,4))',
    '(Plus(4,4,1)->Plus(4,1,4))', '(Plus(5,4,1)->Plus(5,1,4))', 
    '(Plus(0,4,2)->Plus(0,2,4))', '(Plus(1,4,2)->Plus(1,2,4))',
    '(Plus(2,4,2)->Plus(2,2,4))', '(Plus(3,4,2)->Plus(3,2,4))',
    '(Plus(4,4,2)->Plus(4,2,4))', '(Plus(5,4,2)->Plus(5,2,4))', 
    '(Plus(0,4,3)->Plus(0,3,4))', '(Plus(1,4,3)->Plus(1,3,4))',
    '(Plus(2,4,3)->Plus(2,3,4))', '(Plus(3,4,3)->Plus(3,3,4))',
    '(Plus(4,4,3)->Plus(4,3,4))', '(Plus(5,4,3)->Plus(5,3,4))', 
    '(Plus(0,4,4)->Plus(0,4,4))', '(Plus(1,4,4)->Plus(1,4,4))',
    '(Plus(2,4,4)->Plus(2,4,4))', '(Plus(3,4,4)->Plus(3,4,4))',
    '(Plus(4,4,4)->Plus(4,4,4))', '(Plus(5,4,4)->Plus(5,4,4))', 
    '(Plus(0,4,5)->Plus(0,5,4))', '(Plus(1,4,5)->Plus(1,5,4))',
    '(Plus(2,4,5)->Plus(2,5,4))', '(Plus(3,4,5)->Plus(3,5,4))',
    '(Plus(4,4,5)->Plus(4,5,4))', '(Plus(5,4,5)->Plus(5,5,4))', 
    '(Plus(0,5,0)->Plus(0,0,5))', '(Plus(1,5,0)->Plus(1,0,5))',
    '(Plus(2,5,0)->Plus(2,0,5))', '(Plus(3,5,0)->Plus(3,0,5))',
    '(Plus(4,5,0)->Plus(4,0,5))', '(Plus(5,5,0)->Plus(5,0,5))', 
    '(Plus(0,5,1)->Plus(0,1,5))', '(Plus(1,5,1)->Plus(1,1,5))',
    '(Plus(2,5,1)->Plus(2,1,5))', '(Plus(3,5,1)->Plus(3,1,5))',
    '(Plus(4,5,1)->Plus(4,1,5))', '(Plus(5,5,1)->Plus(5,1,5))', 
    '(Plus(0,5,2)->Plus(0,2,5))', '(Plus(1,5,2)->Plus(1,2,5))',
    '(Plus(2,5,2)->Plus(2,2,5))', '(Plus(3,5,2)->Plus(3,2,5))',
    '(Plus(4,5,2)->Plus(4,2,5))', '(Plus(5,5,2)->Plus(5,2,5))', 
    '(Plus(0,5,3)->Plus(0,3,5))', '(Plus(1,5,3)->Plus(1,3,5))',
    '(Plus(2,5,3)->Plus(2,3,5))', '(Plus(3,5,3)->Plus(3,3,5))',
    '(Plus(4,5,3)->Plus(4,3,5))', '(Plus(5,5,3)->Plus(5,3,5))', 
    '(Plus(0,5,4)->Plus(0,4,5))', '(Plus(1,5,4)->Plus(1,4,5))',
    '(Plus(2,5,4)->Plus(2,4,5))', '(Plus(3,5,4)->Plus(3,4,5))',
    '(Plus(4,5,4)->Plus(4,4,5))', '(Plus(5,5,4)->Plus(5,4,5))', 
    '(Plus(0,5,5)->Plus(0,5,5))', '(Plus(1,5,5)->Plus(1,5,5))',
    '(Plus(2,5,5)->Plus(2,5,5))', '(Plus(3,5,5)->Plus(3,5,5))',
    '(Plus(4,5,5)->Plus(4,5,5))', '(Plus(5,5,5)->Plus(5,5,5))'}})
SIX_ELEMENT_COMMUTATIVITY_CLOSURE = SIX_ELEMENT_COMMUTATIVITY_CLOSURE1.union(
    SIX_ELEMENT_COMMUTATIVITY_CLOSURE2, SIX_ELEMENT_COMMUTATIVITY_CLOSURE3)

SIX_ELEMENT_COMMUTATIVE_GROUP_PRIMITIVES = frozenset({
    Formula.parse(s) for s in {
        'Plus(0,0,0)', '~Plus(1,0,0)', '~Plus(2,0,0)',
        '~Plus(3,0,0)', '~Plus(4,0,0)', '~Plus(5,0,0)',
        '~Plus(0,0,1)', 'Plus(1,0,1)', '~Plus(2,0,1)',
        '~Plus(3,0,1)', '~Plus(4,0,1)', '~Plus(5,0,1)',
        '~Plus(0,0,2)', '~Plus(1,0,2)', 'Plus(2,0,2)',
        '~Plus(3,0,2)', '~Plus(4,0,2)', '~Plus(5,0,2)',
        '~Plus(0,0,3)', '~Plus(1,0,3)', '~Plus(2,0,3)',
        'Plus(3,0,3)', '~Plus(4,0,3)', '~Plus(5,0,3)',
        '~Plus(0,0,4)', '~Plus(1,0,4)', '~Plus(2,0,4)',
        '~Plus(3,0,4)', 'Plus(4,0,4)', '~Plus(5,0,4)',
        '~Plus(0,0,5)', '~Plus(1,0,5)', '~Plus(2,0,5)',
        '~Plus(3,0,5)', '~Plus(4,0,5)', 'Plus(5,0,5)',
        '~Plus(0,1,0)', 'Plus(1,1,0)', '~Plus(2,1,0)',
        '~Plus(3,1,0)', '~Plus(4,1,0)', '~Plus(5,1,0)',
        '~Plus(0,1,1)', '~Plus(1,1,1)', 'Plus(2,1,1)',
        '~Plus(3,1,1)', '~Plus(4,1,1)', '~Plus(5,1,1)',
        '~Plus(0,1,2)', '~Plus(1,1,2)', '~Plus(2,1,2)',
        'Plus(3,1,2)', '~Plus(4,1,2)', '~Plus(5,1,2)',
        '~Plus(0,1,3)', '~Plus(1,1,3)', '~Plus(2,1,3)',
        '~Plus(3,1,3)', 'Plus(4,1,3)', '~Plus(5,1,3)',
        '~Plus(0,1,4)', '~Plus(1,1,4)', '~Plus(2,1,4)',
        '~Plus(3,1,4)', '~Plus(4,1,4)', 'Plus(5,1,4)',
        'Plus(0,1,5)', '~Plus(1,1,5)', '~Plus(2,1,5)',
        '~Plus(3,1,5)', '~Plus(4,1,5)', '~Plus(5,1,5)',
        '~Plus(0,2,0)', '~Plus(1,2,0)', 'Plus(2,2,0)',
        '~Plus(3,2,0)', '~Plus(4,2,0)', '~Plus(5,2,0)',
        '~Plus(0,2,1)', '~Plus(1,2,1)', '~Plus(2,2,1)',
        'Plus(3,2,1)', '~Plus(4,2,1)', '~Plus(5,2,1)',
        '~Plus(0,2,2)', '~Plus(1,2,2)', '~Plus(2,2,2)',
        '~Plus(3,2,2)', 'Plus(4,2,2)', '~Plus(5,2,2)',
        '~Plus(0,2,3)', '~Plus(1,2,3)', '~Plus(2,2,3)',
        '~Plus(3,2,3)', '~Plus(4,2,3)', 'Plus(5,2,3)',
        'Plus(0,2,4)', '~Plus(1,2,4)', '~Plus(2,2,4)',
        '~Plus(3,2,4)', '~Plus(4,2,4)', '~Plus(5,2,4)',
        '~Plus(0,2,5)', 'Plus(1,2,5)', '~Plus(2,2,5)',
        '~Plus(3,2,5)', '~Plus(4,2,5)', '~Plus(5,2,5)',
        '~Plus(0,3,0)', '~Plus(1,3,0)', '~Plus(2,3,0)',
        'Plus(3,3,0)', '~Plus(4,3,0)', '~Plus(5,3,0)',
        '~Plus(0,3,1)', '~Plus(1,3,1)', '~Plus(2,3,1)',
        '~Plus(3,3,1)', 'Plus(4,3,1)', '~Plus(5,3,1)',
        '~Plus(0,3,2)', '~Plus(1,3,2)', '~Plus(2,3,2)',
        '~Plus(3,3,2)', '~Plus(4,3,2)', 'Plus(5,3,2)',
        'Plus(0,3,3)', '~Plus(1,3,3)', '~Plus(2,3,3)',
        '~Plus(3,3,3)', '~Plus(4,3,3)', '~Plus(5,3,3)',
        '~Plus(0,3,4)', 'Plus(1,3,4)', '~Plus(2,3,4)',
        '~Plus(3,3,4)', '~Plus(4,3,4)', '~Plus(5,3,4)',
        '~Plus(0,3,5)', '~Plus(1,3,5)', 'Plus(2,3,5)',
        '~Plus(3,3,5)', '~Plus(4,3,5)', '~Plus(5,3,5)',
        '~Plus(0,4,0)', '~Plus(1,4,0)', '~Plus(2,4,0)',
        '~Plus(3,4,0)', 'Plus(4,4,0)', '~Plus(5,4,0)',
        '~Plus(0,4,1)', '~Plus(1,4,1)', '~Plus(2,4,1)',
        '~Plus(3,4,1)', '~Plus(4,4,1)', 'Plus(5,4,1)',
        'Plus(0,4,2)', '~Plus(1,4,2)', '~Plus(2,4,2)',
        '~Plus(3,4,2)', '~Plus(4,4,2)', '~Plus(5,4,2)',
        '~Plus(0,4,3)', 'Plus(1,4,3)', '~Plus(2,4,3)',
        '~Plus(3,4,3)', '~Plus(4,4,3)', '~Plus(5,4,3)',
        '~Plus(0,4,4)', '~Plus(1,4,4)', 'Plus(2,4,4)',
        '~Plus(3,4,4)', '~Plus(4,4,4)', '~Plus(5,4,4)',
        '~Plus(0,4,5)', '~Plus(1,4,5)', '~Plus(2,4,5)',
        'Plus(3,4,5)', '~Plus(4,4,5)', '~Plus(5,4,5)',
        '~Plus(0,5,0)', '~Plus(1,5,0)', '~Plus(2,5,0)',
        '~Plus(3,5,0)', '~Plus(4,5,0)', 'Plus(5,5,0)',
        'Plus(0,5,1)', '~Plus(1,5,1)', '~Plus(2,5,1)',
        '~Plus(3,5,1)', '~Plus(4,5,1)', '~Plus(5,5,1)',
        '~Plus(0,5,2)', 'Plus(1,5,2)', '~Plus(2,5,2)',
        '~Plus(3,5,2)', '~Plus(4,5,2)', '~Plus(5,5,2)',
        '~Plus(0,5,3)', '~Plus(1,5,3)', 'Plus(2,5,3)',
        '~Plus(3,5,3)', '~Plus(4,5,3)', '~Plus(5,5,3)',
        '~Plus(0,5,4)', '~Plus(1,5,4)', '~Plus(2,5,4)',
        'Plus(3,5,4)', '~Plus(4,5,4)', '~Plus(5,5,4)',
        '~Plus(0,5,5)', '~Plus(1,5,5)', '~Plus(2,5,5)',
        '~Plus(3,5,5)', 'Plus(4,5,5)', '~Plus(5,5,5)'}})

SIX_ELEMENT_COMMUTATIVE_GROUP_MODEL = Model(
    SIX_ELEMENTS,
    {'0':'0', '1':'1', '2':'2', '3':'3', '4':'4', '5':'5'},
    {'SAME': {('0','0'), ('1','1'), ('2','2'), ('3','3'), ('4','4'), ('5','5')},
     'Plus': {('0','0','0'), ('1','0','1'), ('2','0','2'),
              ('3','0','3'), ('4','0','4'), ('5','0','5'), 
              ('1','1','0'), ('2','1','1'), ('3','1','2'),
              ('4','1','3'), ('5','1','4'), ('0','1','5'), 
              ('2','2','0'), ('3','2','1'), ('4','2','2'),
              ('5','2','3'), ('0','2','4'), ('1','2','5'), 
              ('3','3','0'), ('4','3','1'), ('5','3','2'),
              ('0','3','3'), ('1','3','4'), ('2','3','5'), 
              ('4','4','0'), ('5','4','1'), ('0','4','2'),
              ('1','4','3'), ('2','4','4'), ('3','4','5'), 
              ('5','5','0'), ('0','5','1'), ('1','5','2'),
              ('2','5','3'), ('3','5','4'), ('4','5','5')}})

SIX_ELEMENT_NONCOMMUTATIVE_GROUP_PRIMITIVES = frozenset({
    Formula.parse(s) for s in {
        'Plus(0,0,0)', '~Plus(1,0,0)', '~Plus(2,0,0)',
        '~Plus(3,0,0)', '~Plus(4,0,0)', '~Plus(5,0,0)', 
        '~Plus(0,0,1)', 'Plus(1,0,1)', '~Plus(2,0,1)',
        '~Plus(3,0,1)', '~Plus(4,0,1)', '~Plus(5,0,1)', 
        '~Plus(0,0,2)', '~Plus(1,0,2)', 'Plus(2,0,2)',
        '~Plus(3,0,2)', '~Plus(4,0,2)', '~Plus(5,0,2)', 
        '~Plus(0,0,3)', '~Plus(1,0,3)', '~Plus(2,0,3)',
        'Plus(3,0,3)', '~Plus(4,0,3)', '~Plus(5,0,3)', 
        '~Plus(0,0,4)', '~Plus(1,0,4)', '~Plus(2,0,4)',
        '~Plus(3,0,4)', 'Plus(4,0,4)', '~Plus(5,0,4)', 
        '~Plus(0,0,5)', '~Plus(1,0,5)', '~Plus(2,0,5)',
        '~Plus(3,0,5)', '~Plus(4,0,5)', 'Plus(5,0,5)', 
        '~Plus(0,1,0)', 'Plus(1,1,0)', '~Plus(2,1,0)',
        '~Plus(3,1,0)', '~Plus(4,1,0)', '~Plus(5,1,0)', 
        'Plus(0,1,1)', '~Plus(1,1,1)', '~Plus(2,1,1)',
        '~Plus(3,1,1)', '~Plus(4,1,1)', '~Plus(5,1,1)', 
        '~Plus(0,1,2)', '~Plus(1,1,2)', '~Plus(2,1,2)',
        '~Plus(3,1,2)', '~Plus(4,1,2)', 'Plus(5,1,2)', 
        '~Plus(0,1,3)', '~Plus(1,1,3)', '~Plus(2,1,3)',
        '~Plus(3,1,3)', 'Plus(4,1,3)', '~Plus(5,1,3)', 
        '~Plus(0,1,4)', '~Plus(1,1,4)', '~Plus(2,1,4)',
        'Plus(3,1,4)', '~Plus(4,1,4)', '~Plus(5,1,4)', 
        '~Plus(0,1,5)', '~Plus(1,1,5)', 'Plus(2,1,5)',
        '~Plus(3,1,5)', '~Plus(4,1,5)', '~Plus(5,1,5)', 
        '~Plus(0,2,0)', '~Plus(1,2,0)', 'Plus(2,2,0)',
        '~Plus(3,2,0)', '~Plus(4,2,0)', '~Plus(5,2,0)', 
        '~Plus(0,2,1)', '~Plus(1,2,1)', '~Plus(2,2,1)',
        '~Plus(3,2,1)', 'Plus(4,2,1)', '~Plus(5,2,1)', 
        'Plus(0,2,2)', '~Plus(1,2,2)', '~Plus(2,2,2)',
        '~Plus(3,2,2)', '~Plus(4,2,2)', '~Plus(5,2,2)', 
        '~Plus(0,2,3)', '~Plus(1,2,3)', '~Plus(2,2,3)',
        '~Plus(3,2,3)', '~Plus(4,2,3)', 'Plus(5,2,3)', 
        '~Plus(0,2,4)', 'Plus(1,2,4)', '~Plus(2,2,4)',
        '~Plus(3,2,4)', '~Plus(4,2,4)', '~Plus(5,2,4)', 
        '~Plus(0,2,5)', '~Plus(1,2,5)', '~Plus(2,2,5)',
        'Plus(3,2,5)', '~Plus(4,2,5)', '~Plus(5,2,5)', 
        '~Plus(0,3,0)', '~Plus(1,3,0)', '~Plus(2,3,0)',
        'Plus(3,3,0)', '~Plus(4,3,0)', '~Plus(5,3,0)', 
        '~Plus(0,3,1)', '~Plus(1,3,1)', '~Plus(2,3,1)',
        '~Plus(3,3,1)', '~Plus(4,3,1)', 'Plus(5,3,1)', 
        '~Plus(0,3,2)', '~Plus(1,3,2)', '~Plus(2,3,2)',
        '~Plus(3,3,2)', 'Plus(4,3,2)', '~Plus(5,3,2)', 
        'Plus(0,3,3)', '~Plus(1,3,3)', '~Plus(2,3,3)',
        '~Plus(3,3,3)', '~Plus(4,3,3)', '~Plus(5,3,3)', 
        '~Plus(0,3,4)', '~Plus(1,3,4)', 'Plus(2,3,4)',
        '~Plus(3,3,4)', '~Plus(4,3,4)', '~Plus(5,3,4)', 
        '~Plus(0,3,5)', 'Plus(1,3,5)', '~Plus(2,3,5)',
        '~Plus(3,3,5)', '~Plus(4,3,5)', '~Plus(5,3,5)', 
        '~Plus(0,4,0)', '~Plus(1,4,0)', '~Plus(2,4,0)',
        '~Plus(3,4,0)', 'Plus(4,4,0)', '~Plus(5,4,0)', 
        '~Plus(0,4,1)', '~Plus(1,4,1)', 'Plus(2,4,1)',
        '~Plus(3,4,1)', '~Plus(4,4,1)', '~Plus(5,4,1)', 
        '~Plus(0,4,2)', '~Plus(1,4,2)', '~Plus(2,4,2)',
        'Plus(3,4,2)', '~Plus(4,4,2)', '~Plus(5,4,2)', 
        '~Plus(0,4,3)', 'Plus(1,4,3)', '~Plus(2,4,3)',
        '~Plus(3,4,3)', '~Plus(4,4,3)', '~Plus(5,4,3)', 
        '~Plus(0,4,4)', '~Plus(1,4,4)', '~Plus(2,4,4)',
        '~Plus(3,4,4)', '~Plus(4,4,4)', 'Plus(5,4,4)', 
        'Plus(0,4,5)', '~Plus(1,4,5)', '~Plus(2,4,5)',
        '~Plus(3,4,5)', '~Plus(4,4,5)', '~Plus(5,4,5)', 
        '~Plus(0,5,0)', '~Plus(1,5,0)', '~Plus(2,5,0)',
        '~Plus(3,5,0)', '~Plus(4,5,0)', 'Plus(5,5,0)', 
        '~Plus(0,5,1)', '~Plus(1,5,1)', '~Plus(2,5,1)',
        'Plus(3,5,1)', '~Plus(4,5,1)', '~Plus(5,5,1)', 
        '~Plus(0,5,2)', 'Plus(1,5,2)', '~Plus(2,5,2)',
        '~Plus(3,5,2)', '~Plus(4,5,2)', '~Plus(5,5,2)', 
        '~Plus(0,5,3)', '~Plus(1,5,3)', 'Plus(2,5,3)',
        '~Plus(3,5,3)', '~Plus(4,5,3)', '~Plus(5,5,3)', 
        'Plus(0,5,4)', '~Plus(1,5,4)', '~Plus(2,5,4)',
        '~Plus(3,5,4)', '~Plus(4,5,4)', '~Plus(5,5,4)', 
        '~Plus(0,5,5)', '~Plus(1,5,5)', '~Plus(2,5,5)',
        '~Plus(3,5,5)', 'Plus(4,5,5)', '~Plus(5,5,5)'}})

SIX_ELEMENT_NONCOMMUTATIVE_GROUP_NONCOMMUTATIVITY_CLOSURE = frozenset({
    Formula.parse(s) for s in {
        'Ey[Ez[(Plus(z,1,y)&~Plus(z,y,1))]]',
        'Ez[(Plus(z,1,2)&~Plus(z,2,1))]',
        '(Plus(5,1,2)&~Plus(5,2,1))'}})

SIX_ELEMENT_NONCOMMUTATIVE_GROUP_MODEL = Model(
    SIX_ELEMENTS,
    {'0':'0', '1':'1', '2':'2', '3':'3', '4':'4', '5':'5'},
    {'SAME': {('0','0'), ('1','1'), ('2','2'), ('3','3'), ('4','4'), ('5','5')},
     'Plus': {('0','0','0'), ('1','0','1'), ('2','0','2'),
              ('3','0','3'), ('4','0','4'), ('5','0','5'), 
              ('1','1','0'), ('0','1','1'), ('5','1','2'),
              ('4','1','3'), ('3','1','4'), ('2','1','5'), 
              ('2','2','0'), ('4','2','1'), ('0','2','2'),
              ('5','2','3'), ('1','2','4'), ('3','2','5'), 
              ('3','3','0'), ('5','3','1'), ('4','3','2'),
              ('0','3','3'), ('2','3','4'), ('1','3','5'), 
              ('4','4','0'), ('2','4','1'), ('3','4','2'),
              ('1','4','3'), ('5','4','4'), ('0','4','5'), 
              ('5','5','0'), ('3','5','1'), ('1','5','2'),
              ('2','5','3'), ('0','5','4'), ('4','5','5')}})

def test_ex12(debug=False):
    test_is_primitively_closed(debug)
    test_is_universally_closed(debug)
    test_is_existentially_closed(debug)
    test_find_unsatisfied_quantifier_free_sentence(debug)
    test_model_or_inconsistency(debug)
    test_combine_contradictions(debug)
    test_eliminate_universal_instantiation_assumption(debug)
    test_universal_closure_step(debug)
    test_replace_constant(debug)
    test_eliminate_existential_witness_assumption(debug)
    test_existential_closure_step(debug)

def test_all(debug=False):
    test_ex12(debug)
