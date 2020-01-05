# (c) This file is part of the course
# Mathematical Logic through Programming
# by Gonczarowski and Nisan.
# File name: predicates/some_proofs.py

from predicates.syntax import *
from predicates.proofs import *
from predicates.prover import *
# from predicates.deduction import *
# from predicates.prenex import equivalence_of

def syllogism_proof(print_as_proof_forms: bool = False) -> Proof:
    """Proves from the assumptions:

    1. All men are mortal (``'Ax[(Man(x)->Mortal(x))]'``), and
    2. Aristotle is a man (``'Man(aristotle)'``)

    the conclusion: Aristotle is mortal (``'Mortal(aristotle)'``).

    Parameters:
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being constructed.

    Returns:
        A valid proof of the above inference via
        `~predicates.prover.Prover.AXIOMS`.
    """
    prover = Prover({'Ax[(Man(x)->Mortal(x))]', 'Man(aristotle)'},
                    print_as_proof_forms)
    step1 = prover.add_assumption('Ax[(Man(x)->Mortal(x))]')
    step2 = prover.add_instantiated_assumption(
        '(Ax[(Man(x)->Mortal(x))]->(Man(aristotle)->Mortal(aristotle)))',
        Prover.UI, {'R': '(Man(_)->Mortal(_))', 'c': 'aristotle'})
    step3 = prover.add_mp('(Man(aristotle)->Mortal(aristotle))', step1, step2)
    step4 = prover.add_assumption('Man(aristotle)')
    step5 = prover.add_mp('Mortal(aristotle)', step4, step3)
    return prover.qed()

def syllogism_proof_with_universal_instantiation(print_as_proof_forms: bool =
                                                 False) -> Proof:
    """Using the method `~predicates.prover.Prover.add_universal_instantiation`,
    proves from the assumptions:

    1. All men are mortal (``'Ax[(Man(x)->Mortal(x))]'``), and
    2. Aristotle is a man (``'Man(aristotle)'``)

    the conclusion: Aristotle is mortal (``'Mortal(aristotle)'``).

    Parameters:
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being constructed.

    Returns:
        A valid proof, constructed using the method
        `~predicates.prover.Prover.add_universal_instantiation`, of the above
        inference via `~predicates.prover.Prover.AXIOMS`.
    """
    prover = Prover({'Ax[(Man(x)->Mortal(x))]', 'Man(aristotle)'},
                    print_as_proof_forms)
    step1 = prover.add_assumption('Ax[(Man(x)->Mortal(x))]')
    step2 = prover.add_universal_instantiation(
        '(Man(aristotle)->Mortal(aristotle))', step1, 'aristotle')
    step3 = prover.add_assumption('Man(aristotle)')
    step4 = prover.add_mp('Mortal(aristotle)', step3, step2)
    return prover.qed()

def syllogism_all_all_proof(print_as_proof_forms: bool = False) -> Proof:
    """Proves from the assumptions:

    1. All Greeks are human (``'Ax[(Greek(x)->Human(x))]'``), and
    2. All humans are mortal (``'Ax[(Human(x)->Mortal(x))]'``)

    the conclusion: All Greeks are mortal (``'Ax[(Greek(x)->Mortal(x))]'``).

    Parameters:
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being constructed.

    Returns:
        A valid proof of the above inference via
        `~predicates.prover.Prover.AXIOMS`.
    """
    prover = Prover({'Ax[(Greek(x)->Human(x))]', 'Ax[(Human(x)->Mortal(x))]'},
                    print_as_proof_forms)
    step1 = prover.add_assumption('Ax[(Greek(x)->Human(x))]')
    step2 = prover.add_universal_instantiation(
        '(Greek(x)->Human(x))', step1, 'x')
    step3 = prover.add_assumption('Ax[(Human(x)->Mortal(x))]')
    step4 = prover.add_universal_instantiation(
        '(Human(x)->Mortal(x))', step3, 'x')
    step5 = prover.add_tautology(
        '((Greek(x)->Human(x))->((Human(x)->Mortal(x))->(Greek(x)->Mortal(x))))')
    step6 = prover.add_mp(
        '((Human(x)->Mortal(x))->(Greek(x)->Mortal(x)))', step2, step5)
    step7 = prover.add_mp('(Greek(x)->Mortal(x))', step4, step6)
    step8 = prover.add_ug('Ax[(Greek(x)->Mortal(x))]', step7)
    return prover.qed()

def syllogism_all_all_proof_with_tautological_implication(print_as_proof_forms:
                                                          bool = False) -> \
        Proof:
    """Using the method
    `~predicates.prover.Prover.add_tautological_implication`, proves from the
    assumptions:

    1. All Greeks are human (``'Ax[(Greek(x)->Human(x))]'``), and
    2. All humans are mortal (``'Ax[(Human(x)->Mortal(x))]'``)

    the conclusion: All Greeks are mortal (``'Ax[(Greek(x)->Mortal(x))]'``).

    Parameters:
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being constructed.

    Returns:
        A valid proof, constructed using the method
        `~predicates.prover.Prover.add_tautological_implication`, of the above
        inference via `~predicates.prover.Prover.AXIOMS`.
    """
    prover = Prover({'Ax[(Greek(x)->Human(x))]', 'Ax[(Human(x)->Mortal(x))]'},
                    print_as_proof_forms)
    step1 = prover.add_assumption('Ax[(Greek(x)->Human(x))]')
    step2 = prover.add_universal_instantiation(
        '(Greek(x)->Human(x))', step1, 'x')
    step3 = prover.add_assumption('Ax[(Human(x)->Mortal(x))]')
    step4 = prover.add_universal_instantiation(
        '(Human(x)->Mortal(x))', step3, 'x')
    step5 = prover.add_tautological_implication(
        '(Greek(x)->Mortal(x))', {step2, step4})
    step6 = prover.add_ug('Ax[(Greek(x)->Mortal(x))]', step5)
    return prover.qed()

def syllogism_all_exists_proof(print_as_proof_forms: bool = False) -> Proof:
    """Proves from the assumptions:

    1. All men are mortal (``'Ax[(Man(x)->Mortal(x))]'``), and
    2. Some men exist (``'Ex[Man(x)]'``)
    
    the conclusion: Some mortals exist (``'Ex[Mortal(x)]'``).

    Parameters:
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being constructed.

    Returns:
        A valid proof of the above inference via
        `~predicates.prover.Prover.AXIOMS`.
    """
    prover = Prover({'Ax[(Man(x)->Mortal(x))]', 'Ex[Man(x)]'},
                    print_as_proof_forms)
    step1 = prover.add_assumption('Ax[(Man(x)->Mortal(x))]')
    step2 = prover.add_assumption('Ex[Man(x)]')
    step3 = prover.add_universal_instantiation(
        '(Man(x)->Mortal(x))', step1, 'x')
    step4 = prover.add_instantiated_assumption(
        '(Mortal(x)->Ex[Mortal(x)])', Prover.EI,
        {'R': 'Mortal(_)', 'c': 'x'})
    step5 = prover.add_tautological_implication(
        '(Man(x)->Ex[Mortal(x)])', {step3, step4})
    step6 = prover.add_ug('Ax[(Man(x)->Ex[Mortal(x)])]', step5)
    step7 = prover.add_instantiated_assumption(
        '((Ax[(Man(x)->Ex[Mortal(x)])]&Ex[Man(x)])->Ex[Mortal(x)])', Prover.ES,
        {'R': 'Man(_)', 'Q': 'Ex[Mortal(x)]'})
    step8 = prover.add_tautological_implication(
        'Ex[Mortal(x)]', {step2, step6, step7})
    return prover.qed()

def syllogism_all_exists_proof_with_existential_derivation(print_as_proof_forms:
                                                           bool = False) -> \
        Proof:
    """Using the method `~predicates.prover.Prover.add_existential_derivation`,
    proves from the assumptions:

    1. All men are mortal (``'Ax[(Man(x)->Mortal(x))]'``), and
    2. Some men exist (``'Ex[Man(x)]'``)
    
    the conclusion: Some mortals exist (``'Ex[Mortal(x)]'``).

    Parameters:
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being constructed.

    Returns:
        A valid proof, constructed using the method
        `~predicates.prover.Prover.add_existential_derivation`, of the above
        inference via `~predicates.prover.Prover.AXIOMS`.
    """
    prover = Prover({'Ax[(Man(x)->Mortal(x))]', 'Ex[Man(x)]'},
                    print_as_proof_forms)
    step1 = prover.add_assumption('Ax[(Man(x)->Mortal(x))]')
    step2 = prover.add_assumption('Ex[Man(x)]')
    step3 = prover.add_universal_instantiation(
        '(Man(x)->Mortal(x))', step1, 'x')
    step4 = prover.add_instantiated_assumption(
        '(Mortal(x)->Ex[Mortal(x)])', Prover.EI, {'R': 'Mortal(_)', 'c': 'x'})
    step5 = prover.add_tautological_implication(
        '(Man(x)->Ex[Mortal(x)])', {step3, step4})
    step6 = prover.add_existential_derivation('Ex[Mortal(x)]', step2, step5)
    return prover.qed()

def lovers_proof(print_as_proof_forms: bool = False) -> Proof:
    """Proves from the assumptions:

    1. Everybody loves somebody (``'Ax[Ey[Loves(x,y)]]'``), and
    2. Everybody loves a lover (``'Ax[Az[Ay[(Loves(x,y)->Loves(z,x))]]]'``)
    
    the conclusion: Everybody loves everybody (``'Ax[Az[Loves(z,x)]]'``).

    Parameters:
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being constructed.

    Returns:
        A valid proof of the above inference via
        `~predicates.prover.Prover.AXIOMS`.
    """
    prover = Prover({'Ax[Ey[Loves(x,y)]]',
                     'Ax[Az[Ay[(Loves(x,y)->Loves(z,x))]]]'},
                    print_as_proof_forms)
    # Task 10.4
    first_assump = prover.add_assumption('Ax[Ey[Loves(x,y)]]')
    second_assump = prover.add_assumption('Ax[Az[Ay[(Loves(x,y)->Loves(z,x))]]]')
    step_1 = prover.add_universal_instantiation('[Ey[Loves(x,y)]', first_assump, 'x')
    step_2 = prover.add_universal_instantiation('Az[Ay[(Loves(x,y)->Loves(z,x))]]', second_assump, 'x')
    step_3 = prover.add_universal_instantiation('Ay[(Loves(x,y)->Loves(z,x))]', step_2, 'x')
    step_4 = prover.add_existential_derivation('Loves(z,x)', )


    return prover.qed()

def homework_proof(print_as_proof_forms: bool = False) -> Proof:
    """Proves from the assumptions:

    1. No homework is fun (``'~Ex[(Homework(x)&Fun(x))]'``), and
    2. Some reading is homework (``'Ex[(Homework(x)&Reading(x))]'``)
    
    the conclusion: Some reading is not fun (``'Ex[(Reading(x)&~Fun(x))]'``).

    Parameters:
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being constructed.

    Returns:
        A valid proof of the above inference via
        `~predicates.prover.Prover.AXIOMS`.
    """
    prover = Prover({'~Ex[(Homework(x)&Fun(x))]',
                     'Ex[(Homework(x)&Reading(x))]'}, print_as_proof_forms)
    # Task 10.5
    return prover.qed()

#: The three group axioms
GROUP_AXIOMS = frozenset({'plus(0,x)=x', 'plus(minus(x),x)=0',
                          'plus(plus(x,y),z)=plus(x,plus(y,z))'})

def right_neutral_proof(stop_before_flipped_equality: bool,
                        stop_before_free_instantiation: bool,
                        stop_before_substituted_equality: bool,
                        stop_before_chained_equality: bool,
                        print_as_proof_forms: bool = False) -> Proof:
    """Proves from the group axioms that x+0=x (``'plus(x,0)=x'``).

    Parameters:
        stop_before_flipped_equality: flag specifying to stop proving just
            before the first call to
            `~predicates.prover.Prover.add_flipped_equality` and to return the
            prefix of the proof constructed up to that point.
        stop_before_free_instantiation: flag specifying to stop proving just
            before the first call to
            `~predicates.prover.Prover.add_free_instantiation` and to return the
            prefix of the proof constructed up to that point.
        stop_before_substituted_equality: flag specifying stop proving just
            before the first call to
            `~predicates.prover.Prover.add_substituted_equality` and to return
            the prefix of the proof constructed up to that point.
        stop_before_chained_equality: flag specifying to stop proving just
            before the first call to
            `~predicates.prover.Prover.add_chained_equality` and to return the
            prefix of the proof constructed up to that point.
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being constructed.

    Returns:
        A valid proof of the above inference via
        `~predicates.prover.Prover.AXIOMS`.
    """
    prover = Prover(GROUP_AXIOMS, print_as_proof_forms)
    zero = prover.add_assumption('plus(0,x)=x')
    negation = prover.add_assumption('plus(minus(x),x)=0')
    associativity = prover.add_assumption('plus(plus(x,y),z)=plus(x,plus(y,z))')
    if stop_before_flipped_equality:
        return prover.qed()
    flipped_zero = prover.add_flipped_equality('x=plus(0,x)', zero)
    flipped_negation = prover.add_flipped_equality(
        '0=plus(minus(x),x)', negation)
    flipped_associativity = prover.add_flipped_equality(
        'plus(x,plus(y,z))=plus(plus(x,y),z)', associativity)
    if stop_before_free_instantiation:
        return prover.qed()
    step7 = prover.add_free_instantiation(
        '0=plus(minus(minus(x)),minus(x))', flipped_negation, {'x': 'minus(x)'})
    step8 = prover.add_flipped_equality(
        'plus(minus(minus(x)),minus(x))=0', step7)
    step9 = prover.add_free_instantiation(
        'plus(plus(minus(minus(x)),minus(x)),x)='
        'plus(minus(minus(x)),plus(minus(x),x))',
        associativity, {'x': 'minus(minus(x))', 'y': 'minus(x)', 'z': 'x'})
    step10 = prover.add_free_instantiation('plus(0,0)=0', zero, {'x': '0'})
    step11 = prover.add_free_instantiation(
        'plus(x,0)=plus(0,plus(x,0))', flipped_zero, {'x': 'plus(x,0)'})
    step12 = prover.add_free_instantiation(
        'plus(0,plus(x,0))=plus(plus(0,x),0)', flipped_associativity,
        {'x': '0', 'y': 'x', 'z': '0'})
    if stop_before_substituted_equality:
        return prover.qed()
    step13 = prover.add_substituted_equality(
        'plus(plus(0,x),0)=plus(plus(plus(minus(minus(x)),minus(x)),x),0)',
        step7, 'plus(plus(_,x),0)')
    step14 = prover.add_substituted_equality(
        'plus(plus(plus(minus(minus(x)),minus(x)),x),0)='
        'plus(plus(minus(minus(x)),plus(minus(x),x)),0)',
        step9, 'plus(_,0)')
    step15 = prover.add_substituted_equality(
        'plus(plus(minus(minus(x)),plus(minus(x),x)),0)='
        'plus(plus(minus(minus(x)),0),0)',
        negation, 'plus(plus(minus(minus(x)),_),0)')
    step16 = prover.add_free_instantiation(
        'plus(plus(minus(minus(x)),0),0)=plus(minus(minus(x)),plus(0,0))',
        associativity, {'x': 'minus(minus(x))', 'y': '0', 'z': '0'})
    step17 = prover.add_substituted_equality(
        'plus(minus(minus(x)),plus(0,0))=plus(minus(minus(x)),0)',
        step10, 'plus(minus(minus(x)),_)')
    step18 = prover.add_substituted_equality(
        'plus(minus(minus(x)),0)=plus(minus(minus(x)),plus(minus(x),x))',
        flipped_negation, 'plus(minus(minus(x)),_)')
    step19 = prover.add_free_instantiation(
        'plus(minus(minus(x)),plus(minus(x),x))='
        'plus(plus(minus(minus(x)),minus(x)),x)', flipped_associativity,
        {'x': 'minus(minus(x))','y': 'minus(x)','z': 'x'})
    step20 = prover.add_substituted_equality(
        'plus(plus(minus(minus(x)),minus(x)),x)=plus(0,x)', step8, 'plus(_,x)')
    if stop_before_chained_equality:
        return prover.qed()
    step21 = prover.add_chained_equality(
        'plus(x,0)=x',
        [step11, step12, step13, step14, step15, step16, step17, step18, step19,
         step20, zero])
    return prover.qed()

def unique_zero_proof(print_as_proof_forms: bool = False) -> Proof:
    """Proves from the group axioms and from the assumption a+c=a
    (``'plus(a,c)=a'``) that c=0 (``'c=0'``).

    Parameters:
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being constructed.

    Returns:
        A valid proof of the above inference via
        `~predicates.prover.Prover.AXIOMS`.
    """
    prover = Prover(GROUP_AXIOMS.union({'plus(a,c)=a'}), print_as_proof_forms)
    # Task 10.10
    return prover.qed()

#: The six field axioms
FIELD_AXIOMS = frozenset(GROUP_AXIOMS.union(
    {'plus(x,y)=plus(y,x)', 'times(x,1)=x', 'times(x,y)=times(y,x)',
     'times(times(x,y),z)=times(x,times(y,z))', '(~x=0->Ey[times(y,x)=1])',
     'times(x,plus(y,z))=plus(times(x,y),times(x,z))'}))

def multiply_zero_proof(print_as_proof_forms: bool = False) -> Proof:
    """Proves from the field axioms that 0*x=0 (``'times(0,x)=0'``).

    Parameters:
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being constructed.

    Returns:
        A valid proof of the above inference via
        `~predicates.prover.Prover.AXIOMS`.
    """
    prover = Prover(FIELD_AXIOMS, print_as_proof_forms)
    # Task 10.11
    return prover.qed()

#: The induction axiom
INDUCTION_AXIOM = Schema(
    Formula.parse('((R(0)&Ax[(R(x)->R(s(x)))])->Ax[R(x)])'), {'R'})
#: The six axioms of Peano arithmetic
PEANO_AXIOMS = frozenset({'(s(x)=s(y)->x=y)', '(~x=0->Ey[s(y)=x])', '~s(x)=0',
                          'plus(x,0)=x', 'plus(x,s(y))=s(plus(x,y))',
                          'times(x,0)=0', 'times(x,s(y))=plus(times(x,y),x)',
                          INDUCTION_AXIOM})

def peano_zero_proof(print_as_proof_forms: bool = False) -> Proof:
    """Proves from the axioms of Peano arithmetic that 0+x=x
    (``'plus(0,x)=x'``).

    Parameters:
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being constructed.

    Returns:
        A valid proof of the above inference via
        `~predicates.prover.Prover.AXIOMS`.
    """
    prover = Prover(PEANO_AXIOMS, print_as_proof_forms)
    # Task 10.12
    return prover.qed()

#: The axiom schema of (unrestricted) comprehension
COMPREHENSION_AXIOM = Schema(
    Formula.parse('Ey[Ax[((In(x,y)->R(x))&(R(x)->In(x,y)))]]'), {'R'})

def russell_paradox_proof(print_as_proof_forms: bool = False) -> Proof:
    """Proves from the axioms schema of unrestricted comprehension the
    contradiction ``'(z=z&~z=z)'``.

    Parameters:
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being constructed.

    Returns:
        A valid proof of the above inference via
        `~predicates.prover.Prover.AXIOMS`.
    """
    prover = Prover({COMPREHENSION_AXIOM}, print_as_proof_forms)
    # Task 10.13
    return prover.qed()

def not_exists_not_implies_all_proof(formula: Formula, variable: str,
                                     print_as_proof_forms: bool = False) -> \
        Proof:
    """Proves that
    ``'(~E``\ `variable`\ ``[~``\ `formula`\ ``]->A``\ `variable`\ ``[``\ `formula`\ ``])'``.

    Parameters:
        formula: predicate for the universal quantification in the formula to be
            proven.
        variable: variable name for the quantifications in the formula to be
            proven.
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being constructed.

    Returns:
        A valid proof of the above inference via
        `~predicates.prover.Prover.AXIOMS`.
    """
    assert is_variable(variable)
    # Optional Task 11.4.1

def exists_not_implies_not_all_proof(formula: Formula, variable: str,
                                     print_as_proof_forms: bool = False) -> \
        Proof:
    """Proves that
    ``'(E``\ `variable`\ ``[~``\ `formula`\ ``]->~A``\ `variable`\ ``[``\ `formula`\ ``])'``.

    Parameters:
        formula: predicate for the universal quantification in the formula to be
            proven.
        variable: variable name for the quantifications in the formula to be
            proven.
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being constructed.

    Returns:
        A valid proof of the above inference via
        `~predicates.prover.Prover.AXIOMS`.
    """
    assert is_variable(variable)
    # Optional Task 11.4.2

def not_all_iff_exists_not_proof(formula: Formula, variable: str,
                                 print_as_proof_forms: bool = False) -> Proof:
    """Proves that
    `equivalence_of`\ ``('(~A``\ `variable`\ ``[``\ `formula`\ ``]', 'E``\ `variable`\ ``[~``\ `formula`\ ``]')``.

    Parameters:
        formula: predicate for the universal quantification in the formula to be
            proven.
        variable: variable name for the quantifications in the formula to be
            proven.
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being constructed.

    Returns:
        A valid proof of the above inference via
        `~predicates.prover.Prover.AXIOMS`.
    """
    assert is_variable(variable)
    # Optional Task 11.4.3
