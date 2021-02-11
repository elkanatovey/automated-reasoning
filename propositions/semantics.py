""""Semantic analysis of propositional-logic constructs."""
import itertools
from typing import AbstractSet, Iterable, Iterator, List, Mapping

from propositions.syntax import *


Model = Mapping[str, bool]

def is_model(model: Model) -> bool:
    """Checks if the given dictionary a model over some set of variables.

    Parameters:
        model: dictionary to check.

    Returns:
        ``True`` if the given dictionary is a model over some set of variables,
        ``False`` otherwise.
    """
    for key in model:
        if not (is_variable(key) and type(model[key]) is bool):
            return False
    return True

def variables(model: Model) -> AbstractSet[str]:
    """Finds all variables over which the given model is defined.

    Parameters:
        model: model to check.

    Returns:
        A set of all variables over which the given model is defined.
    """
    assert is_model(model)
    return model.keys()

def evaluate(formula: Formula, model: Model) -> bool:
    """Calculates the truth value of the given formula in the given model.

    Parameters:
        formula: formula to calculate the truth value of.
        model: model over (possibly a superset of) the variables of the formula,
            to calculate the truth value in.

    Returns:
        The truth value of the given formula in the given model.
    """
    assert is_model(model)
    assert formula.variables().issubset(variables(model))
    # Task 2.1

    # binary case
    if hasattr(formula, 'second'):
        if str(formula.second) in model:
            second_val = model[str(formula.second)]
        else:
            second_val = evaluate(formula.second, model)

        if str(formula.first) not in model:
            first_val = evaluate(formula.first, model)
        else:
            first_val = model[str(formula.first)]

        if formula.root == '->':  # implies
            return (not first_val) or second_val
        if formula.root == '&':  # and
            return first_val and second_val
        if formula.root == '|':  # or
            return first_val or second_val
        if formula.root == '+':  # xor
            return first_val != second_val
        if formula.root == '<->':  # iff
            return first_val == second_val
        if formula.root == '-&':  # nand
            return not (first_val and second_val)
        if formula.root == '-|':  # nor
            return not (first_val or second_val)

    # unary case
    if hasattr(formula, 'first'):
        if str(formula.first) not in model:
            first_val = evaluate(formula.first, model)
        else:
            first_val = model[str(formula.first)]
        return not first_val

    # atomic case
    if formula.root == 'T':
        return True
    elif formula.root == 'F':
        return False
    return model[str(formula)]


def all_models(variables: List[str]) -> Iterable[Model]:
    """Calculates all possible models over the given variables.

    Parameters:
        variables: list of variables over which to calculate the models.

    Returns:
        An iterable over all possible models over the given variables. The order
        of the models is lexicographic according to the order of the given
        variables, where False precedes True.

    Examples:
        >>> list(all_models(['p', 'q']))
        [{'p': False, 'q': False}, {'p': False, 'q': True}, {'p': True, 'q': False}, {'p': True, 'q': True}]
    """
    for v in variables:
        assert is_variable(v)
    # Task 2.2
    bools = [False, True]
    num_of_variables = len(variables)
    for model in itertools.product(bools, repeat=num_of_variables):
        yield {v: model[i] for i, v in enumerate(variables)}


def truth_values(formula: Formula, models: Iterable[Model]) -> Iterable[bool]:
    """Calculates the truth value of the given formula in each of the given
    model.

    Parameters:
        formula: formula to calculate the truth value of.
        model: iterable over models to calculate the truth value in.

    Returns:
        An iterable over the respective truth values of the given formula in
        each of the given models, in the order of the given models.
    """
    # Task 2.3
    for model in models:
        yield evaluate(formula, model)


def print_truth_table(formula: Formula) -> None:
    """Prints the truth table of the given formula, with variable-name columns
    sorted alphabetically.

    Parameters:
        formula: formula to print the truth table of.

    Examples:
        >>> print_truth_table(Formula.parse('~(p&q76)'))
        | p | q76 | ~(p&q76) |
        |---|-----|----------|
        | F | F   | T        |
        | F | T   | T        |
        | T | F   | T        |
        | T | T   | F        |
    """
    # Task 2.4
    atomics = formula.variables()
    atomics = list(atomics)
    atomics.sort()
    for atom in atomics:
        print("| ", atom, " ", end='')
    print("| ", formula, " |")

    for i in range(0, len(atomics)):
        print("|-", '-'*(1+len(atomics[i])), end='')
    print("|-", '-'*(1+len(formula.root)),'|')
    model_gen = all_models(atomics)
    for model in model_gen:
        for i in range(0, len(atomics)):
            print("| ", end='')
            if model[atomics[i]]:
                print('T', ' '*len(atomics[i]), end='')
            else:
                print('F', ' '*len(atomics[i]), end='')
        print("| ", end='')
        model_result = evaluate(formula, model)
        if model_result:
            print('T', ' '*len(formula.root), '|')
        else:
            print('F', ' '*len(formula.root), '|')


def is_tautology(formula: Formula) -> bool:
    """Checks if the given formula is a tautology.

    Parameters:
        formula: formula to check.

    Returns:
        ``True`` if the given formula is a tautology, ``False`` otherwise.
    """
    # Task 2.5a
    atomic_vars = list(formula.variables())
    models = all_models(atomic_vars)
    tautology_check = truth_values(formula, models)
    for setting in tautology_check:
        if setting is False:
            return False
    return True


def is_contradiction(formula: Formula) -> bool:
    """Checks if the given formula is a contradiction.

    Parameters:
        formula: formula to check.

    Returns:
        ``True`` if the given formula is a contradiction, ``False`` otherwise.
    """
    # Task 2.5b
    atomic_vars = formula.variables()
    models = all_models(list(atomic_vars))
    contradiction_check = truth_values(formula, models)
    for setting in contradiction_check:
        if setting is True:
            return False
    return True

def is_satisfiable(formula: Formula) -> bool:
    """Checks if the given formula is satisfiable.

    Parameters:
        formula: formula to check.

    Returns:
        ``True`` if the given formula is satisfiable, ``False`` otherwise.
    """
    # Task 2.5c
    return not is_contradiction(formula)


def synthesize_for_model(model: Model) -> Formula:
    """Synthesizes a propositional formula in the form of a single clause that
      evaluates to ``True`` in the given model, and to ``False`` in any other
      model over the same variables.

    Parameters:
        model: model in which the synthesized formula is to hold.

    Returns:
        The synthesized formula.
    """
    assert is_model(model)
    # Task 2.6
    if len(model.keys()) == 1:
        for key in model:
            if model[key]:
                return Formula(key)
            s = '~' + key
            return Formula.parse_prefix(s)[0]
    formula_string = ''
    count = -1
    for key in model:
        if not model[key]:
            if (count+2) == len(model.keys()):
                formula_string = formula_string + '~' + key
            else:
                formula_string = formula_string + '(~' + key + '&'
        else:
            if (count+2) == len(model.keys()):
                formula_string = formula_string + key
            else:
                formula_string += '(' + key + '&'
        count += 1
    formula_string = formula_string + ')'*count
    return Formula.parse_prefix(formula_string)[0]

def synthesize(variables: List[str], values: Iterable[bool]) -> Formula:
    """Synthesizes a propositional formula in DNF over the given variables, from
    the given specification of which value the formula should have on each
    possible model over these variables.

    Parameters:
        variables: the set of variables for the synthesize formula.
        values: iterable over truth values for the synthesized formula in every
            possible model over the given variables, in the order returned by
            `all_models`\ ``(``\ `~synthesize.variables`\ ``)``.

    Returns:
        The synthesized formula.

    Examples:
        >>> formula = synthesize(['p', 'q'], [True, True, True, False])
        >>> for model in all_models(['p', 'q']):
        ...     evaluate(formula, model)
        True
        True
        True
        False
    """
    assert len(variables) > 0
    # Task 2.7

    models = all_models(variables)
    dnf_string = ''
    most_recent_formula = ''
    count = -1
    for value, model in zip(values, models):
        if value:
            most_recent_formula = str(synthesize_for_model(model))
            dnf_string += '(' + most_recent_formula + '|'
            count += 1

    # false table case
    if count == -1:
        contradiction_str = ''
        count = 0
        for atom in variables:
            contradiction_str = '(('+atom+'&~'+atom+')&'
        if count == 0:
            contradiction_str = contradiction_str[1:-1]
            return Formula.parse_prefix(contradiction_str)[0]
        contradiction_str = contradiction_str[:-1] + ')'*count
        return Formula.parse_prefix(contradiction_str)[0]

    # one value case
    if count == 0:
        dnf_string = dnf_string[1:-1]
        return Formula.parse_prefix(dnf_string)[0]

    # standard case
    dnf_string = dnf_string[:-len(most_recent_formula)-2] + \
                 most_recent_formula + count*')'
    return Formula.parse_prefix(dnf_string)[0]
