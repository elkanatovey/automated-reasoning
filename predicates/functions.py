# (c) This file is part of the course
# Mathematical Logic through Programming
# by Gonczarowski and Nisan.
# File name: predicates/functions.py

"""Syntactic conversion of first-order formulas to not use functions and
equality."""

from typing import AbstractSet, List, Set

from logic_utils import fresh_variable_name_generator

from predicates.syntax import *
from predicates.semantics import *


def function_name_to_relation_name(function: str) -> str:
    """Converts the given function name to a canonically corresponding relation
    name.

    Parameters:
        function: function name to convert.

    Returns:
        A relation name that is the same as the given function name, except that
        its first letter is capitalized.
    """
    assert is_function(function)
    return function[0].upper() + function[1:]


def relation_name_to_function_name(relation: str) -> str:
    """Converts the given relation name to a canonically corresponding function
    name.

    Parameters:
        relation: relation name to convert.

    Returns:
        A function name `function` such that
        `function_name_to_relation_name`\ ``(``\ `function`\ ``)`` is the given
        relation name.
    """
    assert is_relation(relation)
    return relation[0].lower() + relation[1:]


def replace_functions_with_relations_in_model(model: Model[T]) -> Model[T]:
    """Converts the given model to a canonically corresponding model without any
    function meanings, replacing each function meaning with a canonically
    corresponding relation meaning.

    Parameters:
        model: model to convert, such that there exist no canonically
            corresponding function name and relation name that both have
            meanings in this model.

    Return:
        A model obtained from the given model by replacing every function
        meaning of a function name with a relation meaning of the canonically
        corresponding relation name, such that the relation meaning contains
        any tuple ``(``\ `x1`\ ``,``...\ ``,``\ `xn`\ ``)``  if and only if `x1`
        is the output of the function meaning for the arguments
        ``(``\ `x2`\ ``,``...\ ``,``\ `xn`\ ``)``.
    """
    for function in model.function_meanings:
        assert function_name_to_relation_name(function) not in \
               model.relation_meanings
    # Task 8.1

    new_relation_meanings = dict(model.relation_meanings)

    # go over each function to convert
    for function_name in model.function_meanings:
        r_name = function_name_to_relation_name(function_name)
        f_mapping = model.function_meanings[function_name]
        new_relation_meanings.update({r_name: set()})

        # iterate over valid settings and add to relation
        for assignment in f_mapping:
            assignment_list = list(assignment)
            assignment_list.insert(0, f_mapping[assignment])
            new_relation_meanings[r_name].add(tuple(assignment_list))

    return Model(model.universe, model.constant_meanings,
                 new_relation_meanings, {})


def replace_relations_with_functions_in_model(model: Model[T],
                                              original_functions:
                                              AbstractSet[str]) -> \
        Union[Model[T], None]:
    """Converts the given model with no function meanings to a canonically
    corresponding model with meanings for the given function names, having each
    new function meaning replace a canonically corresponding relation meaning.

    Parameters:
        model: model to convert, that contains no function meanings.
        original_functions: function names for the model to convert to,
            such that no relation name that canonically corresponds to any of
            these function names has a meaning in the given model.

    Returns:
        A model `model` with the given function names such that
        `replace_functions_with_relations_in_model`\ ``(``\ `model`\ ``)``
        is the given model, or ``None`` if no such model exists.
    """
    for function in original_functions:
        assert is_function(function)
        assert function not in model.function_meanings
        assert function_name_to_relation_name(function) in \
               model.relation_meanings
    # Task 8.2

    for f_name in original_functions:
        if function_name_to_relation_name(f_name) not in \
                model.relation_meanings.keys():
            return None

    new_function_meanings = dict(model.function_meanings)
    updated_relation_meanings = dict()

    # go over each relation to convert

    for relation_name in model.relation_meanings:
        f_name = relation_name_to_function_name(relation_name)
        if f_name not in original_functions:
            updated_relation_meanings.update({relation_name: \
                                                  model.relation_meanings[
                                                      relation_name]})
            continue

        r_mapping = model.relation_meanings[relation_name]
        new_function_meanings.update({f_name: dict()})

        # iterate over valid settings and add to relation

        checker = set()
        for assignment in r_mapping:

            if (len(assignment) < 2):
                return None

            new_function_meanings[f_name][assignment[1:]] = \
                assignment[0]
            if assignment[1:] in checker:
                return None
            checker.add(assignment[1:])

        if len(checker) < len(model.universe) ** (model.relation_arities[
                                                      relation_name] - 1):
            return None

    return Model(model.universe, model.constant_meanings,
                 updated_relation_meanings,
                 new_function_meanings)


def compile_term(term: Term) -> List[Formula]:
    """Syntactically compiles the given term into a list of single-function
    invocation steps.

    Parameters:
        term: term to compile, whose root is a function invocation, and that
            contains no variable names starting with ``z``.

    Returns:
        A list of steps, each of which is a formula of the form
        ``'``\ `y`\ ``=``\ `f`\ ``(``\ `x1`\ ``,``...\ ``,``\ `xn`\ ``)'``,
        where `y` is a new variable name obtained by calling
        `next`\ ``(``\ `~logic_utils.fresh_variable_name_generator`\ ``)``, `f`
        is a function name, and each of the `x`\ `i` is either a constant name
        or a variable name. If `x`\ `i` is a new variable name, then it is also
        the left-hand side of a previous step, where all of the steps "leading
        up to" `x1` precede those "leading up" to `x2`, etc. If all the returned
        steps hold in any model, then the left-hand-side variable of the last
        returned step evaluates in that model to the value of the given term.
    """
    assert is_function(term.root)
    # Task 8.3
    formula_list = []

    construction_formula = []

    for argument in term.arguments:
        if is_function(argument.root):
            formula_list.extend(compile_term(argument))
            construction_formula.append(formula_list[-1].arguments[0])

            # recursion base
        else:
            construction_formula.append(argument)

    function_as_z = next(fresh_variable_name_generator)

    function_as_z = Term.parse(function_as_z)
    function_with_z_terms = Term(term.root, construction_formula)

    reconfigured_f = Formula('=', [function_as_z, function_with_z_terms])

    formula_list.append(reconfigured_f)
    return formula_list


def replace_functions_with_relations_in_formula(formula: Formula) -> Formula:
    """Syntactically converts the given formula to a formula that does not
    contain any function invocations, and is "one-way equivalent" in the sense
    that the former holds in a model if and only if the latter holds in the
    canonically corresponding model with no function meanings.

    Parameters:
        formula: formula to convert, that contains no variable names starting
            with ``z``, and such that there exist no canonically corresponding
            function name and relation name that are both invoked in this
            formula.

    Returns:
        A formula such that the given formula holds in any model `model` if and
        only if the returned formula holds in
        `replace_function_with_relations_in_model`\ ``(``\ `model`\ ``)``.
    """
    assert len({function_name_to_relation_name(function) for
                function, arity in formula.functions()}.intersection(
        {relation for relation, arity in formula.relations()})) == 0
    for variable in formula.variables():
        assert variable[0] != 'z'
    # Task 8.4

    # cases

    if is_relation(formula.root) or is_equality(formula.root):

        z_list = list()
        z_names = list()

        for argument in formula.arguments:
            if is_function(argument.root):
                z_list.extend(compile_term(argument))
                z_names.append(z_list[-1].arguments[0])
            else:
                z_names.append(argument)

        # original R with z's as args
        current_exp = Formula(formula.root, z_names)

        for compiled_exp in reversed(z_list):
            r_name = function_name_to_relation_name(compiled_exp.arguments[
                                                        1].root)
            r_args = [compiled_exp.arguments[0]] + list(compiled_exp.arguments[
                                                            1].arguments)
            r_exp = Formula(r_name, r_args)

            current_exp = Formula('->', r_exp, current_exp)
            current_exp = Formula('A', compiled_exp.arguments[0].root,
                                  current_exp)

        return current_exp

    elif is_quantifier(formula.root):
        return Formula(formula.root, formula.variable,
                       replace_functions_with_relations_in_formula(
                           formula.predicate))

    elif is_unary(formula.root):
        return Formula('~', replace_functions_with_relations_in_formula(
            formula.first))

    elif is_binary(formula.root):
        return Formula(formula.root,
                       replace_functions_with_relations_in_formula(
                           formula.first),
                       replace_functions_with_relations_in_formula(
                           formula.second))


def replace_functions_with_relations_in_formulas(formulas:
AbstractSet[Formula]) -> \
        Set[Formula]:
    """Syntactically converts the given set of formulas to a set of formulas
    that do not contain any function invocations, and is "two-way
    equivalent" in the sense that:

    1. The former holds in a model if and only if the latter holds in the
       canonically corresponding model with no function meanings.
    2. The latter holds in a model if and only if that model has a
       canonically corresponding model with meanings for the functions of the
       former, and the former holds in that model.

    Parameters:
        formulas: formulas to convert, that contain no variable names starting
            with ``z``, and such that there exist no canonically corresponding
            function name and relation name that are both invoked in these
            formulas.

    Returns:
        A set of formulas, one for each given formula as well as one additional
        formula for each relation name that replaces a function name from the
        given formulas, such that:

        1. The given formulas holds in a model `model` if and only if the
           returned formulas holds in
           `replace_functions_with_relations_in_model`\ ``(``\ `model`\ ``)``.
        2. The returned formulas holds in a model `model` if and only if
           `replace_relations_with_functions_in_model`\ ``(``\ `model`\ ``,``\ `original_functions`\ ``)``,
           where `original_functions` are all the function names in the given
           formulas, is a model and the given formulas hold in it.
    """
    assert len(set.union(*[{function_name_to_relation_name(function) for
                            function, arity in formula.functions()}
                           for formula in formulas]).intersection(
        set.union(*[{relation for relation, arity in
                     formula.relations()} for
                    formula in formulas]))) == 0
    for formula in formulas:
        for variable in formula.variables():
            assert variable[0] != 'z'
    # Task 8.5
    formula_set = set()

    for formula in formulas:
        functions_in_formula = formula.functions()
        updated_formula = replace_functions_with_relations_in_formula(formula)

        for function in functions_in_formula:
            current_z = next(fresh_variable_name_generator)
            func_args = [Term(current_z)]
            for i in range(0, function[1]):
                func_args.append(Term('x' + str(i)))
            func_as_relation = Formula(function_name_to_relation_name(
                function[0]), func_args)
            exists_qualifier = Formula('E', current_z, func_as_relation)

            all_qualifier = exists_qualifier
            for var in func_args[1:]:
                all_qualifier = Formula('A', var.root, exists_qualifier)

            current_z1 = next(fresh_variable_name_generator)
            func_args[0] = Term(current_z1)
            equality1 = Formula(function_name_to_relation_name(
                function[0]), func_args)

            current_z2 = next(fresh_variable_name_generator)
            func_args[0] = Term(current_z2)
            equality2 = Formula(function_name_to_relation_name(
                function[0]), func_args)

            z1_eq_z2 = Formula("=", [Term(current_z1), Term(current_z2)])
            f1_and_f2 = Formula("&", equality1, equality2)
            implies = Formula("->", f1_and_f2, z1_eq_z2)
            all1 = Formula("A", current_z1, implies)
            all2 = Formula("A", current_z2, all1)
            for var in func_args[1:]:
                all2 = Formula("A", var.root, all2)

            formula_and = Formula("&", all_qualifier, all2)
            formula_set.add(formula_and)

        formula_set.add(updated_formula)

    return formula_set


def same_helper(formula: Formula) -> Formula:
    if is_equality(formula.root):
        return Formula("SAME", formula.arguments)
    if is_relation(formula.root):
        return formula
    if is_unary(formula.root):
        return Formula("~", same_helper(formula.first))
    if is_binary(formula.root):
        return Formula(formula.root, same_helper(formula.first),
                       same_helper(formula.second))
    if is_quantifier(formula.root):
        return Formula(formula.root, formula.variable,
                       same_helper(formula.predicate))


def replace_equality_with_SAME_in_formulas(formulas: AbstractSet[Formula]) -> \
        Set[Formula]:
    """Syntactically converts the given set of formulas to a canonically
    corresponding set of formulas that do not contain any equalities, consisting
    of the following formulas:

    1. A formula for each of the given formulas, where each equality is
       replaced with a matching invocation of the relation name ``'SAME'``.
    2. Formula(s) that ensure that in any model for the returned formulas,
       the meaning of the relation name ``'SAME'`` is reflexive, symmetric, and
       transitive.
    3. For each relation name from the given formulas, formula(s) that ensure
       that in any model for the returned formulas, the meaning of this
       relation name respects the meaning of the relation name ``'SAME'``.

    Parameters:
        formulas: formulas to convert, that contain no function names and do not
            contain the relation name ``'SAME'``.

    Returns:
        The converted set of formulas.
    """
    for formula in formulas:
        assert len(formula.functions()) == 0
        assert 'SAME' not in \
               {relation for relation, arity in formula.relations()}
    # Task 8.6
    return_set = set()

    for formula in formulas:
        samed_formula = same_helper(formula)
        return_set.add(samed_formula)

        relations = formula.relations()
        for relation in relations:
            x_lst = []
            y_lst = []
            for i in range(0, relation[1]):
                x_lst = x_lst + [Term('x'+str(i))]
                y_lst = y_lst + [Term('y'+str(i))]
            formula_y = Formula(relation[0], y_lst)
            formula_x = Formula(relation[0], x_lst)
            x_means_y = Formula('->', formula_x, formula_y)

            a_joined = Formula('SAME', [x_lst[-1], y_lst[-1]])
            for i in range(0, relation[1] - 1):
                a_joined = Formula('&',Formula('SAME', [x_lst[i],
                                                         y_lst[i]]), a_joined)
            x_means_y = Formula('->', a_joined,
                                x_means_y)
            for i in reversed(range(0, relation[1])):
                x_means_y = Formula('A',x_lst[i].root, x_means_y)
            for i in reversed(range(0, relation[1])):
                x_means_y = Formula('A',y_lst[i].root, x_means_y)

            return_set.add(x_means_y)
    return_set.add(Formula.parse("Ax[SAME(x,x)]"))
    return_set.add(Formula.parse("Ax[Ay[((SAME(x,y)->SAME(y,x))&(SAME(y,x)->SAME(x,y)))]]"))
    return_set.add(Formula.parse("Ax[Ay[Az[((SAME(x,y)&SAME(y,z))->SAME(x,z))]]]"))
    return return_set

def add_SAME_as_equality_in_model(model: Model[T]) -> Model[T]:
    """Adds a meaning for the relation name ``'SAME'`` in the given model, that
    canonically corresponds to equality in the given model.

    Parameters:
        model: model that has no meaning for the relation name ``'SAME'``, to
            add the meaning to.

    Return:
        A model obtained from the given model by adding a meaning for the
        relation name ``'SAME'``, that contains precisely all pairs
        ``(``\ `x`\ ``,``\ `x`\ ``)`` for every element `x` of the universe of
        the given model.
    """
    assert 'SAME' not in model.relation_meanings
    # Task 8.7

    updated_relation_meanings = dict(model.relation_meanings)

    same_meanings = list()

    for const in model.universe:
        same_meanings.append((const, const))

    updated_relation_meanings.update({"SAME": set(same_meanings)})

    return Model(model.universe, model.constant_meanings, updated_relation_meanings, model.function_meanings)


def make_equality_as_SAME_in_model(model: Model[T]) -> Model[T]:
    """Converts the given model to a model where equality coincides with the
    meaning of ``'SAME'`` in the given model, in the sense that any set of
    formulas holds in the returned model if and only if its canonically
    corresponding set of formulas that do not contain equality holds in the
    given model.

    Parameters:
        model: model to convert, that contains no function meanings, and
            contains a meaning for the relation name ``'SAME'`` that is
            reflexive, symmetric, transitive, and respected by the meanings
            of all other relation names.

    Returns:
        A model that is a model for any set `formulas` if and only if
        the given model is a model for
        `replace_equality_with_SAME`\ ``(``\ `formulas`\ ``)``. The universe of
        the returned model corresponds to the equivalence classes of the
        ``'SAME'`` relation in the given model.
    """
    assert 'SAME' in model.relation_meanings and \
           model.relation_arities['SAME'] == 2
    assert len(model.function_meanings) == 0
    # Task 8.8

    equality_meanings = set(model.relation_meanings["SAME"])

    equivalence_classes = dict()
    for first, second in equality_meanings:
        if first in equivalence_classes.keys():
            equivalence_classes[first].add(second)
            continue
        flag = True
        for key in equivalence_classes.keys():
            if (first, key) in equality_meanings:
                equivalence_classes[key].union({first, second})
                flag = False
                break
        if flag:
            equivalence_classes[first] = {second}

    classes = dict()
    for key in equivalence_classes.keys():
        for elem in equivalence_classes[key]:
            if elem in equivalence_classes.keys():
                continue
            classes[elem] = key

    new_constants_meanings = dict()
    for key in model.constant_meanings.keys():
        if model.constant_meanings[key] in equivalence_classes.keys():
            new_constants_meanings[key] = model.constant_meanings[key]
        else:
            for rep in equivalence_classes.keys():
                if model.constant_meanings[key] in equivalence_classes[rep]:
                    new_constants_meanings[key] = rep

    new_relations_meanings = dict()
    for relation in model.relation_meanings.keys():
        if relation == "SAME":
            continue
        relation_list1 = list()
        for meanings in model.relation_meanings[relation]:
            relation_list2 = list()
            for elem in meanings:
                if elem in equivalence_classes.keys():
                    relation_list2.append(elem)
                else:
                    relation_list2.append(classes[elem])
            relation_list1.append(tuple(relation_list2))
        new_relations_meanings[relation] = set(relation_list1)

    return Model(equivalence_classes.keys(), new_constants_meanings, new_relations_meanings, model.function_meanings)

