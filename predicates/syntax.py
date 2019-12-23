# (c) This file is part of the course
# Mathematical Logic through Programming
# by Gonczarowski and Nisan.
# File name: predicates/syntax.py

"""Syntactic handling of first-order formulas and terms."""

from __future__ import annotations
from typing import AbstractSet, Mapping, Optional, Sequence, Set, Tuple, Union

from logic_utils import fresh_variable_name_generator, frozen

from propositions.syntax import Formula as PropositionalFormula, \
                                is_variable as is_propositional_variable

class ForbiddenVariableError(Exception):
    """Raised by `Term.substitute` and `Formula.substitute` when a substituted
    term contains a variable name that is forbidden in that context."""

    def __init__(self, variable_name: str) -> None:
        """Initializes a `ForbiddenVariableError` from its offending variable
        name.

        Parameters:
            variable_name: variable name that is forbidden in the context in
                which a term containing it was to be substituted.
        """
        assert is_variable(variable_name)
        self.variable_name = variable_name

def is_constant(s: str) -> bool:
    """Checks if the given string is a constant name.

    Parameters:
        s: string to check.

    Returns:
        ``True`` if the given string is a constant name, ``False`` otherwise.
    """
    return  (((s[0] >= '0' and s[0] <= '9') or (s[0] >= 'a' and s[0] <= 'd'))
             and s.isalnum()) or s == '_'

def is_variable(s: str) -> bool:
    """Checks if the given string is a variable name.

    Parameters:
        s: string to check.

    Returns:
        ``True`` if the given string is a variable name, ``False`` otherwise.
    """
    return s[0] >= 'u' and s[0] <= 'z' and s.isalnum()

def is_function(s: str) -> bool:
    """Checks if the given string is a function name.

    Parameters:
        s: string to check.

    Returns:
        ``True`` if the given string is a function name, ``False`` otherwise.
    """
    return s[0] >= 'f' and s[0] <= 't' and s.isalnum()

@frozen
class Term:
    """An immutable first-order term in tree representation, composed from
    variable names and constant names, and function names applied to them.

    Attributes:
        root (`str`): the constant name, variable name, or function name at the
            root of the term tree.
        arguments (`~typing.Optional`\\[`~typing.Tuple`\\[`Term`, ...]]): the
            arguments to the root, if the root is a function name.
    """
    root: str
    arguments: Optional[Tuple[Term, ...]]

    def __init__(self, root: str,
                 arguments: Optional[Sequence[Term]] = None) -> None:
        """Initializes a `Term` from its root and root arguments.

        Parameters:
            root: the root for the formula tree.
            arguments: the arguments to the root, if the root is a function
                name.
        """
        if is_constant(root) or is_variable(root):
            assert arguments is None
            self.root = root
        else:
            assert is_function(root)
            assert arguments is not None
            self.root = root
            self.arguments = tuple(arguments)
            assert len(self.arguments) > 0

    def __repr__(self) -> str:
        """Computes the string representation of the current term.

        Returns:
            The standard string representation of the current term.
        """
        # Task 7.1
        if is_constant(self.root) or is_variable(self.root):
            return self.root
        return self.root + '('+ ','.join([str(self.arguments[i]) for i in
                                          range(len(self.arguments))]) + ')'

    def __eq__(self, other: object) -> bool:
        """Compares the current term with the given one.

        Parameters:
            other: object to compare to.

        Returns:
            ``True`` if the given object is a `Term` object that equals the
            current term, ``False`` otherwise.
        """
        return isinstance(other, Term) and str(self) == str(other)
        
    def __ne__(self, other: object) -> bool:
        """Compares the current term with the given one.

        Parameters:
            other: object to compare to.

        Returns:
            ``True`` if the given object is not a `Term` object or does not
            equal the current term, ``False`` otherwise.
        """
        return not self == other

    def __hash__(self) -> int:
        return hash(str(self))

    @staticmethod
    def parse_prefix(s: str) -> Tuple[Term, str]:
        """Parses a prefix of the given string into a term.

        Parameters:
            s: string to parse, which has a prefix that is a valid
                representation of a term.

        Returns:
            A pair of the parsed term and the unparsed suffix of the string. If
            the given string has as a prefix a constant name (e.g., ``'c12'``)
            or a variable name (e.g., ``'x12'``), then the parsed prefix will be
            that entire name (and not just a part of it, such as ``'x1'``).
        """
        # Task 7.3.1

        if is_variable(s[0]):
            i = 1
            while i <= len(s):
                if is_variable(s[0:i]):
                    i += 1
                else:
                    i -= 1
                    break
            return Term(s[:i]), s[i:]

        elif is_constant(s[0]):
            i = 1
            while i <= len(s):
                if is_constant(s[0:i]):
                    i += 1
                else:
                    i -= 1
                    break
            return Term(s[:i]), s[i:]

        elif is_function(s[0]):
            i = 1
            while i <= len(s):
                if is_function(s[0:i]):
                    i += 1
                else:
                    i -= 1
                    break

            # bad input case
            if not((not len(s) == i) and (not s[i] != '(')):
                return None, s

            func_name = s[:i]

            func_params, to_parse = Term.parse_prefix(s[i+1:])
            if len(to_parse) == 0:
                return None, s

            elif to_parse[0] == ')':
                return Term(func_name, [func_params]), to_parse[1:]

            # case ,
            else:
                params = [func_params]
                while to_parse[0] != ')':
                    new_param, to_parse = Term.parse_prefix(
                        to_parse[1:])
                    params.append(new_param)
                return Term(func_name, params), to_parse[1:]

        else:
            return None, s

    @staticmethod
    def parse(s: str) -> Term:
        """Parses the given valid string representation into a term.

        Parameters:
            s: string to parse.

        Returns:
            A term whose standard string representation is the given string.
        """
        # Task 7.3.2

        return Term.parse_prefix(s)[0]

    def constants(self) -> Set[str]:
        """Finds all constant names in the current term.

        Returns:
            A set of all constant names used in the current term.
        """
        # Task 7.5.1

        if is_variable(self.root):
            return set()
        elif is_constant(self.root):
            return {self.root}
        elif is_function(self.root):
            all_constants = set()
            for k in self.arguments:
                all_constants = all_constants.union(k.constants())
            return all_constants


    def variables(self) -> Set[str]:
        """Finds all variable names in the current term.

        Returns:
            A set of all variable names used in the current term.
        """
        # Task 7.5.2

        if is_constant(self.root):
            return set()
        elif is_variable(self.root):
            return {self.root}
        elif is_function(self.root):
            all_variables = set()
            for k in self.arguments:
                all_variables = all_variables.union(k.variables())
            return all_variables



    def functions(self) -> Set[Tuple[str, int]]:
        """Finds all function names in the current term, along with their
        arities.

        Returns:
            A set of pairs of function name and arity (number of arguments) for
            all function names used in the current term.
        """
        # Task 7.5.3
        if is_constant(self.root):
            return set()
        elif is_variable(self.root):
            return set()
        elif is_function(self.root):
            all_functions = {(self.root, len(self.arguments))}
            for k in self.arguments:
                all_functions = all_functions.union(k.functions())
            return all_functions


    def substitute(self, substitution_map: Mapping[str, Term],
                   forbidden_variables: AbstractSet[str] = frozenset()) -> Term:
        """Substitutes in the current term, each constant name `name` or
        variable name `name` that is a key in `substitution_map` with the term
        `substitution_map[name]`.

        Parameters:
            substitution_map: mapping defining the substitutions to be
                performed.
            forbidden_variables: variables not allowed in substitution terms.

        Returns:
            The term resulting from performing all substitutions. Only
            constant names and variable names originating in the current term
            are substituted (i.e., those originating in one of the specified
            substitutions are not subjected to additional substitutions).

        Raises:
            ForbiddenVariableError: If a term that is used in the requested
                substitution contains a variable from `forbidden_variables`.

        Examples:
            >>> Term.parse('f(x,c)').substitute(
            ...     {'c': Term.parse('plus(d,x)'), 'x': Term.parse('c')}, {'y'})
            f(c,plus(d,x))
            >>> Term.parse('f(x,c)').substitute(
            ...     {'c': Term.parse('plus(d,y)')}, {'y'})
            Traceback (most recent call last):
              ...
            predicates.syntax.ForbiddenVariableError: y
        """
        for element_name in substitution_map:
            assert is_constant(element_name) or is_variable(element_name)
        for variable in forbidden_variables:
            assert is_variable(variable)
        # Task 9.1

        # substitute variable
        if is_variable(self.root) and self.root in substitution_map:

            if substitution_map[self.root].variables().intersection(forbidden_variables):
                bad_var = substitution_map[self.root].variables().intersection(
                    forbidden_variables).pop()
                raise ForbiddenVariableError(str(bad_var))
            else:
                return substitution_map[self.root]

        # replace constant
        elif is_constant(self.root) and self.root in substitution_map:
            if substitution_map[self.root].variables().intersection(forbidden_variables):
                bad_var = substitution_map[self.root].variables().intersection(
                    forbidden_variables).pop()
                raise ForbiddenVariableError(str(bad_var))
            return substitution_map[self.root]

        # substitute function
        elif is_function(self.root):
            new_arguments = []
            for arg in self.arguments:
                new_arguments.append(arg.substitute(substitution_map, forbidden_variables))

            # replace self name
            if self.root in substitution_map:
                return Term(substitution_map[self.root].root, new_arguments)
            else:
                return Term(self.root, new_arguments)

        return self


def is_equality(s: str) -> bool:
    """Checks if the given string is the equality relation.

    Parameters:
        s: string to check.

    Returns:
        ``True`` if the given string is the equality relation, ``False``
        otherwise.
    """
    return s == '='

def is_relation(s: str) -> bool:
    """Checks if the given string is a relation name.

    Parameters:
        s: string to check.

    Returns:
        ``True`` if the given string is a relation name, ``False`` otherwise.
    """
    return s[0] >= 'F' and s[0] <= 'T' and s.isalnum()

def is_unary(s: str) -> bool:
    """Checks if the given string is a unary operator.

    Parameters:
        s: string to check.

    Returns:
        ``True`` if the given string is a unary operator, ``False`` otherwise.
    """
    return s == '~'

def is_binary(s: str) -> bool:
    """Checks if the given string is a binary operator.

    Parameters:
        s: string to check.

    Returns:
        ``True`` if the given string is a binary operator, ``False`` otherwise.
    """
    return s == '&' or s == '|' or s == '->'

def is_quantifier(s: str) -> bool:
    """Checks if the given string is a quantifier.

    Parameters:
        s: string to check.

    Returns:
        ``True`` if the given string is a quantifier, ``False`` otherwise.
    """
    return s == 'A' or s == 'E'

@frozen
class Formula:
    """An immutable first-order formula in tree representation, composed from
    relation names applied to first-order terms, and operators and
    quantifications applied to them.

    Attributes:
        root (`str`): the relation name, equality relation, operator, or
            quantifier at the root of the formula tree.
        arguments (`~typing.Optional`\\[`~typing.Tuple`\\[`Term`, ...]]): the
            arguments to the root, if the root is a relation name or the
            equality relation.
        first (`~typing.Optional`\\[`Formula`]): the first operand to the root,
            if the root is a unary or binary operator.
        second (`~typing.Optional`\\[`Formula`]): the second
            operand to the root, if the root is a binary operator.
        variable (`~typing.Optional`\\[`str`]): the variable name quantified by
            the root, if the root is a quantification.
        predicate (`~typing.Optional`\\[`Formula`]): the predicate quantified by
            the root, if the root is a quantification.
    """
    root: str
    arguments: Optional[Tuple[Term, ...]]
    first: Optional[Formula]
    second: Optional[Formula]
    variable: Optional[str]
    predicate: Optional[Formula]

    def __init__(self, root: str,
                 arguments_or_first_or_variable: Union[Sequence[Term],
                                                       Formula, str],
                 second_or_predicate: Optional[Formula] = None) -> None:
        """Initializes a `Formula` from its root and root arguments, root
        operands, or root quantified variable and predicate.

        Parameters:
            root: the root for the formula tree.
            arguments_or_first_or_variable: the arguments to the the root, if
                the root is a relation name or the equality relation; the first
                operand to the root, if the root is a unary or binary operator;
                the variable name quantified by the root, if the root is a
                quantification.
            second_or_predicate: the second operand to the root, if the root is
                a binary operator; the predicate quantified by the root, if the
                root is a quantification.
        """
        if is_equality(root) or is_relation(root):
            # Populate self.root and self.arguments
            assert second_or_predicate is None
            assert isinstance(arguments_or_first_or_variable, Sequence) and \
                   not isinstance(arguments_or_first_or_variable, str)
            self.root, self.arguments = \
                root, tuple(arguments_or_first_or_variable)
            if is_equality(root):
                assert len(self.arguments) == 2
        elif is_unary(root):
            # Populate self.first
            assert isinstance(arguments_or_first_or_variable, Formula) and \
                   second_or_predicate is None
            self.root, self.first = root, arguments_or_first_or_variable
        elif is_binary(root):
            # Populate self.first and self.second
            assert isinstance(arguments_or_first_or_variable, Formula) and \
                   second_or_predicate is not None
            self.root, self.first, self.second = \
                root, arguments_or_first_or_variable, second_or_predicate           
        else:
            assert is_quantifier(root)
            # Populate self.variable and self.predicate
            assert isinstance(arguments_or_first_or_variable, str) and \
                   is_variable(arguments_or_first_or_variable) and \
                   second_or_predicate is not None
            self.root, self.variable, self.predicate = \
                root, arguments_or_first_or_variable, second_or_predicate

    def __repr__(self) -> str:
        """Computes the string representation of the current formula.

        Returns:
            The standard string representation of the current formula.
        """
        # Task 7.2

        if is_equality(self.root):
            return str(self.arguments[0]) + self.root + \
                   str(self.arguments[1])

        elif is_relation(self.root):
            return self.root + '(' + ','.join([str(self.arguments[i]) for i in
                                       range(len(self.arguments))]) + ')'

        elif is_unary(self.root):
            return self.root + str(self.first)

        elif is_quantifier(self.root):
            return self.root + self.variable + '[' + str(self.predicate) + ']'

        elif is_binary(self.root):
            return '('+str(self.first) + self.root + str(self.second) + ')'

    def __eq__(self, other: object) -> bool:
        """Compares the current formula with the given one.

        Parameters:
            other: object to compare to.

        Returns:
            ``True`` if the given object is a `Formula` object that equals the
            current formula, ``False`` otherwise.
        """
        return isinstance(other, Formula) and str(self) == str(other)
        
    def __ne__(self, other: object) -> bool:
        """Compares the current formula with the given one.

        Parameters:
            other: object to compare to.

        Returns:
            ``True`` if the given object is not a `Formula` object or does not
            equal the current formula, ``False`` otherwise.
        """
        return not self == other

    def __hash__(self) -> int:
        return hash(str(self))

    @staticmethod
    def parse_prefix(s: str) -> Tuple[Formula, str]:
        """Parses a prefix of the given string into a formula.

        Parameters:
            s: string to parse, which has a prefix that is a valid
                representation of a formula.

        Returns:
            A pair of the parsed formula and the unparsed suffix of the string.
            If the given string has as a prefix a term followed by an equality
            followed by a constant name (e.g., ``'c12'``) or by a variable name
            (e.g., ``'x12'``), then the parsed prefix will include that entire
            name (and not just a part of it, such as ``'x1'``).
        """
        # Task 7.4.1

        if is_relation(s[0]):
            i = 1
            while i <= len(s):
                if is_relation(s[0:i]):
                    i += 1
                else:
                    i -= 1
                    break

            rel_name = s[:i]

            # case no args
            if s[i+1] == ')':
                return Formula(rel_name, []), s[i+2:]

            rel_param, to_parse = Term.parse_prefix(s[i+1:])
            if len(to_parse) == 0:
                return None, s

            relationship_params = [rel_param]
            if to_parse[0] == ')':
                return Formula(rel_name, relationship_params), to_parse[1:]

            # case ,
            else:
                while to_parse[0] != ')':
                    new_param, to_parse = Term.parse_prefix(
                        to_parse[1:])
                    relationship_params.append(new_param)
                return Formula(rel_name, relationship_params), to_parse[1:]

        elif is_unary(s[0]):
            f, r = Formula.parse_prefix(s[1:])
            return Formula(s[0], f), r

        elif is_quantifier(s[0]):
            i = 2
            while i <= len(s):
                if is_variable(s[1:i]):
                    i += 1
                else:
                    i -= 1
                    break
            quantifier = s[0]
            quantified_var = s[1:i]
            quantified_formula, remainder = Formula.parse_prefix(s[i+1:])
            return Formula(quantifier, quantified_var, quantified_formula), \
                   remainder[1:]

        # binary case
        elif s[0] == '(':
            first, remainder = Formula.parse_prefix(s[1:])
            if is_binary(remainder[0]):
                binary_op = remainder[0]
                i = 1
            else:
                binary_op = remainder[:2]
                i = 2
            second, remainder = Formula.parse_prefix(remainder[i:])
            if second is not None and len(remainder) > 0 and remainder[0] == ')':
                return Formula(binary_op, first, second), remainder[1:]

        # equality case
        else:
            first, remainder = Term.parse_prefix(s)
            op = remainder[0]
            second, remainder = Term.parse_prefix(remainder[1:])
            return Formula(op, [first, second]), remainder

    @staticmethod
    def parse(s: str) -> Formula:
        """Parses the given valid string representation into a formula.

        Parameters:
            s: string to parse.

        Returns:
            A formula whose standard string representation is the given string.
        """
        # Task 7.4.2
        return Formula.parse_prefix(s)[0]

    def constants(self) -> Set[str]:
        """Finds all constant names in the current formula.

        Returns:
            A set of all constant names used in the current formula.
        """
        # Task 7.6.1

        if is_unary(self.root):
            return self.first.constants()

        elif is_equality(self.root):
            return self.arguments[0].constants() | self.arguments[1].constants()

        elif is_binary(self.root):
            return self.first.constants() | self.second.constants()

        elif is_relation(self.root):
            all_constants = set()
            for k in self.arguments:
                all_constants = all_constants.union(k.constants())
            return all_constants

        elif is_quantifier(self.root):
            return self.predicate.constants()

    def variables(self) -> Set[str]:
        """Finds all variable names in the current formula.

        Returns:
            A set of all variable names used in the current formula.
        """
        # Task 7.6.2

        if is_unary(self.root):
            return self.first.variables()

        elif is_equality(self.root):
            return self.arguments[0].variables() | self.arguments[1].variables()

        elif is_binary(self.root):
            return self.first.variables() | self.second.variables()

        elif is_relation(self.root):
            all_variables = set()
            for k in self.arguments:
                all_variables = all_variables.union(k.variables())
            return all_variables

        elif is_quantifier(self.root):
            return self.predicate.variables() | {self.variable}

    def free_variables(self) -> Set[str]:
        """Finds all variable names that are free in the current formula.

        Returns:
            A set of all variable names used in the current formula not only
            within a scope of a quantification on those variable names.
        """
        # Task 7.6.3

        if is_unary(self.root):
            return self.first.free_variables()

        elif is_equality(self.root):
            return self.arguments[0].variables() | self.arguments[1].variables()

        elif is_binary(self.root):
            return self.first.free_variables() | self.second.free_variables()

        elif is_relation(self.root):
            all_variables = set()
            for k in self.arguments:
                all_variables = all_variables.union(k.variables())
            return all_variables

        elif is_quantifier(self.root):
            return self.predicate.free_variables() - {self.variable}

    def functions(self) -> Set[Tuple[str, int]]:
        """Finds all function names in the current formula, along with their
        arities.

        Returns:
            A set of pairs of function name and arity (number of arguments) for
            all function names used in the current formula.
        """
        # Task 7.6.4
        if is_unary(self.root):
            return self.first.functions()

        elif is_equality(self.root):
            return self.arguments[0].functions() | self.arguments[1].functions()

        elif is_binary(self.root):
            return self.first.functions() | self.second.functions()

        elif is_relation(self.root):
            all_variables = set()
            for k in self.arguments:
                all_variables = all_variables.union(k.functions())
            return all_variables

        elif is_quantifier(self.root):
            return self.predicate.functions()

    def relations(self) -> Set[Tuple[str, int]]:
        """Finds all relation names in the current formula, along with their
        arities.

        Returns:
            A set of pairs of relation name and arity (number of arguments) for
            all relation names used in the current formula.
        """
        # Task 7.6.5
        if is_unary(self.root):
            return self.first.relations()

        elif is_equality(self.root):
            return set()

        elif is_binary(self.root):
            return self.first.relations() | self.second.relations()

        elif is_relation(self.root):
            all_relations = {(self.root, len(self.arguments))}
            return all_relations

        elif is_quantifier(self.root):
            return self.predicate.relations()

    def substitute(self, substitution_map: Mapping[str, Term],
                   forbidden_variables: AbstractSet[str] = frozenset()) -> \
                Formula:
        """Substitutes in the current formula, each constant name `name` or free
        occurrence of variable name `name` that is a key in `substitution_map`
        with the term `substitution_map[name]`.

        Parameters:
            substitution_map: mapping defining the substitutions to be
                performed.
            forbidden_variables: variables not allowed in substitution terms.

        Returns:
            The formula resulting from performing all substitutions. Only
            constant names and variable names originating in the current formula
            are substituted (i.e., those originating in one of the specified
            substitutions are not subjected to additional substitutions).

        Raises:
            ForbiddenVariableError: If a term that is used in the requested
                substitution contains a variable from `forbidden_variables`
                or a variable occurrence that becomes bound when that term is
                substituted into the current formula.

        Examples:
            >>> Formula.parse('Ay[x=c]').substitute(
            ...     {'c': Term.parse('plus(d,x)'), 'x': Term.parse('c')}, {'z'})
            Ay[c=plus(d,x)]
            >>> Formula.parse('Ay[x=c]').substitute(
            ...     {'c': Term.parse('plus(d,z)')}, {'z'})
            Traceback (most recent call last):
              ...
            predicates.syntax.ForbiddenVariableError: z
            >>> Formula.parse('Ay[x=c]').substitute(
            ...     {'c': Term.parse('plus(d,y)')})
            Traceback (most recent call last):
              ...
            predicates.syntax.ForbiddenVariableError: y
        """
        for element_name in substitution_map:
            assert is_constant(element_name) or is_variable(element_name)
        for variable in forbidden_variables:
            assert is_variable(variable)
        # Task 9.2

        #substitute terms
        if is_equality(self.root) or is_relation(self.root):
            new_arguments = []
            for arg in self.arguments:
                new_arguments.append(arg.substitute(substitution_map, forbidden_variables))
            return Formula(self.root, new_arguments)

        #substitute formulas
        if is_unary(self.root):
            return Formula("~", self.first.substitute(substitution_map, forbidden_variables))

        if is_binary(self.root):
            return Formula(self.root, self.first.substitute(
                substitution_map, forbidden_variables),
                           self.second.substitute(substitution_map, forbidden_variables))

        if is_quantifier(self.root):
            checker_set = set(forbidden_variables)
            new_substitution_map = substitution_map.copy()
            if self.variable not in self.free_variables():
                checker_set.add(self.variable)
                if self.variable in substitution_map.keys():
                    del new_substitution_map[self.variable]
            return Formula(self.root, self.variable, self.predicate.substitute(new_substitution_map, checker_set))
        return self





    def propositional_skeleton(self) -> Tuple[PropositionalFormula,
                                              Mapping[str, Formula]]:
        """Computes a propositional skeleton of the current formula.

        Returns:
            A pair. The first element of the pair is a propositional formula
            obtained from the current formula by substituting every (outermost)
            subformula that has a relation or quantifier at its root with an
            atomic propositional formula, consistently such that multiple equal
            such (outermost) subformulas are substituted with the same atomic
            propositional formula. The atomic propositional formulas used for
            substitution are obtained, from left to right, by calling
            `next`\ ``(``\ `~logic_utils.fresh_variable_name_generator`\ ``)``.
            The second element of the pair is a map from each atomic
            propositional formula to the subformula for which it was
            substituted.
        """
        # Task 9.6

    @staticmethod
    def from_propositional_skeleton(skeleton: PropositionalFormula,
                                    substitution_map: Mapping[str, Formula]) -> \
            Formula:
        """Computes a first-order formula from a propositional skeleton and a
        substitution map.

        Arguments:
            skeleton: propositional skeleton for the formula to compute.
            substitution_map: a map from each atomic propositional subformula
                of the given skeleton to a first-order formula.

        Returns:
            A first-order formula obtained from the given propositional skeleton
            by substituting each atomic propositional subformula with the formula
            mapped to it by the given map.
        """
        for key in substitution_map:
            assert is_propositional_variable(key)
        # Task 9.10
