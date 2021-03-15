"""Syntactic handling of propositional formulae."""

from __future__ import annotations
from typing import Mapping, Optional, Set, Tuple, Union, List, MutableMapping

from logic_utils import frozen

POS = 0
NEG = 1

def is_variable(s: str) -> bool:
    """Checks if the given string is an atomic proposition.

    Parameters:
        s: string to check.

    Returns:
        ``True`` if the given string is an atomic proposition, ``False``
        otherwise.
    """
    return s[0] >= 'p' and s[0] <= 'z' and (len(s) == 1 or s[1:].isdigit())

def is_constant(s: str) -> bool:
    """Checks if the given string is a constant.

    Parameters:
        s: string to check.

    Returns:
        ``True`` if the given string is a constant, ``False`` otherwise.
    """
    return s == 'T' or s == 'F'

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
    # return s == '&' or s == '|' or s == '->'
    # For Chapter 3:
    return s in {'&', '|',  '->', '+', '<->', '-&', '-|'}

@frozen
class Formula:
    """An immutable propositional formula in tree representation.

    Attributes:
        root (`str`): the constant, atomic proposition, or operator at the root
            of the formula tree.
        first (`~typing.Optional`\\[`Formula`]): the first operand to the root,
            if the root is a unary or binary operator.
        second (`~typing.Optional`\\[`Formula`]): the second operand to the
            root, if the root is a binary operator.
    """
    root: str
    first: Optional[Formula]
    second: Optional[Formula]

    def __init__(self, root: str, first: Optional[Formula] = None,
                 second: Optional[Formula] = None) -> None:
        """Initializes a `Formula` from its root and root operands.

        Parameters:
            root: the root for the formula tree.
            first: the first operand to the root, if the root is a unary or
                binary operator.
            second: the second operand to the root, if the root is a binary
                operator.
        """
        if is_variable(root) or is_constant(root):
            assert first is None and second is None
            self.root = root
        elif is_unary(root):
            assert type(first) is Formula and second is None
            self.root, self.first = root, first
        else:
            assert is_binary(root) and type(first) is Formula and \
                   type(second) is Formula
            self.root, self.first, self.second = root, first, second

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
            does not equal the current formula, ``False`` otherwise.
        """
        return not self == other

    def __hash__(self) -> int:
        return hash(str(self))

    def __repr__(self) -> str:
        """Computes the string representation of the current formula.

        Returns:
            The standard string representation of the current formula.
        """
        # Task 1.1
        if hasattr(self, 'second'):
            return '(' + str(self.first) + self.root + str(self.second) + ')'
        if hasattr(self, 'first'):
            return self.root + str(self.first)
        return self.root


    def variables(self) -> Set[str]:
        """Finds all atomic propositions (variables) in the current formula.

        Returns:
            A set of all atomic propositions used in the current formula.
        """
        # Task 1.2
        atomics = set()
        if hasattr(self, 'second'):
            atomics = (self.first.variables() | self.second.variables())
            return atomics
        if hasattr(self, 'first'):
            return self.first.variables()
        if is_variable(self.root):
            atomics.add(self.root)
        return atomics

    def pos_literals_consts(self) -> Set[str]:
        """Finds all nonnegated consts and variables in the current clasue. - assumes that
        there are no ands in formula.

        Returns:
            A set of all nonnegated consts and variables used in the current formula.
        """
        assert self.operators().issubset({'~', '|', 'T', 'F'})
        atomics = set()
        if hasattr(self, 'second'):
            atomics = (self.first.pos_literals_consts() | self.second.pos_literals_consts())
            return atomics
        if hasattr(self, 'first'):
            return atomics
        if is_variable(self.root):
            atomics.add(self.root)
        if is_constant(self.root):
            atomics.add(self.root)
        return atomics

    def negated_literals_consts(self) -> Set[str]:
        """Finds all negated consts and variables in the current clause - assumes that
        there are no ands in formula.

        Returns:
            A set of all negated consts and variables used in the current formula.
        """
        assert self.operators().issubset({'~', '|', 'T', 'F'})
        atomics = set()
        if is_variable(self.root):
            return atomics
        if is_constant(self.root):
            return atomics

        if hasattr(self, 'second'):
            atomics = (self.first.negated_literals_consts() | self.second.negated_literals_consts())
            return atomics
        if hasattr(self, 'first'):
            atomics.add(self.first.root)
        return atomics

    def operators(self) -> Set[str]:
        """Finds all operators in the current formula.

        Returns:
            A set of all operators (including ``'T'`` and ``'F'``) used in the
            current formula.
        """
        # Task 1.3
        atomics = set()
        if hasattr(self, 'second'):
            atomics = atomics.union(self.second.operators())
            atomics = atomics.union(self.first.operators())
        elif hasattr(self, 'first'):
            atomics = atomics.union(self.first.operators())
        if not is_variable(self.root):
            atomics.add(self.root)
        return atomics

    def negation_childrens(self) -> Set[str]:
        """Search for children of negations -
             if it's not a variable or a constant, return it.

        Returns:
            A set of children of negations that are not a variable or a constant
        """
        bad_childrens = set()
        if hasattr(self, 'second'):
            bad_childrens = bad_childrens.union(self.second.negation_childrens())
            bad_childrens = bad_childrens.union(self.first.negation_childrens())
        elif hasattr(self, 'first'):
            if is_variable(self.first.root):
                return bad_childrens
            elif is_constant(self.first.root):
                return bad_childrens
            else:
                bad_childrens.add(self.first.root)
        return bad_childrens

    @staticmethod
    def parse_prefix(s: str) -> Tuple[Union[Formula, None], str]:
        """Parses a prefix of the given string into a formula.

        Parameters:
            s: string to parse.

        Returns:
            A pair of the parsed formula and the unparsed suffix of the string.
            If the first token of the string is a variable name (e.g.,
            ``'x12'``), then the parsed prefix will be that entire variable name
            (and not just a part of it, such as ``'x1'``). If no prefix of the
            given string is a valid standard string representation of a formula
            then returned pair should be of ``None`` and an error message, where
            the error message is a string with some human-readable content.
        """
        # Task 1.4
        assert(isinstance(s, str)), [None, 'not a string!']
        if len(s) == 0:
            return None, 'invalid formula!'

        if is_constant(s[0]):
            if len(s)== 1:
                return Formula(s[0]), ''
            return Formula(s[0]), s[1:]

        if is_unary(s[0]):
            if len(s) == 1:
                return None, 'invalid formula!'
            remainder_tuple = Formula.parse_prefix(s[1:])  # recursive validity
            if remainder_tuple[0] is not None:
                return Formula(s[0], remainder_tuple[0]), remainder_tuple[1]
            return None, "invalid formula!"

        if is_variable(s[0]):
            i = 1
            while i <= len(s):
                if is_variable(s[0:i]):
                    i += 1
                else:
                    i -= 1
                    break
            return Formula(s[:i]), s[i:]

        if s[0] == '(':
            remainder_tuple = Formula.parse_prefix(s[1:])  #first var
            if remainder_tuple[0] is not None:
                remainder = remainder_tuple[1]
                if is_binary(remainder[0]):  # 1 part binary val
                    tuple_level2 = Formula.parse_prefix(remainder[1:])
                    #second var
                    if tuple_level2[0] is not None:
                        remain_level2 = tuple_level2[1]
                        if remain_level2 == '' or remain_level2[0] != ')':
                            return None, "bad parenthesis count"
                        return Formula(remainder[0], remainder_tuple[0],
                                             tuple_level2[0]), \
                               remain_level2[1:]

                elif is_binary(remainder[:2]):  # 2 part binary val
                    tuple_level2 = Formula.parse_prefix(remainder[2:])
                    #second var
                    if tuple_level2[0] is not None:
                        remain_level2 = tuple_level2[1]
                        if remain_level2 == '' or remain_level2[0] != ')':
                            return None, "bad parenthesis count"
                        return Formula(remainder[:2], remainder_tuple[0],
                                             tuple_level2[0]), \
                               remain_level2[1:]

                elif is_binary(remainder[:3]):  # 3 part binary val
                    tuple_level2 = Formula.parse_prefix(remainder[3:])
                    #second var
                    if tuple_level2[0] is not None:
                        remain_level2 = tuple_level2[1]
                        if remain_level2 == '' or remain_level2[0] != ')':
                            return None, "bad parenthesis count"
                        return Formula(remainder[:3], remainder_tuple[0],
                                       tuple_level2[0]), \
                               remain_level2[1:]

        return None, "bad input!"

    @staticmethod
    def is_formula(s: str) -> bool:
        """Checks if the given string is a valid representation of a formula.

        Parameters:
            s: string to check.

        Returns:
            ``True`` if the given string is a valid standard string
            representation of a formula, ``False`` otherwise.
        """
        # Task 1.5
        if Formula.parse_prefix(s)[1] == '':
            return True
        return False

    @staticmethod
    def parse(s: str) -> Formula:
        """Parses the given valid string representation into a formula.

        Parameters:
            s: string to parse.

        Returns:
            A formula whose standard string representation is the given string.
        """
        assert Formula.is_formula(s)
        # Task 1.6
        return Formula.parse_prefix(s)[0]

# Tasks for Chapter 3

    def substitute_variables(
            self, substitution_map: Mapping[str, Formula]) -> Formula:
        """Substitutes in the current formula, each variable `v` that is a key
        in `substitution_map` with the formula `substitution_map[v]`.

        Parameters:
            substitution_map: the mapping defining the substitutions to be
                performed.

        Returns:
            The resulting formula.

        Examples:
            >>> Formula.parse('((p->p)|z)').substitute_variables(
            ...     {'p': Formula.parse('(q&r)')})
            (((q&r)->(q&r))|z)
        """
        for variable in substitution_map:
            assert is_variable(variable)
        # Task 3.3
        if hasattr(self, 'second'):
            return Formula(self.root, self.first.substitute_variables(
                substitution_map), self.second.substitute_variables(
                substitution_map))
        elif hasattr(self, 'first'):
            return Formula(self.root, self.first.substitute_variables(
                substitution_map))
        if is_variable(self.root):
            if self.root in substitution_map:
                return substitution_map[self.root]
        return self

    def substitute_operators(
            self, substitution_map: Mapping[str, Formula]) -> Formula:
        """Substitutes in the current formula, each constant or operator `op`
        that is a key in `substitution_map` with the formula
        `substitution_map[op]` applied to its (zero or one or two) operands,
        where the first operand is used for every occurrence of ``'p'`` in the
        formula and the second for every occurrence of ``'q'``.

        Parameters:
            substitution_map: the mapping defining the substitutions to be
                performed.

        Returns:
            The resulting formula.

        Examples:
            >>> Formula.parse('((x&y)&~z)').substitute_operators(
            ...     {'&': Formula.parse('~(~p|~q)')})
            ~(~~(~x|~y)|~~z)
        """
        for operator in substitution_map:
            assert is_binary(operator) or is_unary(operator) or \
                   is_constant(operator)
            assert substitution_map[operator].variables().issubset({'p', 'q'})
        # Task 3.4
        if hasattr(self, 'second'):
            second_formula = self.second.substitute_operators(substitution_map)
            first_formula = self.first.substitute_operators(substitution_map)
            if self.root not in substitution_map:
                return Formula(self.root, first_formula, second_formula)
            # replacing p and q
            return substitution_map[self.root].substitute_variables({'p':
                                           first_formula, 'q': second_formula})

        elif hasattr(self, 'first'):
            first_formula = self.first.substitute_operators(substitution_map)
            if self.root not in substitution_map:
                return Formula(self.root, first_formula)
            return substitution_map[self.root].substitute_variables \
                ({'p': first_formula})
        if self.root in substitution_map:
            return substitution_map[self.root]
        return self


    def verify_and_not_child_of_or(self, parent: str) -> bool:
        """verify that and is not child of or in formula's tree. Assumes that unary
        ops are pushed down the parse tree
        """
        if hasattr(self, 'second'):
            if parent == '|':
                if self.root == '&':
                    return False
                left = self.first.verify_and_not_child_of_or('|')
                right = self.second.verify_and_not_child_of_or('|')
                return left and right
            else:
                left = self.first.verify_and_not_child_of_or(self.first.root)
                right = self.second.verify_and_not_child_of_or(self.second.root)
                return left and right
        return True

    def verify_or_not_child_of_and(self, parent: str) -> bool:
        """verify that or is not child of and in formula's tree. Assumes that unary
        ops are pushed down the parse tree
        """
        if hasattr(self, 'second'):
            if parent == '&':
                if self.root == '|':
                    return False
                left = self.first.verify_or_not_child_of_and('&')
                right = self.second.verify_or_not_child_of_and('&')
                return left and right
            else:
                left = self.first.verify_or_not_child_of_and(self.first.root)
                right = self.second.verify_or_not_child_of_and(self.second.root)
                return left and right
        return True

    def get_clauses(self) -> List[Tuple[List[str], List[str]]]:
        """For each CNF clause in formula return two lists: pos, neg where they respectively are the literals
        and negated literals within the clause. """
        individual_clauses = list()

        if self.root == '&':
            left = self.first.get_clauses()
            right = self.second.get_clauses()
            individual_clauses.extend(left)
            individual_clauses.extend(right)
            return individual_clauses

        pos = self.pos_literals_consts()
        negs = self.negated_literals_consts()
        clause = tuple((list(pos), list(negs)))
        individual_clauses.append(clause)
        return individual_clauses


    @staticmethod
    def __generate_clause(clause_tuple: Tuple[List[str], List[str]]) -> Formula:
        if len(clause_tuple[POS]) == 0 and len(clause_tuple[NEG]) == 0:
            return Formula('F')

        if len(clause_tuple[NEG]) != 0:
            negs = clause_tuple[NEG]
            fnn = Formula('~', Formula(negs[0]))
            for i in range(1, len(negs)):
                fn = Formula('~', Formula(negs[i]))
                fnn = Formula('|', fnn, fn)
            if len(clause_tuple[POS]) == 0:
                return fnn

        if len(clause_tuple[POS]) != 0:
            pos = clause_tuple[POS]
            fpp =  Formula(pos[0])
            for i in range(1, len(pos)):
                fp = Formula(pos[i])
                fpp = Formula('|', fpp, fp)
            if len(clause_tuple[NEG]) == 0:
                return fpp

        return Formula('|', fpp, fnn)

    @staticmethod
    def generate_formula(clause_list:  List[Tuple[List[str], List[str]]]) -> Formula:

        if len(clause_list) == 0:
            return Formula('T')

        f = Formula.__generate_clause(clause_list[0])
        for i in range(1, len(clause_list)):
            f = Formula('&', f, Formula.__generate_clause(clause_list[i]))
        return f