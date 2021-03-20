from typing import Union

from logic_utils import fresh_variable_name_generator
from propositions.syntax import Formula, is_variable, is_constant, is_unary, is_binary


def to_NNF(formula: Formula) -> Formula:
    '''
    return formula in NNF form
    :param formula:
    :return: formula in NNF form
    '''
    return to_NNF_push_negations(to_NNF_eliminate_IFF_and_IF(formula))


def to_NNF_eliminate_IFF_and_IF(formula: Formula) -> Formula:
    '''
    Eliminate <-> and -> by:
    a<->b   -->   (a->b)&(b->a)
    a->b   -->   ~a|b
    :param formula:
    :return:
    '''
    return formula.substitute_operators(
        {
         '->': Formula.parse_prefix('~(p&~q)')[0],
         '<->': Formula.parse_prefix('((p&q)|(~p&~q))')[0]
        })


def to_NNF_push_negations(formula: Formula) -> Formula:
    '''
        De Morgan Laws - push negation into clause:
        ~(a&b)  ->  ~a|~b
        ~(a|b)  ->  ~a&~b
        :param formula: formula
        :return: The formula after performing on it De Morgan laws

        ~(~a|b) - >
    '''
    # base case
    if is_variable(formula.root) or is_constant(formula.root):
        return formula

    if is_unary(formula.root):
        child = formula.first
        if is_variable(child.root):
            return formula
        elif is_constant(child.root):
            if child.root == 'T':
                return Formula('F')
            else:
                return Formula('T')
        elif is_unary(child.root):
            return to_NNF_push_negations(child.first)

        else:   #   case: ~(a&b) - child is binary
            l_part = Formula('~', to_NNF_push_negations(child.first))
            r_part = Formula('~', to_NNF_push_negations(child.second))
            if(child.root == '|'):
                return Formula('&', to_NNF_push_negations(l_part), to_NNF_push_negations(r_part))
            elif(child.root == '&'):
                return Formula('|', to_NNF_push_negations(l_part), to_NNF_push_negations(r_part))

    # case binary
    return Formula(formula.root, to_NNF_push_negations(formula.first), to_NNF_push_negations(formula.second))


def create_negs(formulas: list) -> Union[Formula, None]:
    "create disjunction of negation of literals in sent list - if empty return T"
    if len(formulas) == 0:
        return None
    f = Formula('~', Formula(formulas[0]))

    for i in range(1, len(formulas)):
        ff = Formula('~', Formula(formulas[i]))
        f = Formula('|', f, ff)
    return f


def create_pos(formulas: list) -> Union[Formula, None]:
    "create disjunction of literals in sent list - if empty return T"
    if len(formulas) == 0:
        return None
    if len(formulas) > 1 and formulas[0] == 'F':
        formulas.pop(0)
    f = Formula(formulas[0])

    for i in range(1, len(formulas)):
        if formulas[i] == 'F':
            continue
        ff = Formula(formulas[i])
        f = Formula('|', f, ff)
    return f


def preprocess_clauses(formula: Formula) -> Formula:
    if is_binary(formula.root):

        if formula.root == '&':
            l = preprocess_clauses(formula.first)
            r = preprocess_clauses(formula.second)
            if l.root == 'T' or r.root == 'F':
                return r
            if r.root == 'T' or l.root == 'F':
                return l
            processed_f = Formula('&', l, r)
            return processed_f

        # or case
        else:
            l_negs = formula.first.negated_literals_consts()
            l_pos = formula.first.pos_literals_consts()

            r_negs = formula.second.negated_literals_consts()
            r_pos = formula.second.pos_literals_consts()

            negs = l_negs | r_negs
            pos = l_pos | r_pos

            # nonempty intersection means trivial clause
            if negs.intersection(pos):
                return Formula('T')
            if 'F' in negs or 'T' in pos:
                return Formula('T')

            if 'T' in negs:
                negs.discard('T')
                pos.add('F')

            neg_conjunction = create_negs(list(negs))
            pos_conjunction = create_pos(list(pos))

            if neg_conjunction is None and pos_conjunction is None:
                return Formula('F')
            if neg_conjunction is None:
                return pos_conjunction
            if pos_conjunction is None:
                return neg_conjunction
            if pos_conjunction.root == 'F':
                return neg_conjunction

            return Formula('|', pos_conjunction, neg_conjunction)

    return formula


def NNF_to_CNF(formula: Formula) -> Formula:
    '''

    :param formula: an NNF formula
    :return:
    '''
    # base/unary case
    if is_variable(formula.root) or is_constant(formula.root) or is_unary(formula.root):
        return formula

    if formula.root == '|':
        child_l = NNF_to_CNF(formula.first)
        child_r = NNF_to_CNF(formula.second)
        if child_l.root == '&' and child_r.root == '&':
            a = NNF_to_CNF(child_l.first)
            b = NNF_to_CNF(child_l.second)
            c = NNF_to_CNF(child_r.first)
            d = NNF_to_CNF(child_r.second)
            ac = NNF_to_CNF(Formula('|', a, c))
            ad = NNF_to_CNF(Formula('|', a, d))
            bc = NNF_to_CNF(Formula('|', b, c))
            bd = NNF_to_CNF(Formula('|', b, d))

            left = Formula('&', ac, ad)
            right = Formula('&', bc,bd)
            return Formula('&', left, right)
        elif child_l.root == '&':
            a = NNF_to_CNF(child_l.first)
            b = NNF_to_CNF(child_l.second)
            c = child_r
            left = NNF_to_CNF(Formula('|', a, c))
            right = NNF_to_CNF(Formula('|', b, c))


            return Formula('&', left, right)
        elif child_r.root == '&':
            a = NNF_to_CNF(child_r.first)
            b = NNF_to_CNF(child_r.second)
            c = child_l
            left = NNF_to_CNF(Formula('|', a, c))
            right = NNF_to_CNF(Formula('|', b, c))

            return Formula('&', left, right)
        else:
            return Formula('|', child_l, child_r)

    elif formula.root == '&':
        return Formula('&', NNF_to_CNF(formula.first), NNF_to_CNF(formula.second))
    else:
        assert False

def NNF_to_DNF(formula: Formula) -> Formula:
    '''

    :param formula: an NNF formula
    :return:
    '''
    # base/unary case
    if is_variable(formula.root) or is_constant(formula.root) or is_unary(formula.root):
        return formula

    if formula.root == '&':
        child_l = NNF_to_DNF(formula.first)
        child_r = NNF_to_DNF(formula.second)
        if child_l.root == '|' and child_r.root == '|':
            a = NNF_to_DNF(child_l.first)
            b = NNF_to_DNF(child_l.second)
            c = NNF_to_DNF(child_r.first)
            d = NNF_to_DNF(child_r.second)
            ac = NNF_to_DNF(Formula('&', a, c))
            ad = NNF_to_DNF(Formula('&', a, d))
            bc = NNF_to_DNF(Formula('&', b, c))
            bd = NNF_to_DNF(Formula('&', b, d))

            left = Formula('|', ac, ad)
            right = Formula('|', bc,bd)
            return Formula('|', left, right)
        elif child_l.root == '|':
            a = NNF_to_DNF(child_l.first)
            b = NNF_to_DNF(child_l.second)
            c = child_r
            left = NNF_to_DNF(Formula('&', a, c))
            right = NNF_to_DNF(Formula('&', b, c))
            return Formula('|', left, right)

        elif child_r.root == '|':
            a = NNF_to_DNF(child_r.first)
            b = NNF_to_DNF(child_r.second)
            c = child_l
            left = NNF_to_DNF(Formula('&', a, c))
            right = NNF_to_DNF(Formula('&', b, c))

            return Formula('|', left, right)
        else:
            return Formula('&', child_l, child_r)

    elif formula.root == '|':
        return Formula('|', NNF_to_DNF(formula.first), NNF_to_DNF(formula.second))
    else:
        assert False

def to_tseitin_step1(formula: Formula) -> list:
    """ return a list of all subformulas reformulated as iff tseitin reps
    """
    representatives = []

    # base case
    if is_variable(formula.root) or is_constant(formula.root):
        return representatives

    current_z = next(fresh_variable_name_generator)
    if is_unary(formula.root):
        child_tseitin = to_tseitin_step1(formula.first)

        if len(child_tseitin) == 0:
            new_representative = Formula('<->', Formula(current_z), formula)  #z<->~q
            representatives.append(new_representative)
            return representatives

        new_representative = Formula('<->', Formula(current_z), Formula('~', child_tseitin[0].first))
        representatives.append(new_representative)
        representatives.extend(child_tseitin)
        return representatives

    if is_binary(formula.root):
        l_child_tseitin = to_tseitin_step1(formula.first)
        r_child_tseitin = to_tseitin_step1(formula.second)

        if len(l_child_tseitin) == 0:
            l_rep = formula.first
        else:
            l_rep = l_child_tseitin[0].first

        if len(r_child_tseitin) == 0:
            r_rep = formula.second
        else:
            r_rep = r_child_tseitin[0].first

        repped_formula = Formula(formula.root, l_rep, r_rep)
        new_representative = Formula('<->', Formula(current_z), repped_formula)
        representatives.append(new_representative)

        representatives.extend(l_child_tseitin)
        representatives.extend(r_child_tseitin)
        return representatives


def to_tseitin_step2(formulas_list: list) -> Formula:
    """return full tseitin formula before cnf, if literal returns none"""
    if(len(formulas_list)==0):
        return None
    formula = formulas_list[0].first
    for i in range(len(formulas_list)):
        formula = Formula('&', formula,  NNF_to_CNF(to_NNF(formulas_list[i])))
    return formula


def to_tseitin(formula: Formula) -> Formula:
    """ receive formula, return tseitin transformation of formula before preproccessing"""
    f_list = to_tseitin_step1(formula)
    f = to_tseitin_step2(f_list)
    return f