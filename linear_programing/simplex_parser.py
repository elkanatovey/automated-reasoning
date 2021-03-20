from logic_utils import fresh_variable_name_generator
from predicates.syntax import Formula as smtFormula, Term, is_variable
from propositions.tseitin import to_NNF, NNF_to_DNF
from propositions.syntax import Formula as propositionalFormula


class LP_formula:
    def __init__(self, fol_formula: smtFormula):

        # step 1 - NNF converting ~(=) to != and ~(>=) to <
        self.propositional_formula, self.z2f, self.f2z = fol_formula.propositional_skeleton_mappings()
        self.propositional_formula = to_NNF(self.propositional_formula)
        self.propositional_formula = self.push_negations(self.propositional_formula)


        # step 2 - converting formulas with <, =, !=, >=  to formula only with <=
        propositional_vars = self.propositional_formula.variables()
        for key in propositional_vars:
            self.z2f[key] = self.process_smt_formula(self.z2f[key])

        # step 3 - DNF
        fol_formula = smtFormula.from_propositional_skeleton(self.propositional_formula, self.z2f)
        self.propositional_formula, self.z2f, self.f2z = fol_formula.propositional_skeleton_mappings()
        self.propositional_formula = NNF_to_DNF(self.propositional_formula)

        self.clauses = break_to_clauses(self.propositional_formula)
        self.clauses_count = len(self.clauses)  # counter for number of clauses

    def get_z2f(self):
        return self.z2f

    def clauses_left(self):
        return self.clauses_count

    def get_clause(self):
        """
        return a clause and deduce clauses_left by 1
        :return:
        """
        self.clauses_count -= 1
        return self.clauses[self.clauses_count]

    def push_negations(self, formula: propositionalFormula) -> propositionalFormula:
        """
        switch negation on formula in a new formula and give it a new propositional variable

        negation on >= becomes <  ('GS' becomes 'K')
        negation on = becomes !=  ('S' becomes 'LS')

        :param formula:
        :return:
        """
        if formula.root == '~':
            var = formula.first.root
            fol_formula = self.z2f[var]
            operator = fol_formula.root
            if operator == 'S':
                new_formula = smtFormula('LS', [fol_formula.arguments[0], fol_formula.arguments[1]])
            else:
                assert operator == 'GS'
                new_formula = smtFormula('K', [fol_formula.arguments[0], fol_formula.arguments[1]])

            if new_formula not in self.f2z:
                #   if new formula wasn't added yet
                new_z = next(fresh_variable_name_generator)
                f_as_proposition = propositionalFormula(new_z)
                self.z2f[new_z] = new_formula
                self.f2z[new_formula] = f_as_proposition
            else:
                f_as_proposition = propositionalFormula(self.f2z[new_formula].root)

            return f_as_proposition

        elif formula.root == '&' or formula.root == '|':
            return propositionalFormula(formula.root, self.push_negations(formula.first),
                                           self.push_negations(formula.second))
        else:
            #   case variable/const
            return formula



    def process_smt_formula(self, formula: smtFormula):
        """
        convert an smt formula to the form of - A1X1 + A2X2 + A3X3 + .... $$ C
        when $$ can be:
            S (shave, equal)
            LS (lo shave, not equal)
            GS (gadol shave, bigger/equal)
            K (katan, smaller)
        :param formula:
        :return:
        """

        # processing an NNF Formula

        term1 = formula.arguments[0]
        term2 = formula.arguments[1]  # always should exists

        left_consts = get_all_const(term1)
        right_consts = get_all_const(term2)

        c = 0  # compute constant C on the right side of formula
        for x in left_consts:
            c -= x
        for x in right_consts:
            c += x

        left_vars = get_all_vars(term1)
        right_vars = get_all_vars(term2)

        # left side of the formula
        # computing dict of vector a of constants multiplied by vector x of vars - dict type {str:float}
        aTx = {k: left_vars.get(k, 0) - right_vars.get(k, 0) for k in set(left_vars) | set(right_vars)}


        if formula.root == 'GS':  # case >= (operator 'GS') becomes <= (operator 'KS') after multiplication by -1
            c *= -1
            aTx = {k: -1 * aTx.get(k, 0) for k in set(aTx)}

            new_formula = self.create_formula(c, aTx, 'KS')

        elif formula.root == 'K':   # case <
            aTx['y'] = 1
            new_formula = self.create_formula(c, aTx, 'KS')

        elif formula.root == 'S':   # case =
            formula1 = self.create_formula(c, aTx, 'KS')

            c *= -1
            aTx = {k: -1 * aTx.get(k, 0) for k in set(aTx)}
            formula2 = self.create_formula(c, aTx, 'KS')
            new_formula = smtFormula('&', formula1, formula2)

        else:  # case !=
            assert formula.root == 'LS'
            aTx['y'] = 1
            formula1 = self.create_formula(c, aTx, 'KS')

            c *= -1
            aTx = {k: -1 * aTx.get(k, 0) for k in set(aTx)}
            aTx['y'] = 1
            formula2 = self.create_formula(c, aTx, 'KS')
            new_formula = smtFormula('|', formula1, formula2)

        return new_formula

    def create_formula(self, c, aTx, relation):
        all_vars = list(aTx.keys())
        aTx_term = Term('0')
        for i in range(len(all_vars)):
            var = all_vars[i]
            var_term = Term(var)
            if aTx[var] > 0:
                coeff_term = Term(str(aTx[var]))
                aTx_term = Term("plus", [aTx_term, Term("multi", [coeff_term, var_term])])
            elif aTx[var] < 0:
                coeff_term = Term(str(-1 * aTx[var]))
                aTx_term = Term("minus", [aTx_term, Term("multi", [coeff_term, var_term])])

        if c < 0:
            c_term = Term('minus', [Term('0'), Term(str(-1 * c))])
        else:
            c_term = Term(str(c))

        return smtFormula(relation, [aTx_term, c_term])


def break_to_clauses(formula: propositionalFormula) :
    """
    breaks the dnf formula into clauses

    return: list of lists, where each list represents a clause and hold the vars of the clause (list of strings)
    """
    clauses_lst = []    # list of lists
    if (formula.root == '|'):
        if(formula.first.root == '&'):
            clauses_lst.append(parse_clause(formula.first))
        elif(formula.first.root == '|'):
            clauses_lst += break_to_clauses(formula.first)
        else:
            # variable case
            clauses_lst.append([formula.first.root])

        if (formula.second.root == '&'):
            clauses_lst.append(parse_clause(formula.second))
        elif (formula.second.root == '|'):
            clauses_lst += break_to_clauses(formula.second)
        else:
            # variable case
            clauses_lst.append([formula.second.root])

    elif formula.root == '&':
        clauses_lst.append(parse_clause(formula))

    else:
        # case root is a variable
        clauses_lst.append([formula.root])

    return clauses_lst

def parse_clause(clause: propositionalFormula) -> list:
    """
    gets a clause of conjunctions and return its variables
    :param clause:
    :return:
    """
    if clause.root != '&':
        return [clause.root]
    else:
        return parse_clause(clause.first) + parse_clause(clause.second)

def parse_string(s: str):
    """
    return a float represented by the string s if s is a number.
    else,
    return the string itself
    :param s:
    :return:
    """
    try:
        x = float(s)
    except:
        # not a number
        return s
    return x


def get_all_const(term: Term) -> list:
    """
    return a list with all the consts (positive and negative numbers) that appears in the term

    for example  ->    -(1-2x) + 5   will return [-1,5]

    :param term:
    :return:
    """
    ls = []
    if type(parse_string(term.root)) is float and parse_string(term.root) != 0:  # case term is number
        return [parse_string(term.root)]

    elif term.root == 'plus':
        ls.extend(get_all_const(term.arguments[0]))  # first arg
        ls.extend(get_all_const(term.arguments[1]))  # second arg

    elif term.root == 'minus':
        ls = get_all_const(term.arguments[1])  # second arg
        for i in range(len(ls)):
            ls[i] = ls[i] * -1

        ls.extend(get_all_const(term.arguments[0]))  # first arg

    return ls


def get_all_vars(term) -> {str: float}:
    """
    return a dictionary of the vars as keys, and their number of appearances as values

    for example  ->    -(1-2x) + 5y -x   will return {'y' : 5, 'x': 1}

    :param term: Term or smtFormula
    :return:
    """
    dic = {}

    if is_variable(term.root):  # case term is number
        return {parse_string(term.root): 1}

    if term.root == 'multi':
        const = parse_string(term.arguments[0].root)
        assert type(const) == float

        new_dic = get_all_vars(term.arguments[1])
        for key in new_dic:
            new_dic[key] *= const
        dic = {k: dic.get(k, 0) + new_dic.get(k, 0) for k in set(dic) | set(new_dic)}

    elif term.root == 'plus':
        new_dic = get_all_vars(term.arguments[0])
        dic = {k: dic.get(k, 0) + new_dic.get(k, 0) for k in set(dic) | set(new_dic)}
        new_dic = get_all_vars(term.arguments[1])
        dic = {k: dic.get(k, 0) + new_dic.get(k, 0) for k in set(dic) | set(new_dic)}

    elif term.root == 'minus':
        new_dic = get_all_vars(term.arguments[1])
        for key in new_dic:
            new_dic[key] *= -1
        dic = {k: dic.get(k, 0) + new_dic.get(k, 0) for k in set(dic) | set(new_dic)}

        new_dic = get_all_vars(term.arguments[0])
        dic = {k: dic.get(k, 0) + new_dic.get(k, 0) for k in set(dic) | set(new_dic)}

    return dic