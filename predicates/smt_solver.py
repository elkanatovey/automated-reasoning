from predicates.syntax import Formula


def get_boolean_abstraction(formula: Formula):
    """returns tuple of boolean abstraction of first order formula
    and substitution map for reconstruction in [boolean abstraction, substitution_map] form.
    See formula.propositional_skeleton() for details"""
    return formula.propositional_skeleton()

def get_sat_l0():
    pass