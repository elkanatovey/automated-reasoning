"""helper functions for different solvers - mainly SMT"""

from propositions.sat_solver import UNSAT_MSG
from propositions.sat_solver import SAT_MSG
from propositions.sat_solver import BACKTRACK_MSG


def sat_backjump_helper(sat_solver, smt_solver, sat_smt_level_mappings, c, jump_level, dpoints_settings):
    """run backjump that arises from SAT solver given conflict clause"""
    original_sat_level = sat_solver.level
    sat_solver.backtrack(c, jump_level)
    smt_solver.t_backtrack(sat_smt_level_mappings[jump_level])
    for i in range(original_sat_level, jump_level, -1):  # @todo may need -1
        if len(dpoints_settings) == sat_smt_level_mappings[i]:
            dpoints_settings.pop()
        del sat_smt_level_mappings[i]


def sat_backjump(sat_solver, smt_solver, sat_smt_level_mappings, conflict_clause, backjump_level,
                            dpoints_settings):
    """run SAT backjump until successful SAT propagation or reach level 0
    - return:
    - (UNSAT_MSG, None) if reached contradiction at level 0
    - (None) if succesfully propagated at some level. All relevant objects modified in place
    """
    flag = False
    while flag is not True:
        sat_backjump_helper(sat_solver, smt_solver, sat_smt_level_mappings, conflict_clause, backjump_level,
                            dpoints_settings)
        conflict_clause, backjump_level = sat_solver.propagate(BACKTRACK_MSG)
        if conflict_clause == UNSAT_MSG:
            return UNSAT_MSG, None
        # propagated succesfully
        elif conflict_clause is True:
            return None

def smt_backjump_helper(sat_solver, dpoints_settings, smt_solver, sat_smt_level_mappings):
    """get clause from t-explain then use clause to backtrack
    - return:
    - (UNSAT_MSG, None) if reached contradiction at level 0
    - (None) if succesfully propagated at some level. All relevant objects modified in place"""
    c = smt_solver.t_explain(dpoints_settings)
    c, jump_level = sat_solver.create_clause_jump_level(c)
    original_sat_level = sat_solver.level
    sat_solver.backtrack(c, jump_level)
    smt_solver.t_backtrack(sat_smt_level_mappings[jump_level])
    for i in range(original_sat_level, jump_level, -1):  # @todo may need -1
        del sat_smt_level_mappings[i]


def smt_backjump(sat_solver, dpoints_settings, smt_solver, sat_smt_level_mappings):
    """run smt backjump (meaning theory contradiction) until successful SAT propagation or reach level 0"""
    flag = False
    while flag is not True:
        smt_backjump_helper(sat_solver, dpoints_settings, smt_solver, sat_smt_level_mappings)
        conflict_clause, backjump_level = sat_solver.propagate(BACKTRACK_MSG)
        if conflict_clause == UNSAT_MSG:
            return UNSAT_MSG, None
        # propagated succesfully
        elif conflict_clause is True:
            return None


def smt_update_sat(sat_solver, fake_decision, assignments, smt_solver, sat_smt_level_mappings, dpoints_settings):
    """run pseudo-decide in sat solver to propagate theory lemmas.
    If fails does SMT backjump.
    If reaches level 0, return unsat"""
    status = sat_solver.t_update(fake_decision, assignments[fake_decision])
    sat_smt_level_mappings[sat_solver.level] = smt_solver.level
    # already set
    if status is True:
        return True
    elif status == fake_decision:

        conflict_clause, backjump_level = sat_solver.propagate(fake_decision)
        if conflict_clause == UNSAT_MSG:
            return UNSAT_MSG, None
        elif conflict_clause is True:
            return True
        else:  # also t-conflict
            if smt_backjump(sat_solver, dpoints_settings, smt_solver, sat_smt_level_mappings) is not None:
                return UNSAT_MSG, None
            return False
    else:
        if smt_backjump(sat_solver, dpoints_settings, smt_solver, sat_smt_level_mappings) is not None:
            return UNSAT_MSG, None
        return False


def smt_run_decide(sat_solver, dpoints_settings, smt_solver, sat_smt_level_mappings):
    """run decide and SAT propagate, decide is chosen by SAT solver"""
    decision_var, _ = sat_solver.decide()
    if decision_var != SAT_MSG:
        setting = sat_solver.assignment_dict[decision_var]
        dpoints_settings.append(tuple([decision_var, setting]))
        smt_solver.level_up()
        sat_smt_level_mappings[sat_solver.level] = smt_solver.level
        conflict_clause, backjump_level = sat_solver.propagate(decision_var)
        if conflict_clause == UNSAT_MSG:
            return UNSAT_MSG, None
        # propagated succesfully
        elif conflict_clause is True:
            return True
        else:  # @todo deal with backtrack here
            if sat_backjump(sat_solver, smt_solver, sat_smt_level_mappings, conflict_clause, backjump_level,
                            dpoints_settings) is not None:
                return UNSAT_MSG, None
