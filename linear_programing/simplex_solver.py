import numpy as np
import copy
import operator as op
from functools import reduce
from predicates.syntax import *
from linear_programing.simplex_parser import LP_formula, get_all_vars, get_all_const

UNBOUNDED = "UNBOUNDED"
TERMINATION = "TERMINATION"
NO_SOLUTION = "NO_SOLUTION"

EPSILON = 0.00000000001
MAXIMUM_NUM_OF_ETA_MAT = 10


def run_simplex(formula: str):
    """
    The main function that handles with the first order logic formula, parse it, and run the simplex algorithm
    :param formula:
    :return:
    """
    formula = Formula.parse(formula)
    assert formula is not None

    lp_parser = LP_formula(formula)
    z2f = lp_parser.get_z2f()  # dictionary of {variable: formula}

    is_sat = False

    while (lp_parser.clauses_left() > 0):
        variables_dictionaries = []  # list of dictionaries, one for each formula
        Cs_list = []  # list of the different c's (one for each formula), keep same order as variables_dictionaries
        clause = lp_parser.get_clause()
        for var in clause:
            formula = z2f[var]
            variables_dict = get_all_vars(formula.arguments[0])

            if (formula.arguments[1].root == 'minus'):
                c = float(formula.arguments[1].arguments[1].root) * -1
            else:
                c = float(formula.arguments[1].root)

            if variables_dict in variables_dictionaries:
                index = variables_dictionaries.index(variables_dict)
                if c == Cs_list[index]:
                    continue
            # case formula not in list yet
            variables_dictionaries.append(copy.deepcopy(variables_dict))
            Cs_list.append(c)

        lp_solver = LP_Solver(variables_dictionaries, Cs_list, False)

        if np.any(np.array(Cs_list) < 0):
            # case there was an auxiliary problem
            if lp_solver.final_scores == UNBOUNDED:
                is_sat = False
            elif lp_solver.final_scores['x0'] != 0:
                is_sat = False
            elif 'y' not in lp_solver.final_scores:  # case x0 = 0. if there is no 'y', we found feasible solution
                is_sat = True
                break

        else:
            # case there was no auxiliary problem
            answer = lp_solver.revised_simplex()
            if answer == UNBOUNDED:
                is_sat = True
                break
            elif 'y' in answer:
                if answer['y'] <= 0:
                    is_sat = False
                else:
                    is_sat = True
                    break
            else:
                # case no 'y' and not unbounded
                is_sat = True
                break
    if is_sat:
        print('SAT')
    else:
        print('UNSAT')


class LP_Solver:
    """
    syntax:
        0. TQ  ---------  only '>=' ('GS')  and '=' ('S') relations are allowed
        1. multiplication looks like this mult(const, X) - const at the first argument (term. not a formula)
        2. minus always has 2 arguments. even in case of -x we will use minus(0,x)
        3. don't use variable 'y' or 'x0' (saved names)
    """

    def __init__(self, variables_dictionaries, Cs_list, is_auxiliary_problem):

        self.final_scores = {}
        self.auxiliary_problem = None
        if not is_auxiliary_problem and np.any(np.array(Cs_list) < 0):
            aux_dicts = []
            for dict in variables_dictionaries:
                aux_dict = copy.deepcopy(dict)
                aux_dict['x0'] = -1
                aux_dicts.append(aux_dict)
            self.auxiliary_problem = LP_Solver(aux_dicts, Cs_list, True)
            self.final_scores = self.auxiliary_problem.revised_simplex()
            if self.final_scores == UNBOUNDED or self.final_scores['x0'] != 0:
                return



        variables_set = set()  # keep all variables_set in a specific order
        num_of_formulas = len(variables_dictionaries)
        for i in range(0, num_of_formulas):
            variables_set = variables_set | set(variables_dictionaries[i].keys())
        num_of_variables = len(variables_set)

        self.variables = sorted(list(variables_set))
        self.An = np.zeros((num_of_formulas, num_of_variables))
        self.X_N = np.arange(1, num_of_variables + 1)
        self.X_B = np.arange(num_of_variables + 1, num_of_variables + 1 + num_of_formulas)
        self.C_N = np.zeros(num_of_variables)
        self.C_B = np.zeros(len(self.X_B), dtype=np.float64)
        self.Xb_star = np.zeros(num_of_formulas)


        self.num_2_var = {}  # dictionary that holds Xi -> variable. for example{'x4':'z'}
        for i in range(num_of_variables):
            self.num_2_var[i + 1] = self.variables[i]
        for i in range(num_of_variables, num_of_variables + len(self.X_B)):
            self.num_2_var[i + 1] = 'x' + str(i + 1)

        if is_auxiliary_problem:
            self.C_N[self.variables.index('x0')] = -1

        if self.final_scores == {}:
            #   case there was no need for auxiliary
            for i in range(0, num_of_formulas):
                coefficients = []  # row of the matrix An
                for j in range(num_of_variables):
                    var = self.variables[j]
                    if (var in variables_dictionaries[i]):  # if variable not in dict, put 0 in the row in matrix
                        coefficients.append(variables_dictionaries[i][var])
                    else:
                        coefficients.append(0)
                self.An[i] = np.array(coefficients)
                self.Xb_star[i] = Cs_list[i]

            # initialize - default values
            self.C_B = np.zeros(len(self.X_B), dtype=np.float64)
            self.B = np.identity(len(self.X_B), dtype=np.float64)

            self.eta_matrices = [(0, np.array(self.B[0]))]  # keep the eta matrices as tuples (col_num,col)
        else:
            assert self.auxiliary_problem is not None

            # case there was auxiliary problem. need to use its dictionary
            number_of_x0 = self.auxiliary_problem.variables.index('x0') + 1
            self.Xb_star = self.auxiliary_problem.Xb_star
            self.X_B = self.auxiliary_problem.X_B

            if number_of_x0 in self.auxiliary_problem.X_N:
                index_of_x0 = np.where(self.auxiliary_problem.X_N == number_of_x0)[0][0]
                self.An = np.delete(np.array(self.auxiliary_problem.An), index_of_x0, 1)
                self.X_N = np.delete(np.array(self.auxiliary_problem.X_N), index_of_x0)
            else:
                assert False, "x0 is in basic, but shouldn't be"


            if 'y' in self.variables:
                number_of_y = self.variables.index('y') + 1
                if number_of_y in self.X_N:
                    index_of_y = np.where(self.X_N == number_of_y)[0]
                    self.C_N[index_of_y] = 1
                else:
                    index_of_y = np.where(self.X_B == number_of_y)[0]
                    self.C_B[index_of_y] = 1
            else:
                self.C_N[0] = 1   # fake objective function

            self.B = self.auxiliary_problem.B
            self.eta_matrices = self.auxiliary_problem.eta_matrices


        self.iterations_before_bland = self.ncr(len(self.X_N) + len(self.X_B), len(self.Xb_star))
        self.iters = 0
        self.t = -1
        self.d = np.array([], dtype=np.float64)
        self.bland_on = False
        self.is_auxilary_problem = is_auxiliary_problem


        # self.X_B = np.array([4, 5, 6], dtype=np.float64)
        # self.X_N = np.array([1, 2, 3], dtype=np.float64)
        # self.An = np.array([[1, 1, -1], [1, 2, 2], [1, 1, -4]], dtype=np.float64)
        # self.C_N = np.array([-1, 0, 0], dtype=np.float64)
        # self.Xb_star = np.array([-1, -6, 2], dtype=np.float64)

        # self.X_B = np.array([5, 6, 7], dtype=np.float64)
        # self.X_N = np.array([1, 2, 3, 4], dtype=np.float64)
        # self.An = np.array([[3, 2, 1, 2], [1, 1, 1, 1], [4, 3, 3, 4]], dtype=np.float64)
        # self.C_N = np.array([19, 13, 12, 17], dtype=np.float64)
        # self.Xb_star = np.array([225, 117, 420], dtype=np.float64)

    def ncr(self, n, r):
        r = min(r, n - r)
        numer = reduce(op.mul, range(n, n - r, -1), 1)
        denom = reduce(op.mul, range(1, r + 1), 1)
        return numer // denom

    def revised_simplex(self):

        while (True):

            if (self.iters >= self.iterations_before_bland):
                self.bland_on = True

            leaving_ind, entering_ind = 0, 0
            entering_index_num_of_tries = 0  # for numerical stability on the diagonal of eta matrices
            entering_indexes_already_tried = []
            while (True):

                # the entering variable and it's column index in the table
                entering_ind, entering_indexes_already_tried, entering_candidates_indexes = \
                    self.BTRAN(entering_index_num_of_tries, entering_indexes_already_tried)

                if entering_candidates_indexes == "FINAL":
                    leaving_ind = np.where(self.X_B == self.variables.index('x0') + 1)[0][0]
                    self.t = 0
                    self.swap_and_update(entering_ind, leaving_ind)
                    return self.terminate(TERMINATION)


                if (entering_ind == TERMINATION):
                    return self.terminate(entering_ind)

                leaving_ind = self.FTRAN(entering_ind)
                if (leaving_ind == TERMINATION or leaving_ind == UNBOUNDED):
                    return self.terminate(leaving_ind)

                entering_index_num_of_tries += 1

                # vec d will be in the eta matrix in column leaving_ind, so need to check that d[leaving_ind] is not smaller than EPSILON
                if (self.d[leaving_ind] > EPSILON or entering_index_num_of_tries == len(entering_candidates_indexes)):
                    break

            if leaving_ind == TERMINATION or entering_ind == TERMINATION or leaving_ind == UNBOUNDED:
                break

            self.swap_and_update(entering_ind, leaving_ind)
            self.iters += 1

    def BTRAN(self, entering_index_num_of_tries, entering_indexes_already_tried):
        y = self.compute_y(self.C_B)
        product = np.dot(y, self.An)

        if (self.is_auxilary_problem == True and self.iters == 0):
            entering_index = self.variables.index('x0')
            entering_candidates_indexes = [entering_index]  # the only candidate
            return entering_index, entering_candidates_indexes, entering_candidates_indexes

        elif (self.bland_on == False):
            #   Dantzig's rule

            diff = self.C_N - product

            if np.max(diff) <= EPSILON:
                if self.is_auxilary_problem:
                    number = self.variables.index('x0') + 1
                    if np.max(diff) <= 0 and number in self.X_B and self.Xb_star[np.where(self.X_B == number)[0]] == 0:
                        index = np.argmax(diff)
                        return index, "FINAL", "FINAL"

                return TERMINATION, None, None



            entering_index_try = sorted(diff)[len(self.C_N) - 1 - entering_index_num_of_tries]

            entering_candidates_indexes = np.where(diff == entering_index_try)[0]
            # maybe there is more than 1 index that equals to the i-th biggest value

            entering_index = -1

            for i in range(len(entering_candidates_indexes)):  # looking for one that wasn't tried yet
                if entering_candidates_indexes[i] not in entering_indexes_already_tried:
                    entering_index = entering_candidates_indexes[i]
                    break

            assert entering_index != -1

        else:
            #   Bland's rule
            entering_candidates_indexes = np.where(product < self.C_N)[0]
            if len(entering_candidates_indexes) == 0:  # Terminate
                return TERMINATION, None, None

            if len(entering_candidates_indexes) <= entering_index_num_of_tries:
                # case already tried all possible options for entering var - take minimum var (Bland's)
                entering_index = sorted(entering_candidates_indexes)[0]
            else:
                entering_index = sorted(entering_candidates_indexes)[entering_index_num_of_tries]

        entering_indexes_already_tried.append(entering_index)

        return entering_index, entering_indexes_already_tried, entering_candidates_indexes

    def FTRAN(self, entering_var):
        self.d = self.compute_d(self.An[:, entering_var])

        if np.all(self.d < 0) and (not np.any(self.Xb_star < 0)):
            return UNBOUNDED

        ts = np.divide(self.Xb_star, self.d)

        # find largest possible t
        if not self.is_auxilary_problem or self.iters != 0:
            ts = np.nan_to_num(ts, nan=np.inf)
            ts[ts <= 0] = np.inf
            best_t_ind = np.argmin(ts)
            self.t = np.min(ts)
        else:
            best_t_ind = np.argmax(ts)
            self.t = ts[best_t_ind]

        diff = self.Xb_star - self.t * self.d

        if np.any(diff < -1 * EPSILON):
            return UNBOUNDED

        return best_t_ind

    def swap_and_update(self, entering_ind, leaving_ind):
        self.C_B[leaving_ind], self.C_N[entering_ind] = self.C_N[entering_ind], self.C_B[leaving_ind]
        self.X_B[leaving_ind], self.X_N[entering_ind] = self.X_N[entering_ind], self.X_B[leaving_ind]

        temp = copy.deepcopy(self.B[:, leaving_ind])
        self.B[:, leaving_ind] = self.An[:, entering_ind]
        self.An[:, entering_ind] = temp


        self.Xb_star = self.Xb_star - self.d * self.t
        self.Xb_star[leaving_ind] = self.t

        # updating Eta matrices list
        self.eta_matrices.append((leaving_ind, copy.deepcopy(self.d)))

        if (len(self.eta_matrices) > MAXIMUM_NUM_OF_ETA_MAT):
            self.lu_factorization()

    def terminate(self, terminate_reason):
        """
            Terminate - if it got an optimal solution - print the results
        """

        if (terminate_reason == UNBOUNDED):
            return UNBOUNDED
        elif (terminate_reason == TERMINATION):
            final_dict = {}
            objective_function = "The objective function is: "
            sum = 0
            for i in range(len(self.Xb_star)):
                objective_function += str(self.C_B[i]) + " * " + str(self.Xb_star[i])
                if (i != len(self.Xb_star) - 1):
                    objective_function += " + "
                sum += (self.Xb_star[i] * self.C_B[i])
            objective_function += ' = ' + str(sum)
            print(objective_function)

            optimal_solution = "The optimal solution is: "
            for i in range(1, len(self.X_N) + len(self.X_B) + 1):
                if (i in self.X_N):
                    final_dict[self.num_2_var[i]] = 0
                    optimal_solution += (self.num_2_var[i] + " = 0, ")
                else:
                    final_dict[self.num_2_var[i]] = self.Xb_star[np.where(i == self.X_B)[0][0]]
                    optimal_solution += (
                                self.num_2_var[i] + " = " + str(self.Xb_star[np.where(i == self.X_B)[0][0]]) + ", ")
            print(optimal_solution[0:-2])
            return final_dict

    # compute vectors y and d in BTRAN and FTRAN according to the eta matrices
    def compute_y(self, vec):
        answer_vec = np.zeros(len(vec), dtype=np.float64)
        for i in range(len(self.eta_matrices) - 1, -1, -1):
            col_num, col = self.eta_matrices[i][0], self.eta_matrices[i][1]
            answer_vec = np.array(vec)
            answer_vec[col_num] = 0
            answer_vec[col_num] = (vec[col_num] - np.dot(answer_vec, col)) / col[col_num]
            vec = np.array(answer_vec)

        return answer_vec

    # compute vector d in FTRAN according to the eta matrices
    def compute_d(self, vec):
        answer_vec = np.zeros(len(vec), dtype=np.float64)
        for i in range(len(self.eta_matrices)):
            col_num, col = self.eta_matrices[i][0], self.eta_matrices[i][1]
            answer_vec[col_num] = vec[col_num] / col[col_num]
            for j in range(len(vec)):
                if (j != col_num):
                    answer_vec[j] = (vec[j] - (answer_vec[col_num] * col[j]))
            vec = np.array(answer_vec)
        return answer_vec

    def lu_factorization(self):
        """
        replace the eta matrices list by the l-u factorization matrices of matrix B
        """
        self.eta_matrices = []
        mat = np.array(self.B, dtype=np.float64)

        # compute L matrices
        for i in range(len(self.B)):
            l_mat = np.identity(len(self.B), dtype=np.float64)
            for j in range(i + 1, len(self.B)):
                multiply = -1 * (mat[j, i] / mat[i, i])
                mat[j] = mat[j] + mat[i] * multiply
                l_mat[j] = l_mat[j] + l_mat[i] * multiply

            self.eta_matrices.append(self.eta_matrix_to_list(np.linalg.inv(l_mat)))

        # compute U matrices
        for i in range(len(mat) - 1, -1, -1):
            u_mat = np.identity(len(mat))
            u_mat[:, i] = mat[:, i]
            self.eta_matrices.append(self.eta_matrix_to_list(u_mat))

    def eta_matrix_to_list(self, mat):
        """
        return a compact presentation of the eta mat - [col_num, col]
        """
        identity = np.identity(len(mat))
        for i in range(len(mat)):
            if (np.all(identity[:, i] == mat[:, i])):
                continue
            else:
                return [i, mat[:, i]]

        return [0, identity[:, 0]]  # case of identity mat
