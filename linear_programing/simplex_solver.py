import numpy as np
import copy
import operator as op
from functools import reduce

UNBOUNDED = "UNBOUNDED"
TERMINATION = "TERMINATION"

EPSILON = 0.00000000001
MAXIMUM_NUM_OF_ETA_MAT = 10

class LP_Solver:

    def __init__(self):

        # better to hold vars as integers (in Bland's rule we need to choose smallest)
        # self.X_B = np.array([4, 5, 6], dtype=np.float64)
        # self.X_N = np.array([1, 2, 3], dtype=np.float64)
        # self.An = np.array([[1, 1, 2], [2, 0, 3], [2, 1, 3]], dtype=np.float64)
        # self.C_N = np.array([3, 2, 4], dtype=np.float64)
        # self.Xb_star = np.array([4, 5, 7], dtype=np.float64)

        self.X_B = np.array([4, 5, 6], dtype=np.float64)
        self.X_N = np.array([1, 2, 3], dtype=np.float64)
        self.An = np.array([[1, 1, -1], [1, 2, 2], [1, 1, -4]], dtype=np.float64)
        self.C_N = np.array([-1, 0, 0], dtype=np.float64)
        self.Xb_star = np.array([-1, -6, 2], dtype=np.float64)


        # self.X_B = np.array([5, 6, 7], dtype=np.float64)
        # self.X_N = np.array([1, 2, 3, 4], dtype=np.float64)
        # self.An = np.array([[3, 2, 1, 2], [1, 1, 1, 1], [4, 3, 3, 4]], dtype=np.float64)
        # self.C_N = np.array([19, 13, 12, 17], dtype=np.float64)
        # self.Xb_star = np.array([225, 117, 420], dtype=np.float64)

        self.iterations_before_bland = self.ncr(len(self.X_N) + len(self.X_B), len(self.Xb_star))

        # initialize - default values
        self.C_B = np.zeros(len(self.X_B), dtype=np.float64)
        self.B = np.identity(len(self.X_B), dtype=np.float64)

        self.eta_matrices = [(0, np.array([1, 0, 0]))]  # keep the eta matrices as tuples (col_num,col)

        self.iters = 0
        self.t = -1
        self.d = np.array([], dtype=np.float64)
        self.bland_on = True
        self.auxilary_problem = True

    def ncr(self, n, r):
        r = min(r, n - r)
        numer = reduce(op.mul, range(n, n - r, -1), 1)
        denom = reduce(op.mul, range(1, r + 1), 1)
        return numer // denom

    def revised_simplex(self):

        while (True):

            # print(iters)

            if (self.iters >= self.iterations_before_bland):
                self.bland_on = True

            # termination - got to optimal solution
            if all(x <= 0 for x in self.C_N) and all(y <= 0 for y in self.C_B):
                if(self.auxilary_problem == False):
                    self.terminate(TERMINATION)     # in auxiliary problem the subject function is -X0
                    break

            leaving_ind, entering_ind = 0, 0
            entering_index_num_of_tries = 0  # for numerical stability on the diagonal of eta matrices
            entering_indexes_already_tried = []
            while (True):

                # the entering variable and it's column index in the table
                entering_ind, entering_indexes_already_tried = self.BTRAN(entering_index_num_of_tries,
                                                                          entering_indexes_already_tried)
                if (entering_ind == TERMINATION):
                    self.terminate(entering_ind)
                    break

                leaving_ind = self.FTRAN(entering_ind)
                if (leaving_ind == TERMINATION or leaving_ind == UNBOUNDED):
                    self.terminate(leaving_ind)
                    break

                entering_index_num_of_tries += 1

                # vec d will be in the eta matrix in column leaving_ind, so need to check that d[leaving_ind] is not smaller than EPSILON
                if (self.d[leaving_ind] > EPSILON or entering_index_num_of_tries == len(self.C_N)):
                    break

            if leaving_ind == TERMINATION or entering_ind == TERMINATION or leaving_ind == UNBOUNDED:
                break

            self.swap_and_update(entering_ind, leaving_ind)
            self.iters += 1



    def BTRAN(self, entering_index_num_of_tries, entering_indexes_already_tried):
        y = self.compute_y(self.C_B)
        product = np.dot(y, self.An)

        if(self.auxilary_problem == True and self.iters == 0):
            entering_index = np.argmin(self.Xb_star)

        elif (self.bland_on == False):
            #   Dantzig's rule

            diff = self.C_N - product
            entering_index_try = sorted(diff)[len(self.C_N) - 1 - entering_index_num_of_tries]

            list_of_ind = np.where(diff == entering_index_try)[0]
            # maybe there is more than 1 index that equals to the i-th biggest value

            entering_index = -1

            for i in range(len(list_of_ind)):  # looking for one that wasn't tried yet
                if list_of_ind[i] not in entering_indexes_already_tried:
                    entering_index = list_of_ind[i]
                    entering_indexes_already_tried.append(entering_index)

            assert entering_index != -1

            if np.max(diff) <= 0:
                return TERMINATION, None
        else:
            #   Bland's rule
            entering_candidates_indexes = np.where(product < self.C_N)[0]
            if len(entering_candidates_indexes) == 0:  # Terminate
                return TERMINATION, None

            entering_index = sorted(entering_candidates_indexes)[entering_index_num_of_tries]

        return entering_index, entering_indexes_already_tried

    def FTRAN(self, entering_var):
        self.d = self.compute_d(self.An[:, entering_var])

        # find largest possible t
        ts = np.divide(self.Xb_star, self.d)
        ts[ts < 0] = np.inf
        best_t_ind = np.argmin(ts)
        self.t = np.min(ts)

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

        # updating Xb_star
        self.Xb_star = self.Xb_star - self.d * self.t
        self.Xb_star[leaving_ind] = self.t

        # updating Eta matrices list
        self.eta_matrices.append((leaving_ind, copy.deepcopy(self.d)))

        if(len(self.eta_matrices) > MAXIMUM_NUM_OF_ETA_MAT):
            self.lu_factorization()

    def terminate(self, terminate_reason):
        """
            Terminate - if it got an optimal solution - print the results
        """

        if (terminate_reason == UNBOUNDED):
            print("The problem is unbounded.")
        elif (terminate_reason == TERMINATION):
            objective_function = "The objective function is: "
            sum = 0
            for i in range(len(self.Xb_star)):
                objective_function += str(self.Xb_star[i]) + " * " + str(self.C_B[i])
                if (i != len(self.Xb_star) - 1):
                    objective_function += " + "
                sum += (self.Xb_star[i] * self.C_B[i])
            objective_function += ' = ' + str(sum)
            print(objective_function)

            optimal_solution = "The optimal solution is: "
            for i in range(1, len(self.X_N) + len(self.X_B) + 1):
                if (i in self.X_N):
                    optimal_solution += ("x" + str(i) + " = 0, ")
                else:
                    optimal_solution += ("x" + str(i) + " = " + str(self.Xb_star[np.where(i == self.X_B)[0][0]]) + ", ")
            print(optimal_solution[0:-2])

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

    # compute vectors y and d in BTRAN and FTRAN according to the eta matrices
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
            if(np.all(identity[:, i] == mat[:, i])):
                continue
            else:
                return [i, mat[:, i]]

        return [0, identity[:, 0]]      # case of identity mat



    # def is_triangular(self, matrix):
    #     for i in range(1, len(matrix[0])):
    #         for j in range(i):
    #             if(matrix[i, j] != 0):
    #                 return False
    #     return True

    # # sanity check to check if multiplication of the eta matrices equal B
    # def compute_B(self):
    #     mat = np.identity(len(self.X_B))
    #     for i in range(1, len(self.eta_matrices)):
    #         col_num, col = self.eta_matrices[i][0], self.eta_matrices[i][1]
    #         eta = np.identity(len(self.X_B))
    #         eta[:, col_num] = col
    #         mat = np.dot(mat, eta)
    #     print("mat  " , mat)
    #     print("B  ", self.B)


# a = np.array([1, 2, 3])
# print(sorted(a))
s = LP_Solver()
s.revised_simplex()
