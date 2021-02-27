import numpy as np
import copy



class LP_Solver:

    def __init__(self):

        # better to hold vars as integers (in Bland's rule we need to choose smallest)
        self.X_B = np.array([5, 6, 7])
        self.X_N = np.array([1, 2, 3, 4])

        self.B = np.array([[1, 0, 0], [0, 1, 0], [0, 0, 1]])
        self.An = np.array([[3, 2, 1, 2], [1, 1, 1, 1], [4, 3, 3, 4]])

        self.C_B = np.array([0, 0, 0])
        self.C_N = np.array([19, 13, 12, 17])
        self.Xb_star = np.array([225, 117, 420])



    def revised_simplex(self):

        # termination - got to optimal solution
        if all(x <= 0 for x in self.An[-1, :]) and all(y <= 0 for y in self.B[-1, :]):
            pass

        # the entering variable and it's column index in the table
        entering_var, entering_index = self.BTRAN()
        # entering_index = 2
        leaving_var, leaving_ind, t, d = self.FTRAN(entering_index)

        self.swap_and_update(entering_index, leaving_ind, t, d)


    def BTRAN(self):
        y = np.dot(self.C_B, np.linalg.inv(self.B))
        product = np.dot(y, self.An)

        entering_candidates_indexes = np.where(product < self.C_N)[0]
        if(len(entering_candidates_indexes) == 0):    # Terminate ?
            pass

        # Bland's rule
        return min(self.X_N[entering_candidates_indexes]), np.argmin(self.X_N[entering_candidates_indexes])


    def FTRAN(self, entering_var):
        d = np.dot(np.linalg.inv(self.B), self.An[:, entering_var])
        print(d)


        # find largest possible t
        ts = self.Xb_star / d
        ind_t, t = -1, -1
        for i in range(len(ts)):
            if(ts[i] == np.inf):    # case 0 in d (no t)
                continue
            cur_t = ts[i]
            for j in range(len(ts)):
                if(d[j] * cur_t > self.Xb_star[j]):
                    break
                if j == len(ts) - 1:
                    if(cur_t > t):
                        t = cur_t
                        ind_t = i

        return self.X_B[ind_t], ind_t, t, d


    def swap_and_update(self, entering_ind, leaving_ind, t, d):

        self.X_B[leaving_ind], self.X_N[entering_ind] = self.X_N[entering_ind], self.X_B[leaving_ind]
        self.C_B[leaving_ind], self.C_N[entering_ind] = self.C_N[entering_ind], self.C_B[leaving_ind]

        temp = copy.deepcopy(self.B[:, leaving_ind])
        self.B[:,leaving_ind] = self.An[:, entering_ind]
        self.An[:, entering_ind] = temp

        # updating Xb_star
        Xb_star_new = np.array([self.Xb_star[i] - d[i] * t for i in range(len(d))])
        Xb_star_new[leaving_ind] = t
        print(Xb_star_new)

        print(self.B)
        print(self.An)



s = LP_Solver()
s.revised_simplex()