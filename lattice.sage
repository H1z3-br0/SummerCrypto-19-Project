from sage.all import *

class Lattice:
    def __init__(self, basis):
        self.basis = basis.change_ring(ZZ)
        self.F = self.basis.transpose() * self.basis
    
    def rank(self):
        return self.basis.rank()
    
    def gram_matrix(self):
        return self.F

    def embedded_vec(self, coordinate_vec):
        coordinate_vec = vector(ZZ, coordinate_vec)
        return self.basis * coordinate_vec
    
    def bilinear_form(self, x, y):
        x = vector(ZZ, x)
        y = vector(ZZ, y)
        return x.transpose() * self.gram_matrix() * y
    
    def quadratic_form(self, x):
        return self.bilinear_form(x, x)
    
    def determinant(self):
        return self.gram_matrix().determinant()

def LDL(A):
    if A != A.transpose():
        raise ("Matrix's not symmetrical")
    rang = A.nrows()
    L = identity_matrix(RR, rang)
    D = matrix(RR, rang)
    for j in range(0, rang):
        D[j][j] = A[j][j] - sum((L[j][k])**2 * D[k][k] for k in range(j))
        for i in range(j+1, rang):
            L[i][j] = (A[i][j] - sum(L[i][k] * L[j][k] * D[k][k] for k in range(j)))/D[j][j] 
    D = diagonal_matrix(RR, D)
    return L, D
