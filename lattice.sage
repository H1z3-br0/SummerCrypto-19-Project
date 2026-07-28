from sage.all import *


class Lattice:
    def __init__(self, basis):
        self.basis = basis.change_ring(ZZ)
        self.F = self.basis.transpose() * self.basis
        self._rank = self.basis.rank()
        self._det = None
        self._ldl = None

    def rank(self):
        return self._rank

    def gram_matrix(self):
        return self.F

    def embedded_vec(self, coordinate_vec):
        return self.basis * vector(ZZ, coordinate_vec)

    def bilinear_form(self, x, y):
        return vector(ZZ, x) * self.F * vector(ZZ, y)

    def quadratic_form(self, x):
        x = vector(ZZ, x)
        return x * self.F * x

    def determinant(self):
        if self._det is None:
            self._det = self.F.determinant()
        return self._det

    def finke-phoste(self, bound: int):
        s = []
        return s

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
