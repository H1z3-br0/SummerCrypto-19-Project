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

    def finke_pohst(self, bound: int):
        s = []
        return s

    def ldl(self):
        if self._ldl is not None:
            return self._ldl

        if self.F != self.F.transpose():
            raise ValueError("Gram matrix is not symmetric")

        rang = self._rank
        L = identity_matrix(RR, rang)
        d = [RR(0)] * rang

        for j in range(rang):
            d[j] = self.F[j, j] - sum((L[j, k])**2 * d[k] for k in range(j))
            
            if d[j] == 0:
                raise ValueError("Zero pivot encountered, LDL decomposition non-existent or unstable")
                
            for i in range(j + 1, rang):
                L[i, j] = (self.F[i, j] - sum(L[i, k] * L[j, k] * d[k] for k in range(j))) / d[j]

        D = diagonal_matrix(RR, d)
        self._ldl = (L, D)
        return self._ldl
