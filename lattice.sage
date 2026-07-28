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

def cholevsky_decompose(A_matrix):
    if A_matrix != A_matrix.transpose():
        raise ("Matrix's not symmetrical")
    lt_matr = matrix(RR, n, n)
