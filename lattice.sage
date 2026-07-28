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

def cholevsky_decompose(A_matrix):
    if A_matrix != A_matrix.transpose():
        raise ("Matrix's not symmetrical")
    lt_matr = matrix(RR, n, n)
