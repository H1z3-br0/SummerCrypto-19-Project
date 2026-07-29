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
    
    @staticmethod
    def _gso_vectors(B):
        n = len(B)
        Bstar = [B[0]]
        K = B[0].base_ring().fraction_field()
        zero = vector(K, len(B[0]))
        if Bstar[0] == zero:
            raise ValueError("linearly dependent input for module version of Gram-Schmidt")
        mu = matrix(K, n, n)
        for i in range(1, n):
            for j in range(i):
                mu[i, j] = B[i].dot_product(Bstar[j]) / (Bstar[j].dot_product(Bstar[j]))
            Bstar.append(B[i] - sum(mu[i, j] * Bstar[j] for j in range(i)))
            if Bstar[i] == zero:
                raise ValueError("linearly dependent input for module version of Gram-Schmidt")
        return Bstar, mu

    def gso(self):
        return Lattice._gso_vectors(self.basis.columns())

    def lll(self, delta=3 / 4):
        n = self.basis.ncols()
        B = self.basis.columns()
        while True:
            Bstar, mu = Lattice._gso_vectors(B)
            for i in range(1, n):
                for j in range(i - 1, -1, -1):
                    mu_ij = B[i].dot_product(Bstar[j]) / Bstar[j].dot_product(Bstar[j])
                    B[i] = B[i] - mu_ij.floor() * B[j]
            Bstar, mu = Lattice._gso_vectors(B)
            swapped = False
            for i in range(n - 1):
                lhs = delta * Bstar[i].dot_product(Bstar[i])
                rhs_vec = mu[i + 1, i] * Bstar[i] + Bstar[i + 1]
                rhs = rhs_vec.dot_product(rhs_vec)
                if lhs > rhs:
                    B[i], B[i + 1] = B[i + 1], B[i]
                    swapped = True
                    break
            if not swapped:
        self.basis = matrix(B).transpose().change_ring(ZZ)
        self.F = self.basis.transpose() * self.basis
        self._rank = self.basis.rank()
        self._det = None
        self._ldl = None
        return self

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

    def finke_phost(self, bound: int = None, return_embedded: bool = False):
        L, D = self.ldl()
        n, d = self._rank, D.diagonal()
        M = max(self.F.diagonal()) if bound is None else bound
        x = [0] * n

        def search(i, norm, fnz):
            s = sum(L[j, i] * x[j] for j in range(i + 1, n))
            R = sqrt(max(0, M - norm) / d[i])
            lb = max(0, ceil(-s - R)) if fnz else ceil(-s - R)
            
            for v in range(lb, floor(-s + R) + 1):
                x[i] = v
                n_norm = norm + d[i] * (v + s)**2
                if i == 0:
                    if any(x):
                        vec = vector(ZZ, x)
                        yield vec
                        yield -vec
                else:
                    yield from search(i - 1, n_norm, fnz and v == 0)

        s = list(search(n - 1, 0, True))

        if return_embedded:
            return [self.embedded_vec(v) for v in s]

        return s
