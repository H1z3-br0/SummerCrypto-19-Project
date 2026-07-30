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
                break
                
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

    def finke_pohst(self, bound: int = None, return_embedded: bool = False):
        self.lll()
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


    def same_norm(self, other_lattice, S2):
        D1 = list(self.F.diagonal())
        norm_to_indices = {}
        for i, d in enumerate(D1):
            norm_to_indices.setdefault(d, []).append(i)
        SN2 = [[] for _ in range(self.F.ncols())]
        for u in S2:
            norm = other_lattice.bilinear_form(u, u)
            for i in norm_to_indices.get(norm, []):
                SN2[i].append(u)
        return SN2

    def cand_vect_iso(self, other_lattice, SN2, part_iso, k, i):
        if i < k:
            return []
        C_i = []
        for u in SN2[i - 1]:
            ok = True
            for j in range(k - 1):
                if other_lattice.bilinear_form(u, part_iso[j]) != self.F[k - 1, j]:
                    ok = False
                    break
            if ok:
                C_i.append(u)
        return C_i

    def nb_ext(self, SN_i, kpartial, k, i):
        return len(self.cand_vect(SN_i, kpartial, k, i))

    def cand_vect(self, SN_i, kpartial, k, i):
        if i < k:
            return []
        candidates = []
        for u in SN_i:
            if all(self.bilinear_form(u, kpartial[j]) == self.F[i, j] for j in range(k)):
                candidates.append(u)
        return candidates

    def get_fingerprint_and_perm(self, SN):
        n = self._rank
        f_matrix = matrix(ZZ, n, n)
        b_trivial = [vector(ZZ, n, {idx: 1}) for idx in range(n)]
        
        F_new = copy(self.F)
        SN_new = []
        for lst in SN:
            new_lst = []
            for v in lst:
                v_copy = copy(v)
                v_copy.set_immutable(False)
                new_lst.append(v_copy)
            SN_new.append(new_lst)
            
        perm = list(range(n))
        
        for k in range(n):
            kpartial = b_trivial[:k] 
            for i in range(k, n):
                f_matrix[k, i] = self.nb_ext(SN_new[i], kpartial, k, i)
                
            valid_vals = [(f_matrix[k, i], i) for i in range(k, n) if f_matrix[k, i] > 0]
            
            if valid_vals:
                min_val, min_idx = min(valid_vals, key=lambda x: x[0])
                if min_idx != k:
                    f_matrix.swap_columns(k, min_idx)
                    F_new.swap_rows(k, min_idx)
                    F_new.swap_columns(k, min_idx)
                    SN_new[k], SN_new[min_idx] = SN_new[min_idx], SN_new[k]
                    for lst in SN_new:
                        for v in lst:
                            v[k], v[min_idx] = v[min_idx], v[k]
                    perm[k], perm[min_idx] = perm[min_idx], perm[k]
                    
        for lst in SN_new:
            for v in lst:
                v.set_immutable(True)
                
        return f_matrix, F_new, SN_new, perm

    def is_isometric(self, other):
        """
        Проверяет, изометричны ли две решетки (self и other).
        Возвращает (True, M), если изоморфизм найден, где M - матрица преобразования.
        Возвращает (False, None), если изоморфизма не существует.
        """
        if self.rank() != other.rank() or self.determinant() != other.determinant():
            return False, None

        n = self.rank()
        F1 = self.F

        M1 = max(F1.diagonal())
        S2 = other.finke_pohst(bound=M1, return_embedded=False) 

        SN2 = self.same_norm(other, S2)

        fingerprint, F1_new, SN2_new, perm = self.get_fingerprint_and_perm(SN2)

        inv_perm = [0] * n
        for i, p in enumerate(perm):
            inv_perm[p] = i

        def backtrack(k, partial_iso):
            if k == n:
                return partial_iso

            candidates = []
            for u in SN2_new[k]:
                valid = True
                for j in range(k):
                    if other.bilinear_form(u, partial_iso[j]) != F1_new[k, j]:
                        valid = False
                        break
                if valid:
                    candidates.append(u)

            for v in candidates:
                new_partial = partial_iso + [v]

                if k + 1 < n:
                    ext_count = 0
                    for u in SN2_new[k+1]:
                        valid_ext = True
                        for j in range(k + 1):
                            if other.bilinear_form(u, new_partial[j]) != F1_new[k+1, j]:
                                valid_ext = False
                                break
                        if valid_ext:
                            ext_count += 1
                    
                    if ext_count != fingerprint[k+1, k+1]:
                        continue

                res = backtrack(k + 1, new_partial)
                if res is not None:
                    return res
            return None
        partial_iso_coords = backtrack(0, [])

        if partial_iso_coords is None:
            return False, None

        M_new = matrix(ZZ, n, n)
        for i in range(n):
            M_new.set_column(i, partial_iso_coords[i])

        M_final = matrix(ZZ, n, n)
        for i in range(n):
            M_final.set_column(i, M_new.column(inv_perm[i]))

        return True, M_final