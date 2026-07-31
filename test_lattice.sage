from sage.all import *
import sys, traceback

load("lattice.sage")

# ---------------------------------------------------------------------------
# Эталонные реализации из отдельных файлов проекта. Методы класса Lattice
# сверяются с ними, чтобы консолидация в один файл ничего не изменила.
# ---------------------------------------------------------------------------

def ref_bilinear(F, x, y):
    return x.dot_product(F * y)

# Algs10-12.sage
def ref_same_norm(F1, F2, S2):
    D1 = list(F1.diagonal())
    norm_to_indices = {}
    for i, d in enumerate(D1):
        norm_to_indices.setdefault(d, []).append(i)
    SN2 = [[] for _ in range(F1.ncols())]
    for u in S2:
        norm = ref_bilinear(F2, u, u)
        for i in norm_to_indices.get(norm, []):
            SN2[i].append(u)
    return SN2

# Algs10-12.sage, с исправленным индексом строки (i-1 вместо k-1), см. README:
# C_{ki} = {u in SN2_i : Phi2(u, v_j) = Phi1(b_i, b_j)}
def ref_cand_vect_iso(F1, F2, SN2, part_iso, k, i):
    if i < k:
        return []
    C_i = []
    for u in SN2[i - 1]:
        if all(ref_bilinear(F2, u, part_iso[j]) == F1[i - 1, j] for j in range(k - 1)):
            C_i.append(u)
    return C_i

# Algs10-12.sage
def ref_is_i_partial(F1, F2, part_iso):
    i = len(part_iso)
    for j in range(i):
        if ref_bilinear(F2, part_iso[i - 1], part_iso[j]) != F1[i - 1, j]:
            return False
    return True

# nbExt.sage (удалён в коммите "all in one file")
def ref_cand_vect(F, SN_i, kpartial, k, i):
    if i < k:
        return []
    return [u for u in SN_i if all((u * F * kpartial[j]) == F[i, j] for j in range(k))]

def ref_nb_ext(F, SN_i, kpartial, k, i):
    return len(ref_cand_vect(F, SN_i, kpartial, k, i))

# fingerprint_optimized.sage (set_immutable вызывается без аргумента: в Sage
# у него нет параметра, оригинал падал бы с TypeError)
def ref_compute_fingerprint_optimized(F, SN):
    n = F.nrows()
    f_matrix = matrix(ZZ, n, n)
    b_trivial = [vector(ZZ, n, {idx: 1}) for idx in range(n)]
    F_new = copy(F)
    SN_new = []
    for lst in SN:
        SN_new.append([copy(v) for v in lst])
    for k in range(n):
        kpartial = b_trivial[:k]
        for i in range(k, n):
            f_matrix[k, i] = ref_nb_ext(F_new, SN_new[i], kpartial, k, i)
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
    for lst in SN_new:
        for v in lst:
            v.set_immutable()
    return f_matrix, F_new, SN_new

# vect_sort(part3).sage
def ref_same_norm_p3(Gram, s):
    length = [Gram[ind, ind] for ind in range(Gram.ncols())]
    result = [[] for _ in range(Gram.ncols())]
    for ind_i in range(len(length)):
        for ind_j in range(len(s)):
            v = s[ind_j]
            if (v * Gram * v.column())[0] == length[ind_i]:
                result[ind_i].append(v)
    return result

def ref_allowed_vect(Gram, sn_res, found_vec_img, vect_ind, step):
    result = []
    for u in sn_res:
        flag = True
        for ind_i in range(step - 1):
            if Gram[vect_ind][ind_i] != u.dot_product(Gram * found_vec_img[ind_i]):
                flag = False
                break
        if flag:
            result.append(u)
    return result

def ref_auto_morph(Gram, found_vec_img):
    u = found_vec_img[-1]
    u_ind = len(found_vec_img) - 1
    for ind_i in range(len(found_vec_img)):
        if u.dot_product(Gram * found_vec_img[ind_i]) != Gram[u_ind][ind_i]:
            return False
    return True

# ---------------------------------------------------------------------------
# Хелперы
# ---------------------------------------------------------------------------

def random_basis(n, bound=5, rows=None):
    while True:
        B = random_matrix(ZZ, rows or n, n, x=-bound, y=bound + 1)
        if B.rank() == n:
            return B

def frozen(vs):
    out = set()
    for v in vs:
        w = vector(ZZ, v)
        w.set_immutable()
        out.add(w)
    return out

def sage_short_vectors(F, M):
    """Короткие векторы (кроме нуля) с Phi(v,v) <= M через QuadraticForm Sage."""
    Q = QuadraticForm(ZZ, 2 * F)
    out = set()
    for vecs in Q.short_vector_list_up_to_length(M + 1):
        for v in vecs:
            w = vector(ZZ, v)
            if w.is_zero():
                continue
            for s in (w, -w):
                t = copy(s)
                t.set_immutable()
                out.add(t)
    return out

# ---------------------------------------------------------------------------
# Тесты: базовый интерфейс
# ---------------------------------------------------------------------------

def test_init_rank_gram_det():
    B = matrix(ZZ, [[2, 1], [0, 3]])
    lat = Lattice(B)
    assert lat.rank() == 2
    assert lat.gram_matrix() == B.transpose() * B
    assert lat.determinant() == (B.transpose() * B).determinant() == 36
    assert lat.determinant() == 36, "повторный вызов должен читать кэш"

def test_init_rank_deficient():
    lat = Lattice(matrix(ZZ, [[1, 2], [2, 4]]))
    assert lat.rank() == 1

def test_embedded_vec():
    B = random_basis(3)
    lat = Lattice(B)
    for _ in range(20):
        c = vector(ZZ, [randint(-4, 4) for _ in range(3)])
        assert lat.embedded_vec(c) == B * c

def test_bilinear_and_quadratic_form():
    B = random_basis(3)
    lat = Lattice(B)
    F = lat.gram_matrix()
    for _ in range(20):
        x = vector(ZZ, [randint(-4, 4) for _ in range(3)])
        y = vector(ZZ, [randint(-4, 4) for _ in range(3)])
        # согласованность со скалярным произведением вложенных векторов
        assert lat.bilinear_form(x, y) == (B * x).dot_product(B * y)
        assert lat.quadratic_form(x) == (B * x).dot_product(B * x)
        assert lat.bilinear_form(x, y) == lat.bilinear_form(y, x)
        assert lat.bilinear_form(x, y) == Lattice.bilinear(F, x, y)
        assert lat.bilinear_form(x, y) == ref_bilinear(F, x, y)

def test_bilinear_is_bilinear():
    F = Lattice(random_basis(3)).gram_matrix()
    x = vector(ZZ, [1, -2, 3]); y = vector(ZZ, [0, 4, -1]); z = vector(ZZ, [2, 2, 2])
    a = ZZ(5)
    assert Lattice.bilinear(F, x, y + z) == Lattice.bilinear(F, x, y) + Lattice.bilinear(F, x, z)
    assert Lattice.bilinear(F, a * x, y) == a * Lattice.bilinear(F, x, y)

def test_quadratic_form_positive_definite():
    lat = Lattice(random_basis(3))
    for _ in range(30):
        x = vector(ZZ, [randint(-4, 4) for _ in range(3)])
        if x.is_zero():
            continue
        assert lat.quadratic_form(x) > 0

# ---------------------------------------------------------------------------
# Тесты: Грам–Шмидт
# ---------------------------------------------------------------------------

def test_gso_reconstruction():
    B = random_basis(4)
    lat = Lattice(B)
    Bstar, mu = lat.gso()
    cols = B.columns()
    for i in range(4):
        rebuilt = Bstar[i] + sum(mu[i, j] * Bstar[j] for j in range(i))
        assert rebuilt == cols[i]

def test_gso_orthogonality():
    Bstar, mu = Lattice(random_basis(4)).gso()
    for i in range(4):
        for j in range(i):
            assert Bstar[i].dot_product(Bstar[j]) == 0

def test_gso_rejects_dependent():
    lat = Lattice(matrix(ZZ, [[1, 2], [2, 4]]))
    try:
        lat.gso()
    except ValueError:
        return
    raise AssertionError("ожидался ValueError на линейно зависимом входе")

def test_gso_is_cached():
    lat = Lattice(random_basis(3))
    assert lat.gso() is lat.gso()

# ---------------------------------------------------------------------------
# Тесты: LLL
# ---------------------------------------------------------------------------

def test_lll_preserves_lattice():
    for _ in range(5):
        B = random_basis(4, bound=9)
        lat = Lattice(B)
        lat.lll()
        U = B.inverse() * lat.basis
        assert U.change_ring(QQ).denominator() == 1, "смена базиса не целочисленна"
        assert abs(U.det()) == 1, "смена базиса не унимодулярна"
        assert lat.gram_matrix() == lat.basis.transpose() * lat.basis

def test_lll_lovasz_condition():
    delta = QQ(3) / 4
    for _ in range(5):
        lat = Lattice(random_basis(4, bound=9))
        lat.lll(delta=delta)
        Bstar, mu = lat.gso()
        for i in range(lat.n - 1):
            lhs = delta * Bstar[i].dot_product(Bstar[i])
            rhs_vec = mu[i + 1, i] * Bstar[i] + Bstar[i + 1]
            assert lhs <= rhs_vec.dot_product(rhs_vec), "условие Ловаса нарушено"

def test_lll_shortens_basis():
    for _ in range(5):
        B = random_basis(4, bound=9)
        lat = Lattice(B)
        before = max((B.transpose() * B).diagonal())
        lat.lll()
        assert max(lat.gram_matrix().diagonal()) <= before

def test_lll_is_idempotent():
    lat = Lattice(random_basis(4, bound=9))
    lat.lll()
    first = copy(lat.basis)
    lat.lll()
    assert lat.basis == first

def test_lll_resets_caches():
    lat = Lattice(random_basis(3, bound=9))
    lat.finke_pohst()
    lat.basis = (lat.basis * matrix(ZZ, 3, 3, [3, 1, 0, 0, 1, 0, 0, 0, 1])).change_ring(ZZ)
    lat.F = lat.basis.transpose() * lat.basis
    lat._reset_cache()
    assert lat._short_vectors == {} and lat._gso is None and lat._ldl_exact is None

# ---------------------------------------------------------------------------
# Тесты: LDL
# ---------------------------------------------------------------------------

def test_ldl_exact_reconstruction():
    for _ in range(5):
        lat = Lattice(random_basis(4))
        L, D = lat.ldl(exact=True)
        assert L * D * L.transpose() == lat.gram_matrix()
        assert L.base_ring() is QQ

def test_ldl_exact_unit_lower_triangular():
    L, D = Lattice(random_basis(4)).ldl(exact=True)
    n = L.nrows()
    for i in range(n):
        assert L[i, i] == 1
        for j in range(i + 1, n):
            assert L[i, j] == 0
    assert D == diagonal_matrix(D.diagonal())

def test_ldl_float_reconstruction():
    lat = Lattice(random_basis(4))
    L, D = lat.ldl()
    diff = L * D * L.transpose() - lat.gram_matrix().change_ring(RR)
    assert max(abs(x) for x in diff.list()) < 1e-6

def test_ldl_positive_pivots():
    L, D = Lattice(random_basis(4)).ldl(exact=True)
    assert all(d > 0 for d in D.diagonal()), "форма положительно определена => пивоты > 0"

def test_ldl_caches_separately():
    lat = Lattice(random_basis(3))
    assert lat.ldl(exact=True) is lat.ldl(exact=True)
    assert lat.ldl() is lat.ldl()
    assert lat.ldl(exact=True)[0].base_ring() is not lat.ldl()[0].base_ring()

def test_ldl_rejects_non_symmetric():
    lat = Lattice(random_basis(3))
    lat.F = matrix(ZZ, [[1, 2, 0], [0, 1, 0], [0, 0, 1]])
    lat._reset_cache()
    try:
        lat.ldl(exact=True)
    except ValueError:
        return
    raise AssertionError("ожидался ValueError на несимметричной матрице Грама")

def test_ldl_rejects_zero_pivot():
    lat = Lattice(random_basis(2))
    lat.F = matrix(ZZ, [[0, 0], [0, 1]])
    lat._reset_cache()
    try:
        lat.ldl(exact=True)
    except ValueError:
        return
    raise AssertionError("ожидался ValueError на нулевом пивоте")

# ---------------------------------------------------------------------------
# Тесты: Финке–Пост
# ---------------------------------------------------------------------------

def test_finke_pohst_matches_sage():
    for _ in range(6):
        lat = Lattice(random_basis(3, bound=4))
        got = lat.finke_pohst()
        M = max(lat.gram_matrix().diagonal())
        assert frozen(got) == sage_short_vectors(lat.gram_matrix(), M)

def test_finke_pohst_matches_sage_dim4():
    for _ in range(3):
        lat = Lattice(random_basis(4, bound=3))
        got = lat.finke_pohst()
        M = max(lat.gram_matrix().diagonal())
        assert frozen(got) == sage_short_vectors(lat.gram_matrix(), M)

def test_finke_pohst_respects_bound():
    lat = Lattice(random_basis(3, bound=4))
    M = max(lat.gram_matrix().diagonal())
    for bound in (1, M // 2, M, M + 3):
        vs = lat.finke_pohst(bound=bound)
        assert all(lat.quadratic_form(v) <= bound for v in vs)
        assert frozen(vs) == sage_short_vectors(lat.gram_matrix(), bound)

def test_finke_pohst_monotone_in_bound():
    lat = Lattice(random_basis(3, bound=4))
    M = max(lat.gram_matrix().diagonal())
    small = frozen(lat.finke_pohst(bound=M))
    large = frozen(lat.finke_pohst(bound=M + 5))
    assert small <= large

def test_finke_pohst_symmetric_and_nonzero():
    lat = Lattice(random_basis(3, bound=4))
    vs = frozen(lat.finke_pohst())
    assert all(not v.is_zero() for v in vs)
    for v in vs:
        w = -v
        w.set_immutable()
        assert w in vs, "множество должно быть замкнуто относительно v -> -v"

def test_finke_pohst_includes_boundary_norm():
    # Решётка Z x 2Z: при M = 4 вектор нормы ровно 4 обязан попасть в ответ.
    lat = Lattice(matrix(ZZ, [[1, 0], [0, 2]]))
    emb = set()
    for v in lat.finke_pohst(return_embedded=True):
        w = copy(v); w.set_immutable(); emb.add(w)
    expected = set()
    for c in [(1, 0), (-1, 0), (2, 0), (-2, 0), (0, 2), (0, -2)]:
        w = vector(ZZ, c); w.set_immutable(); expected.add(w)
    assert emb == expected, "потерян вектор с нормой ровно M"

def test_finke_pohst_return_embedded():
    lat = Lattice(random_basis(3, bound=4))
    coords = lat.finke_pohst()
    emb = lat.finke_pohst(return_embedded=True)
    assert len(coords) == len(emb)
    assert frozen(emb) == frozen([lat.embedded_vec(v) for v in coords])

def test_finke_pohst_returns_copies():
    lat = Lattice(random_basis(3, bound=4))
    first = lat.finke_pohst()
    first[0][0] += 1000
    second = lat.finke_pohst()
    assert frozen(second) == sage_short_vectors(lat.gram_matrix(),
                                                max(lat.gram_matrix().diagonal()))

def test_finke_pohst_norms_match_quadratic_form():
    lat = Lattice(random_basis(3, bound=4))
    for v in lat.finke_pohst():
        assert lat.quadratic_form(v) == lat.embedded_vec(v).dot_product(lat.embedded_vec(v))

# ---------------------------------------------------------------------------
# Тесты: same_norm (Алгоритм 10)
# ---------------------------------------------------------------------------

def test_same_norm_matches_reference():
    for _ in range(5):
        L1 = Lattice(random_basis(3, bound=4))
        L2 = Lattice(random_basis(3, bound=4))
        M1 = max(L1.gram_matrix().diagonal())
        S2 = L2.finke_pohst(bound=M1)
        assert L1.same_norm(L2, S2) == ref_same_norm(L1.gram_matrix(), L2.gram_matrix(), S2)

def test_same_norm_matches_part3_variant():
    lat = Lattice(random_basis(3, bound=4))
    S = lat.finke_pohst()
    got = lat.same_norm(lat, S)
    exp = ref_same_norm_p3(lat.gram_matrix(), S)
    assert [frozen(x) for x in got] == [frozen(x) for x in exp]

def test_same_norm_definition():
    L1 = Lattice(random_basis(3, bound=4))
    L2 = Lattice(random_basis(3, bound=4))
    M1 = max(L1.gram_matrix().diagonal())
    S2 = L2.finke_pohst(bound=M1)
    SN2 = L1.same_norm(L2, S2)
    diag = L1.gram_matrix().diagonal()
    for i, lst in enumerate(SN2):
        for u in lst:
            assert L2.quadratic_form(u) == diag[i]
    for u in S2:
        for i, d in enumerate(diag):
            if L2.quadratic_form(u) == d:
                assert u in SN2[i], "вектор нужной нормы пропущен"

def test_same_norm_known_example():
    # Пример из Algs10-12_usage.ipynb: F1 = diag(2,2,4), L2 = Z^3
    L1 = Lattice(matrix(ZZ, [[1, 1, 0], [1, -1, 0], [0, 0, 2]]))
    L2 = Lattice(identity_matrix(ZZ, 3))
    S2 = [vector(ZZ, v) for v in [(1, 1, 0), (2, 0, 0), (0, 2, 0), (1, 0, 0)]]
    SN2 = L1.same_norm(L2, S2)
    assert [len(x) for x in SN2] == [1, 1, 2]
    assert SN2[0] == [vector(ZZ, (1, 1, 0))]
    assert SN2[2] == [vector(ZZ, (2, 0, 0)), vector(ZZ, (0, 2, 0))]

# ---------------------------------------------------------------------------
# Тесты: cand_vect / nb_ext (Алгоритм 11, автоморфизмы)
# ---------------------------------------------------------------------------

def _fixture(n=3, bound=4):
    lat = Lattice(random_basis(n, bound=bound))
    S = lat.finke_pohst()
    return lat, lat.same_norm(lat, S)

def test_cand_vect_matches_reference():
    lat, SN = _fixture()
    F = lat.gram_matrix()
    e = [vector(ZZ, lat.n, {idx: 1}) for idx in range(lat.n)]
    for k in range(lat.n):
        for i in range(lat.n):
            got = lat.cand_vect(SN[i], e[:k], k, i)
            assert got == ref_cand_vect(F, SN[i], e[:k], k, i)

def test_cand_vect_empty_when_i_lt_k():
    lat, SN = _fixture()
    e = [vector(ZZ, lat.n, {idx: 1}) for idx in range(lat.n)]
    assert lat.cand_vect(SN[0], e[:2], 2, 0) == []

def test_cand_vect_definition():
    lat, SN = _fixture()
    F = lat.gram_matrix()
    e = [vector(ZZ, lat.n, {idx: 1}) for idx in range(lat.n)]
    k, i = 2, 2
    got = lat.cand_vect(SN[i], e[:k], k, i)
    for u in got:
        assert all(lat.bilinear_form(u, e[j]) == F[i, j] for j in range(k))
    for u in SN[i]:
        if all(lat.bilinear_form(u, e[j]) == F[i, j] for j in range(k)):
            assert u in got

def test_cand_vect_uses_supplied_gram():
    lat, SN = _fixture()
    F2 = copy(lat.gram_matrix())
    F2.swap_rows(0, 1); F2.swap_columns(0, 1)
    e = [vector(ZZ, lat.n, {idx: 1}) for idx in range(lat.n)]
    assert lat.cand_vect(SN[1], e[:1], 1, 1, F2) == ref_cand_vect(F2, SN[1], e[:1], 1, 1)

def test_nb_ext_is_cardinality_of_cand_vect():
    lat, SN = _fixture()
    e = [vector(ZZ, lat.n, {idx: 1}) for idx in range(lat.n)]
    for k in range(lat.n):
        for i in range(lat.n):
            assert lat.nb_ext(SN[i], e[:k], k, i) == len(lat.cand_vect(SN[i], e[:k], k, i))
            assert lat.nb_ext(SN[i], e[:k], k, i) == ref_nb_ext(lat.gram_matrix(), SN[i], e[:k], k, i)

# ---------------------------------------------------------------------------
# Тесты: cand_vect_iso (Алгоритм 11, изометрии)
# ---------------------------------------------------------------------------

def test_cand_vect_iso_matches_spec():
    L1 = Lattice(matrix(ZZ, [[1, 1, 2], [0, 1, 0], [0, 0, 1]]))
    L2 = Lattice(matrix(ZZ, [[1, 1, 2], [0, 1, 0], [0, 0, 1]]))
    F1 = L1.gram_matrix()
    S2 = L2.finke_pohst(bound=max(F1.diagonal()))
    F2 = L2.gram_matrix()   # читать после finke_pohst: он приводит базис LLL
    SN2 = L1.same_norm(L2, S2)
    n = L1.n
    for k in range(1, n + 1):
        for i in range(1, n + 1):
            for u0 in SN2[0][:4]:
                part_iso = [u0] * (k - 1)
                got = L1.cand_vect_iso(L2, SN2, part_iso, k, i)
                assert got == ref_cand_vect_iso(F1, F2, SN2, part_iso, k, i), \
                    "cand_vect_iso должен фильтровать по строке i, а не k"

def test_cand_vect_iso_empty_when_i_lt_k():
    L1 = Lattice(random_basis(3, bound=4))
    L2 = Lattice(random_basis(3, bound=4))
    S2 = L2.finke_pohst(bound=max(L1.gram_matrix().diagonal()))
    SN2 = L1.same_norm(L2, S2)
    assert L1.cand_vect_iso(L2, SN2, [], 3, 1) == []

def test_cand_vect_iso_matches_allowed_vect():
    # vect_sort(part3).allowed_vect - тот же алгоритм для случая L1 == L2
    lat, SN = _fixture()
    F = lat.gram_matrix()
    for i in range(1, lat.n + 1):
        for k in range(1, lat.n + 1):
            if i < k or not SN[0]:
                continue
            part_iso = [SN[0][0]] * (k - 1)
            got = lat.cand_vect_iso(lat, SN, part_iso, k, i)
            exp = ref_allowed_vect(F, SN[i - 1], part_iso, i - 1, k)
            assert got == exp

def test_cand_vect_iso_full_step_gives_isometry():
    B = random_basis(3, bound=4)
    U = random_matrix(ZZ, 3, 3, algorithm='unimodular')
    L1, L2 = Lattice(B), Lattice(B * U)
    F1 = L1.gram_matrix()
    S2 = L2.finke_pohst(bound=max(F1.diagonal()))
    SN2 = L1.same_norm(L2, S2)
    # кандидаты на первый вектор при k=1 - просто все векторы нужной нормы
    assert L1.cand_vect_iso(L2, SN2, [], 1, 1) == SN2[0]

# ---------------------------------------------------------------------------
# Тесты: is_i_partial / auto_morph (Алгоритм 12)
# ---------------------------------------------------------------------------

def test_is_i_partial_matches_reference():
    L1 = Lattice(random_basis(3, bound=4))
    L2 = Lattice(random_basis(3, bound=4))
    F1, F2 = L1.gram_matrix(), L2.gram_matrix()
    for _ in range(200):
        ln = randint(1, 3)
        p = [vector(ZZ, [randint(-2, 2) for _ in range(3)]) for _ in range(ln)]
        assert Lattice.is_i_partial(F1, F2, p) == ref_is_i_partial(F1, F2, p)

def test_auto_morph_matches_reference():
    lat = Lattice(random_basis(3, bound=4))
    F = lat.gram_matrix()
    for _ in range(200):
        ln = randint(1, 3)
        p = [vector(ZZ, [randint(-2, 2) for _ in range(3)]) for _ in range(ln)]
        assert lat.auto_morph(p) == ref_auto_morph(F, p)
        assert lat.auto_morph(p) == Lattice.is_i_partial(F, F, p)

def test_is_i_partial_accepts_trivial_automorphism():
    lat = Lattice(random_basis(3, bound=4))
    F = lat.gram_matrix()
    e = [vector(ZZ, 3, {idx: 1}) for idx in range(3)]
    for k in range(1, 4):
        assert Lattice.is_i_partial(F, F, e[:k]), "тривиальный автоморфизм должен приниматься"

def test_is_i_partial_rejects_wrong_norm():
    lat = Lattice(random_basis(3, bound=4))
    F = lat.gram_matrix()
    e0 = vector(ZZ, 3, {0: 1})
    assert not Lattice.is_i_partial(F, F, [2 * e0]), "удвоенный вектор меняет норму"

def test_is_i_partial_on_real_isometry():
    B = random_basis(3, bound=4)
    U = random_matrix(ZZ, 3, 3, algorithm='unimodular')
    L1, L2 = Lattice(B), Lattice(B * U)
    ok, M = L1.is_isometric(L2)
    assert ok
    cols = [M.column(i) for i in range(3)]
    for k in range(1, 4):
        assert Lattice.is_i_partial(L1.gram_matrix(), L2.gram_matrix(), cols[:k])

# ---------------------------------------------------------------------------
# Тесты: fingerprint
# ---------------------------------------------------------------------------

def test_fingerprint_matches_reference():
    for _ in range(4):
        lat, SN = _fixture()
        f, F_new, SN_new, perm = lat.get_fingerprint_and_perm(SN)
        rf, rF, rSN = ref_compute_fingerprint_optimized(lat.gram_matrix(), SN)
        assert f == rf
        assert F_new == rF
        assert [frozen(x) for x in SN_new] == [frozen(x) for x in rSN]

def test_fingerprint_perm_is_permutation():
    lat, SN = _fixture()
    f, F_new, SN_new, perm = lat.get_fingerprint_and_perm(SN)
    assert sorted(perm) == list(range(lat.n))

def test_fingerprint_perm_conjugates_gram():
    lat, SN = _fixture()
    f, F_new, SN_new, perm = lat.get_fingerprint_and_perm(SN)
    F = lat.gram_matrix()
    n = lat.n
    P = matrix(ZZ, n, n)
    for k in range(n):
        P[k, perm[k]] = 1
    assert F_new == P * F * P.transpose(), "F_new должна быть перестановочно сопряжена F"

def test_fingerprint_diagonal_counts_extensions():
    lat, SN = _fixture()
    f, F_new, SN_new, perm = lat.get_fingerprint_and_perm(SN)
    n = lat.n
    e = [vector(ZZ, n, {idx: 1}) for idx in range(n)]
    for k in range(n):
        expected = len([u for u in SN_new[k]
                        if all(Lattice.bilinear(F_new, u, e[j]) == F_new[k, j]
                               for j in range(k))])
        assert f[k, k] == expected, "f[k,k] = число расширений тривиального k-частичного автоморфизма"

def test_fingerprint_diagonal_positive():
    lat, SN = _fixture()
    f, F_new, SN_new, perm = lat.get_fingerprint_and_perm(SN)
    for k in range(lat.n):
        assert f[k, k] >= 1, "тривиальный автоморфизм всегда продолжается"

def test_fingerprint_lower_triangle_is_zero():
    lat, SN = _fixture()
    f, F_new, SN_new, perm = lat.get_fingerprint_and_perm(SN)
    for k in range(lat.n):
        for i in range(k):
            assert f[k, i] == 0, "f верхнетреугольная"

def test_fingerprint_does_not_mutate_input():
    lat, SN = _fixture()
    before = [frozen(x) for x in SN]
    lat.get_fingerprint_and_perm(SN)
    assert [frozen(x) for x in SN] == before, "исходный SN не должен меняться"
    assert lat.gram_matrix() == lat.basis.transpose() * lat.basis

def test_fingerprint_vectors_immutable():
    lat, SN = _fixture()
    f, F_new, SN_new, perm = lat.get_fingerprint_and_perm(SN)
    for lst in SN_new:
        for v in lst:
            assert v.is_immutable()

def test_fingerprint_sn_norms_match_permuted_gram():
    lat, SN = _fixture()
    f, F_new, SN_new, perm = lat.get_fingerprint_and_perm(SN)
    for k in range(lat.n):
        for u in SN_new[k]:
            assert Lattice.bilinear(F_new, u, u) == F_new[k, k]

# ---------------------------------------------------------------------------
# Тесты: is_isometric
# ---------------------------------------------------------------------------

def test_is_isometric_self():
    B = random_basis(3, bound=4)
    ok, M = Lattice(B).is_isometric(Lattice(copy(B)))
    assert ok and M is not None

def test_is_isometric_unimodular_transform():
    for _ in range(5):
        B = random_basis(3, bound=5)
        U = random_matrix(ZZ, 3, 3, algorithm='unimodular')
        L1, L2 = Lattice(B), Lattice(B * U)
        ok, M = L1.is_isometric(L2)
        assert ok, "решётки с унимодулярно связанными базисами изометричны"
        assert M.transpose() * L2.gram_matrix() * M == L1.gram_matrix(), \
            "M должна переносить форму L2 в форму L1"

def test_is_isometric_matrix_is_unimodular():
    B = random_basis(3, bound=5)
    U = random_matrix(ZZ, 3, 3, algorithm='unimodular')
    ok, M = Lattice(B).is_isometric(Lattice(B * U))
    assert ok and abs(M.det()) == 1

def test_is_isometric_rotated_lattice():
    # поворот на 90 градусов - настоящая изометрия Z^2
    B = matrix(ZZ, [[1, 0], [0, 1]])
    R = matrix(ZZ, [[0, -1], [1, 0]])
    ok, M = Lattice(B).is_isometric(Lattice(R * B))
    assert ok

def test_is_isometric_rejects_different_determinant():
    L1 = Lattice(matrix(ZZ, [[1, 0], [0, 1]]))
    L2 = Lattice(matrix(ZZ, [[2, 0], [0, 1]]))
    assert L1.is_isometric(L2) == (False, None)

def test_is_isometric_rejects_different_rank():
    L1 = Lattice(identity_matrix(ZZ, 2))
    L2 = Lattice(identity_matrix(ZZ, 3))
    assert L1.is_isometric(L2) == (False, None)

def test_is_isometric_rejects_same_det_different_form():
    # обе формы имеют det = 9 и ранг 2, но минимумы 1 и 2 => не изометричны
    L1 = Lattice(matrix(ZZ, [[1, 0], [0, 3], [0, 0]]))          # F = diag(1, 9)
    L2 = Lattice(matrix(ZZ, [[1, 1], [1, 0], [0, 2]]))          # F = [[2,1],[1,5]]
    assert L1.gram_matrix().det() == L2.gram_matrix().det() == 9
    ok, M = L1.is_isometric(L2)
    assert ok is False and M is None

def test_is_isometric_scaled_lattice_not_isometric():
    L1 = Lattice(identity_matrix(ZZ, 3))
    L2 = Lattice(2 * identity_matrix(ZZ, 3))
    assert L1.is_isometric(L2) == (False, None)

def test_is_isometric_is_symmetric_relation():
    B = random_basis(3, bound=5)
    U = random_matrix(ZZ, 3, 3, algorithm='unimodular')
    assert Lattice(B).is_isometric(Lattice(B * U))[0] == Lattice(B * U).is_isometric(Lattice(B))[0]

def test_is_isometric_repeatable():
    B = random_basis(3, bound=5)
    U = random_matrix(ZZ, 3, 3, algorithm='unimodular')
    L1, L2 = Lattice(B), Lattice(B * U)
    first = L1.is_isometric(L2)[0]
    assert L1.is_isometric(L2)[0] == first, "повторный вызов не должен менять ответ"

def test_is_isometric_preserves_gram_invariant():
    B = random_basis(3, bound=5)
    L1 = Lattice(B)
    L2 = Lattice(B * random_matrix(ZZ, 3, 3, algorithm='unimodular'))
    d1, d2 = L1.determinant(), L2.determinant()
    L1.is_isometric(L2)
    assert L1.gram_matrix().det() == d1 and L2.gram_matrix().det() == d2

# ---------------------------------------------------------------------------
# Раннер
# ---------------------------------------------------------------------------

def main():
    set_random_seed(20260731)
    tests = [(name, obj) for name, obj in sorted(globals().items())
             if name.startswith("test_") and callable(obj)]
    failed = []
    for name, fn in tests:
        try:
            fn()
            print("  ok    %s" % name)
        except Exception:
            failed.append(name)
            print("  FAIL  %s" % name)
            traceback.print_exc()
    print("\n%d/%d passed" % (len(tests) - len(failed), len(tests)))
    if failed:
        print("failed: %s" % ", ".join(failed))
        sys.exit(1)

main()
