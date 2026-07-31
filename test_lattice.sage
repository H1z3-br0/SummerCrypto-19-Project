"""Тесты для класса Lattice из lattice.sage.

Запуск:
    sage test_lattice.sage              # все тесты
    sage test_lattice.sage lll ldl      # только те, чьё имя содержит подстроку

Каждый тест сеется индивидуально (seed = хеш имени), поэтому падение
воспроизводится запуском одного этого теста, без остальной сюиты.

Проверка идёт по двум независимым линиям:

1. Штатные средства Sage как внешний оракул: short_vector_list_up_to_length,
   is_globally_equivalent_to, gram_schmidt, LLL, главные миноры. Это самая
   сильная проверка - реализация сверяется с кодом, написанным не нами.

2. Вторая реализация тех же алгоритмов, восстановленная из удалённых файлов
   проекта (Algs10-12.sage, vect_sort(part3).sage, fingerprint_optimized.sage,
   nbExt.sage - коммиты b0f4fb8 и a66a01b) и сверенная с псевдокодом из
   README/main.tex. Она держит поведение класса привязанным к исходным
   алгоритмам после консолидации в один файл.
"""

from sage.all import *
import os, sys, time, traceback, zlib

HERE = os.path.dirname(os.path.abspath(__file__))
load(os.path.join(HERE, "lattice.sage"))

# ---------------------------------------------------------------------------
# Эталонные реализации (см. п. 2 в docstring)
# ---------------------------------------------------------------------------

def ref_bilinear(F, x, y):
    return x.dot_product(F * y)

def ref_same_norm(F1, F2, S2):
    """Алгоритм 10, Algs10-12.sage."""
    norm_to_indices = {}
    for i, d in enumerate(list(F1.diagonal())):
        norm_to_indices.setdefault(d, []).append(i)
    SN2 = [[] for _ in range(F1.ncols())]
    for u in S2:
        for i in norm_to_indices.get(ref_bilinear(F2, u, u), []):
            SN2[i].append(u)
    return SN2

def ref_same_norm_p3(Gram, s):
    """Тот же Алгоритм 10 в редакции vect_sort(part3).sage - независимый перебор
    без словаря норм."""
    length = [Gram[ind, ind] for ind in range(Gram.ncols())]
    result = [[] for _ in range(Gram.ncols())]
    for ind_i in range(len(length)):
        for ind_j in range(len(s)):
            v = s[ind_j]
            if (v * Gram * v.column())[0] == length[ind_i]:
                result[ind_i].append(v)
    return result

def ref_cand_vect(F, SN_i, kpartial, k, i):
    """nbExt.sage."""
    if i < k:
        return []
    return [u for u in SN_i if all((u * F * kpartial[j]) == F[i, j] for j in range(k))]

def ref_nb_ext(F, SN_i, kpartial, k, i):
    return len(ref_cand_vect(F, SN_i, kpartial, k, i))

def ref_allowed_vect(Gram, sn_res, found_vec_img, vect_ind, step):
    """Алгоритм 11 в редакции vect_sort(part3).sage."""
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

def ref_is_i_partial(F1, F2, part_iso):
    """Алгоритм 12, Algs10-12.sage."""
    i = len(part_iso)
    for j in range(i):
        if ref_bilinear(F2, part_iso[i - 1], part_iso[j]) != F1[i - 1, j]:
            return False
    return True

def ref_auto_morph(Gram, found_vec_img):
    """Тот же Алгоритм 12 в редакции vect_sort(part3).sage."""
    u = found_vec_img[-1]
    u_ind = len(found_vec_img) - 1
    for ind_i in range(len(found_vec_img)):
        if u.dot_product(Gram * found_vec_img[ind_i]) != Gram[u_ind][ind_i]:
            return False
    return True

def ref_fingerprint(F, SN):
    """fingerprint_optimized.sage. Единственная правка против оригинала:
    set_immutable() в Sage не принимает аргументов, из-за чего файл падал с
    TypeError на первой же итерации и никогда не выполнялся."""
    n = F.nrows()
    f_matrix = matrix(ZZ, n, n)
    b_trivial = [vector(ZZ, n, {idx: 1}) for idx in range(n)]
    F_new = copy(F)
    SN_new = [[copy(v) for v in lst] for lst in SN]
    for k in range(n):
        kpartial = b_trivial[:k]
        for i in range(k, n):
            f_matrix[k, i] = ref_nb_ext(F_new, SN_new[i], kpartial, k, i)
        valid = [(f_matrix[k, i], i) for i in range(k, n) if f_matrix[k, i] > 0]
        if valid:
            _, min_idx = min(valid, key=lambda x: x[0])
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

def spec_cand_vect_iso(F1, F2, SN2, part_iso, k, i):
    """Алгоритм 11 по README/main.tex:
    C_i^k = {u in SN2_i : Phi2(u, v_j) = Phi1(b_i, b_j), j = 1..k-1}."""
    if i < k:
        return []
    return [u for u in SN2[i - 1]
            if all(ref_bilinear(F2, u, part_iso[j]) == F1[i - 1, j] for j in range(k - 1))]

# ---------------------------------------------------------------------------
# Утверждения и хелперы
# ---------------------------------------------------------------------------

class Failed(AssertionError):
    pass

def check(cond, msg):
    if not cond:
        raise Failed(msg)

def eq(a, b, msg):
    if a != b:
        raise Failed("%s\n    получено: %s\n    ожидалось: %s" % (msg, a, b))

def raises(fn, exc, msg):
    try:
        fn()
    except exc:
        return
    except Exception as e:
        raise Failed("%s: получено %s(%s), ожидалось %s" % (msg, type(e).__name__, e, exc.__name__))
    raise Failed("%s: исключение не поднято" % msg)

def random_basis(n, bound=5, rows=None):
    """Полноранговый целочисленный базис из n столбцов."""
    for _ in range(1000):
        B = random_matrix(ZZ, rows or n, n, x=-bound, y=bound + 1)
        if B.rank() == n:
            return B
    raise RuntimeError("не удалось построить базис ранга %d" % n)

def frozen(vs):
    out = set()
    for v in vs:
        w = vector(ZZ, list(v))
        w.set_immutable()
        out.add(w)
    return out

def sage_short_vectors(F, M):
    """Ненулевые v с Phi(v,v) <= M, посчитанные средствами Sage."""
    out = set()
    for vecs in QuadraticForm(ZZ, 2 * F).short_vector_list_up_to_length(M + 1):
        for v in vecs:
            w = vector(ZZ, list(v))
            if w.is_zero():
                continue
            for s in (w, -w):
                t = copy(s)
                t.set_immutable()
                out.add(t)
    return out

def sage_equivalent(F1, F2):
    """Оракул: изометричны ли решётки с матрицами Грама F1 и F2."""
    return bool(QuadraticForm(ZZ, 2 * F1).is_globally_equivalent_to(QuadraticForm(ZZ, 2 * F2)))

def unimodular(n):
    return random_matrix(ZZ, n, n, algorithm='unimodular')

def reduced(n, bound=4, rows=None):
    """Решётка с уже приведённым базисом. finke_pohst() вызывает lll() внутри,
    поэтому читать gram_matrix()/M до него нельзя: короткие векторы вернутся в
    координатах уже другого базиса."""
    lat = Lattice(random_basis(n, bound=bound, rows=rows))
    lat.lll()
    return lat

def fixture(n=3, bound=4):
    """Решётка вместе с её SN (короткие векторы, разложенные по нормам базиса)."""
    for _ in range(50):
        lat = Lattice(random_basis(n, bound=bound))
        SN = lat.same_norm(lat, lat.finke_pohst())
        if all(len(x) > 0 for x in SN):
            return lat, SN
    raise RuntimeError("не удалось получить непустой SN")


# ---------------------------------------------------------------------------
# Базовый интерфейс
# ---------------------------------------------------------------------------

def test_init_rank_gram_det():
    B = matrix(ZZ, [[2, 1], [0, 3]])
    lat = Lattice(B)
    eq(lat.rank(), 2, "ранг")
    eq(lat.gram_matrix(), B.transpose() * B, "матрица Грама")
    eq(lat.determinant(), 36, "определитель формы")
    eq(lat.determinant(), 36, "повторный вызов должен читать кэш")

def test_init_determinant_is_det_basis_squared():
    for n in (1, 2, 3, 4):
        B = random_basis(n)
        eq(Lattice(B).determinant(), B.det() ** 2, "det F = det(B)^2 для квадратного B")

def test_init_dimension_one():
    lat = Lattice(matrix(ZZ, [[3]]))
    eq(lat.rank(), 1, "ранг")
    eq(lat.determinant(), 9, "определитель")
    eq(lat.quadratic_form(vector(ZZ, [2])), 36, "квадратичная форма")

def test_init_rank_deficient():
    eq(Lattice(matrix(ZZ, [[1, 2], [2, 4]])).rank(), 1, "ранг вырожденного базиса")

def test_init_embedding_into_higher_dimension():
    B = random_basis(2, rows=5)
    lat = Lattice(B)
    eq(lat.rank(), 2, "ранг вложения 5x2")
    eq(lat.gram_matrix().nrows(), 2, "форма 2x2 независимо от размерности вложения")

def test_init_changes_ring_to_ZZ():
    lat = Lattice(matrix(QQ, [[2, 0], [0, 3]]))
    check(lat.basis.base_ring() is ZZ, "базис должен приводиться к ZZ")

def test_embedded_vec():
    B = random_basis(3)
    lat = Lattice(B)
    for _ in range(20):
        c = vector(ZZ, [randint(-4, 4) for _ in range(3)])
        eq(lat.embedded_vec(c), B * c, "embedded_vec")

def test_embedded_vec_is_linear():
    lat = Lattice(random_basis(3))
    x = vector(ZZ, [1, -2, 3]); y = vector(ZZ, [4, 0, -1])
    eq(lat.embedded_vec(x + y), lat.embedded_vec(x) + lat.embedded_vec(y), "аддитивность")
    eq(lat.embedded_vec(5 * x), 5 * lat.embedded_vec(x), "однородность")

def test_bilinear_form_matches_embedded_dot_product():
    B = random_basis(3)
    lat = Lattice(B)
    for _ in range(20):
        x = vector(ZZ, [randint(-4, 4) for _ in range(3)])
        y = vector(ZZ, [randint(-4, 4) for _ in range(3)])
        eq(lat.bilinear_form(x, y), (B * x).dot_product(B * y), "Phi(x,y) = <Bx, By>")
        eq(lat.quadratic_form(x), (B * x).dot_product(B * x), "Q(x) = <Bx, Bx>")

def test_bilinear_form_is_symmetric():
    lat = Lattice(random_basis(3))
    for _ in range(20):
        x = vector(ZZ, [randint(-4, 4) for _ in range(3)])
        y = vector(ZZ, [randint(-4, 4) for _ in range(3)])
        eq(lat.bilinear_form(x, y), lat.bilinear_form(y, x), "симметричность")

def test_bilinear_staticmethod_agrees_with_form():
    lat = Lattice(random_basis(3))
    F = lat.gram_matrix()
    for _ in range(20):
        x = vector(ZZ, [randint(-4, 4) for _ in range(3)])
        y = vector(ZZ, [randint(-4, 4) for _ in range(3)])
        eq(Lattice.bilinear(F, x, y), lat.bilinear_form(x, y), "bilinear == bilinear_form")
        eq(Lattice.bilinear(F, x, y), ref_bilinear(F, x, y), "bilinear == эталон")

def test_bilinear_is_bilinear():
    F = Lattice(random_basis(3)).gram_matrix()
    x = vector(ZZ, [1, -2, 3]); y = vector(ZZ, [0, 4, -1]); z = vector(ZZ, [2, 2, 2])
    eq(Lattice.bilinear(F, x, y + z),
       Lattice.bilinear(F, x, y) + Lattice.bilinear(F, x, z), "аддитивность по 2-му аргументу")
    eq(Lattice.bilinear(F, x + y, z),
       Lattice.bilinear(F, x, z) + Lattice.bilinear(F, y, z), "аддитивность по 1-му аргументу")
    eq(Lattice.bilinear(F, 5 * x, y), 5 * Lattice.bilinear(F, x, y), "однородность")

def test_quadratic_form_positive_definite():
    for n in (1, 2, 3, 4):
        lat = Lattice(random_basis(n))
        for _ in range(30):
            x = vector(ZZ, [randint(-4, 4) for _ in range(n)])
            if x.is_zero():
                continue
            check(lat.quadratic_form(x) > 0, "форма должна быть положительно определена")

def test_gram_matrix_is_symmetric_and_hadamard():
    for n in (2, 3, 4):
        F = Lattice(random_basis(n)).gram_matrix()
        eq(F, F.transpose(), "матрица Грама симметрична")
        check(F.det() <= prod(F.diagonal()), "неравенство Адамара")

# ---------------------------------------------------------------------------
# Грам-Шмидт
# ---------------------------------------------------------------------------

def test_gso_reconstruction():
    for n in (1, 2, 3, 4, 5):
        B = random_basis(n)
        Bstar, mu = Lattice(B).gso()
        cols = B.columns()
        for i in range(n):
            eq(Bstar[i] + sum(mu[i, j] * Bstar[j] for j in range(i)), cols[i],
               "b_i = b*_i + sum mu_ij b*_j")

def test_gso_orthogonality():
    for n in (2, 3, 4, 5):
        Bstar, _ = Lattice(random_basis(n)).gso()
        for i in range(n):
            for j in range(i):
                eq(Bstar[i].dot_product(Bstar[j]), 0, "b*_i ⊥ b*_j")

def test_gso_matches_sage_gram_schmidt():
    for n in (2, 3, 4):
        B = random_basis(n)
        Bstar, mu = Lattice(B).gso()
        G, M = B.transpose().change_ring(QQ).gram_schmidt()
        for i in range(n):
            eq(Bstar[i], G.row(i), "b*_i совпадает с gram_schmidt Sage")
            for j in range(i):
                eq(mu[i, j], M[i, j], "mu_ij совпадает с gram_schmidt Sage")

def test_gso_mu_is_strictly_lower_triangular():
    n = 4
    _, mu = Lattice(random_basis(n)).gso()
    for i in range(n):
        for j in range(i, n):
            eq(mu[i, j], 0, "mu строго нижнетреугольна")

def test_gso_determinant_identity():
    for n in (2, 3, 4):
        lat = Lattice(random_basis(n))
        Bstar, _ = lat.gso()
        eq(prod(b.dot_product(b) for b in Bstar), lat.determinant(),
           "prod |b*_i|^2 = det F")

def test_gso_rejects_dependent_input():
    raises(lambda: Lattice(matrix(ZZ, [[1, 2], [2, 4]])).gso(), ValueError,
           "линейно зависимый вход")

def test_gso_rejects_zero_first_vector():
    raises(lambda: Lattice(matrix(ZZ, [[0, 1], [0, 0]])).gso(), ValueError,
           "нулевой первый вектор")

def test_gso_is_cached():
    lat = Lattice(random_basis(3))
    check(lat.gso() is lat.gso(), "gso должен кэшироваться")

# ---------------------------------------------------------------------------
# LLL
# ---------------------------------------------------------------------------

def test_lll_preserves_lattice():
    for n in (2, 3, 4):
        B = random_basis(n, bound=9)
        lat = Lattice(B)
        lat.lll()
        U = B.inverse() * lat.basis
        eq(U.change_ring(QQ).denominator(), 1, "смена базиса должна быть целочисленной")
        eq(abs(U.det()), 1, "смена базиса должна быть унимодулярной")

def test_lll_keeps_gram_consistent():
    lat = Lattice(random_basis(4, bound=9))
    lat.lll()
    eq(lat.gram_matrix(), lat.basis.transpose() * lat.basis, "F = B^T B после редукции")
    eq(lat.rank(), 4, "ранг сохраняется")

def test_lll_preserves_determinant():
    for n in (2, 3, 4):
        B = random_basis(n, bound=9)
        lat = Lattice(B)
        before = lat.determinant()
        lat.lll()
        eq(lat.gram_matrix().det(), before, "определитель формы инвариантен")

def test_lll_lovasz_condition_for_several_delta():
    for delta in (QQ(1) / 2, QQ(3) / 4, QQ(9) / 10, QQ(1)):
        lat = Lattice(random_basis(4, bound=9))
        lat.lll(delta=delta)
        Bstar, mu = lat.gso()
        for i in range(lat.n - 1):
            lhs = delta * Bstar[i].dot_product(Bstar[i])
            rhs_vec = mu[i + 1, i] * Bstar[i] + Bstar[i + 1]
            check(lhs <= rhs_vec.dot_product(rhs_vec),
                  "условие Ловаса нарушено при delta=%s, i=%d" % (delta, i))

def test_lll_can_lengthen_basis():
    # ЗАФИКСИРОВАННЫЙ ДЕФЕКТ. Редукция по размеру берёт mu.floor() вместо
    # mu.round(), то есть загоняет mu в [0,1) вместо [-1/2,1/2]. При mu = -0.4
    # floor даёт -1, и вектор не укорачивается, а удлиняется. В итоге lll()
    # регулярно ВЫДАЁТ базис длиннее исходного (замер: 26% случаев в
    # размерности 4, 54% в размерности 6), а max(diag F) - это ровно та
    # граница M, от которой экспоненциально зависит перебор в finke_pohst.
    # Замена floor() на round() убирает эффект (1 случай из 200) и приводит
    # max(diag F) вплотную к штатному LLL Sage. После такой правки тест
    # упадёт - его нужно заменить на проверку "редукция не удлиняет базис".
    lengthened = 0
    for _ in range(25):
        B = random_basis(6, bound=9)
        lat = Lattice(B)
        before = max((B.transpose() * B).diagonal())
        lat.lll()
        if max(lat.gram_matrix().diagonal()) > before:
            lengthened += 1
    check(lengthened > 0,
          "ожидалось, что floor-редукция иногда удлиняет базис; если это "
          "исправлено, замените тест на проверку обратного неравенства")

def test_lll_is_idempotent():
    lat = Lattice(random_basis(4, bound=9))
    lat.lll()
    first = copy(lat.basis)
    lat.lll()
    eq(lat.basis, first, "повторная редукция ничего не меняет")

def test_lll_delta_change_reruns():
    lat = Lattice(random_basis(4, bound=9))
    lat.lll(delta=QQ(1) / 2)
    lat.lll(delta=QQ(99) / 100)
    Bstar, mu = lat.gso()
    for i in range(lat.n - 1):
        lhs = QQ(99) / 100 * Bstar[i].dot_product(Bstar[i])
        rhs_vec = mu[i + 1, i] * Bstar[i] + Bstar[i + 1]
        check(lhs <= rhs_vec.dot_product(rhs_vec), "новая delta должна применяться заново")

def test_lll_invalidates_short_vector_cache():
    lat = Lattice(random_basis(3, bound=9))
    lat.finke_pohst()
    check(lat._short_vectors, "кэш должен наполниться")
    lat._lll_delta = None          # имитируем «базис ещё не редуцирован»
    lat.lll()
    M = max(lat.gram_matrix().diagonal())
    eq(frozen(lat.finke_pohst()), sage_short_vectors(lat.gram_matrix(), M),
       "после повторной редукции кэш должен пересчитаться корректно")

def test_lll_dimension_one_is_noop():
    lat = Lattice(matrix(ZZ, [[3]]))
    lat.lll()
    eq(lat.basis, matrix(ZZ, [[3]]), "в размерности 1 редуцировать нечего")

def test_lll_handles_embedding_into_higher_dimension():
    B = random_basis(3, bound=6, rows=5)
    lat = Lattice(B)
    lat.lll()
    eq(lat.basis.nrows(), 5, "размерность вложения сохраняется")
    eq(abs((B.transpose() * B).det()), abs(lat.gram_matrix().det()), "определитель сохраняется")

def test_lll_deviates_from_textbook_size_reduction():
    # ЗАФИКСИРОВАННОЕ ОТКЛОНЕНИЕ. lll() приводит по размеру через mu.floor()
    # вместо round(), поэтому гарантия |mu_ij| <= 1/2 не выполняется, а вместе
    # с ней теряется и классическая оценка на длину b_1. Тест ищет свидетеля.
    # Если floor() заменят на round(), тест упадёт - тогда его нужно удалить
    # вместе с этим комментарием.
    witness = None
    for _ in range(20):
        lat = Lattice(random_basis(4, bound=9))
        lat.lll()
        _, mu = lat.gso()
        for i in range(4):
            for j in range(i):
                if abs(mu[i, j]) > QQ(1) / 2:
                    witness = (i, j, mu[i, j])
                    break
    check(witness is not None,
          "ожидалось |mu_ij| > 1/2 (floor-редукция); если это исправлено, удалите тест")


# ---------------------------------------------------------------------------
# LDL
# ---------------------------------------------------------------------------

def test_ldl_exact_reconstruction():
    for n in (1, 2, 3, 4, 5):
        lat = Lattice(random_basis(n))
        L, D = lat.ldl(exact=True)
        eq(L * D * L.transpose(), lat.gram_matrix(), "L D L^T = F")
        check(L.base_ring() is QQ, "exact-разложение должно жить над QQ")

def test_ldl_exact_unit_lower_triangular():
    L, D = Lattice(random_basis(4)).ldl(exact=True)
    for i in range(L.nrows()):
        eq(L[i, i], 1, "единицы на диагонали L")
        for j in range(i + 1, L.ncols()):
            eq(L[i, j], 0, "L нижнетреугольная")
    eq(D, diagonal_matrix(D.diagonal()), "D диагональна")

def test_ldl_pivots_match_leading_minors():
    # независимый оракул: d_j = det(F_j) / det(F_{j-1}) для главных миноров
    for n in (2, 3, 4):
        lat = Lattice(random_basis(n))
        F = lat.gram_matrix()
        _, D = lat.ldl(exact=True)
        d = D.diagonal()
        prev = QQ(1)
        for j in range(n):
            cur = F[:j + 1, :j + 1].det()
            eq(d[j], QQ(cur) / prev, "пивот d_%d = det(F_%d)/det(F_%d)" % (j, j + 1, j))
            prev = QQ(cur)

def test_ldl_positive_pivots():
    for n in (2, 3, 4):
        _, D = Lattice(random_basis(n)).ldl(exact=True)
        check(all(d > 0 for d in D.diagonal()), "у положительно определённой формы пивоты > 0")

def test_ldl_float_reconstruction():
    lat = Lattice(random_basis(4))
    L, D = lat.ldl()
    diff = L * D * L.transpose() - lat.gram_matrix().change_ring(RR)
    check(max(abs(x) for x in diff.list()) < 1e-6, "приближённое разложение восстанавливает F")

def test_ldl_float_close_to_exact():
    lat = Lattice(random_basis(4))
    Lf, Df = lat.ldl()
    Le, De = lat.ldl(exact=True)
    check(max(abs(x) for x in (Lf - Le.change_ring(RR)).list()) < 1e-6, "L(RR) ≈ L(QQ)")
    check(max(abs(x) for x in (Df - De.change_ring(RR)).list()) < 1e-6, "D(RR) ≈ D(QQ)")

def test_ldl_caches_exact_and_float_separately():
    lat = Lattice(random_basis(3))
    check(lat.ldl(exact=True) is lat.ldl(exact=True), "exact кэшируется")
    check(lat.ldl() is lat.ldl(), "приближённое кэшируется")
    check(lat.ldl(exact=True)[0].base_ring() is not lat.ldl()[0].base_ring(),
          "кэши exact и RR не должны пересекаться")

def test_ldl_rejects_non_symmetric():
    lat = Lattice(random_basis(3))
    lat.F = matrix(ZZ, [[1, 2, 0], [0, 1, 0], [0, 0, 1]])
    lat._reset_cache()
    raises(lambda: lat.ldl(exact=True), ValueError, "несимметричная матрица Грама")

def test_ldl_rejects_zero_pivot():
    lat = Lattice(random_basis(2))
    lat.F = matrix(ZZ, [[0, 0], [0, 1]])
    lat._reset_cache()
    raises(lambda: lat.ldl(exact=True), ValueError, "нулевой пивот")

# ---------------------------------------------------------------------------
# Финке-Пост
# ---------------------------------------------------------------------------

def test_finke_pohst_matches_sage_oracle():
    for n in (1, 2, 3):
        for _ in range(6):
            lat = reduced(n)
            M = max(lat.gram_matrix().diagonal())
            eq(frozen(lat.finke_pohst()), sage_short_vectors(lat.gram_matrix(), M),
               "множество коротких векторов в размерности %d" % n)

def test_finke_pohst_matches_sage_oracle_dim4():
    for _ in range(4):
        lat = reduced(4, bound=3)
        M = max(lat.gram_matrix().diagonal())
        eq(frozen(lat.finke_pohst()), sage_short_vectors(lat.gram_matrix(), M),
           "множество коротких векторов в размерности 4")

def test_finke_pohst_matches_sage_oracle_over_bounds():
    lat = reduced(3)
    F = lat.gram_matrix()
    M = max(F.diagonal())
    for bound in range(0, M + 4):
        eq(frozen(lat.finke_pohst(bound=bound)), sage_short_vectors(F, bound),
           "bound=%d" % bound)

def test_finke_pohst_zero_bound_is_empty():
    eq(Lattice(random_basis(3, bound=4)).finke_pohst(bound=0), [],
       "при bound=0 ненулевых векторов нет")

def test_finke_pohst_respects_bound():
    lat = Lattice(random_basis(3, bound=4))
    M = max(lat.gram_matrix().diagonal())
    for bound in (1, M // 2, M, M + 3):
        for v in lat.finke_pohst(bound=bound):
            check(lat.quadratic_form(v) <= bound, "норма не должна превышать bound")

def test_finke_pohst_monotone_in_bound():
    lat = Lattice(random_basis(3, bound=4))
    M = max(lat.gram_matrix().diagonal())
    prev = frozen(lat.finke_pohst(bound=0))
    for bound in range(1, M + 4):
        cur = frozen(lat.finke_pohst(bound=bound))
        check(prev <= cur, "множество должно расти по bound")
        prev = cur

def test_finke_pohst_symmetric_and_nonzero():
    lat = Lattice(random_basis(3, bound=4))
    vs = frozen(lat.finke_pohst())
    check(len(vs) > 0, "фикстура не должна быть пустой")
    check(all(not v.is_zero() for v in vs), "нулевой вектор должен исключаться")
    for v in vs:
        w = -v
        w.set_immutable()
        check(w in vs, "множество замкнуто относительно v -> -v")
    eq(len(vs) % 2, 0, "мощность чётна из-за симметрии")

def test_finke_pohst_includes_boundary_norm():
    # решётки, где вектор нормы ровно M существует: округление RR его теряет
    for B, expected in [
        (matrix(ZZ, [[1, 0], [0, 2]]), [(1, 0), (-1, 0), (2, 0), (-2, 0), (0, 2), (0, -2)]),
        (matrix(ZZ, [[1, 0], [0, 3]]), [(1, 0), (-1, 0), (2, 0), (-2, 0), (3, 0), (-3, 0), (0, 3), (0, -3)]),
    ]:
        lat = Lattice(B)
        eq(frozen(lat.finke_pohst(return_embedded=True)), frozen([vector(ZZ, c) for c in expected]),
           "потерян вектор с нормой ровно M")

def test_finke_pohst_return_embedded():
    lat = Lattice(random_basis(3, bound=4))
    coords = lat.finke_pohst()
    emb = lat.finke_pohst(return_embedded=True)
    eq(len(coords), len(emb), "длины должны совпадать")
    eq(frozen(emb), frozen([lat.embedded_vec(v) for v in coords]), "embedded = B * coords")

def test_finke_pohst_embedded_norms_match_quadratic_form():
    lat = Lattice(random_basis(3, bound=4))
    for v in lat.finke_pohst():
        e = lat.embedded_vec(v)
        eq(lat.quadratic_form(v), e.dot_product(e), "Q(x) = |Bx|^2")

def test_finke_pohst_returns_defensive_copies():
    lat = Lattice(random_basis(3, bound=4))
    first = lat.finke_pohst()
    first[0][0] += 1000
    M = max(lat.gram_matrix().diagonal())
    eq(frozen(lat.finke_pohst()), sage_short_vectors(lat.gram_matrix(), M),
       "мутация результата не должна портить кэш")

def test_finke_pohst_cache_is_keyed_by_bound():
    lat = Lattice(random_basis(3, bound=4))
    M = max(lat.gram_matrix().diagonal())
    lat.finke_pohst(bound=M)
    lat.finke_pohst(bound=M + 2)
    check(M in lat._short_vectors and M + 2 in lat._short_vectors, "кэш ключуется по bound")
    eq(frozen(lat.finke_pohst(bound=M)), sage_short_vectors(lat.gram_matrix(), M),
       "повторный запрос отдаёт то же множество")

def test_finke_pohst_contains_shortest_vector():
    for _ in range(4):
        lat = Lattice(random_basis(3, bound=4))
        vs = lat.finke_pohst()
        ours = min(lat.quadratic_form(v) for v in vs)
        lam = QuadraticForm(ZZ, 2 * lat.gram_matrix()).short_vector_list_up_to_length(
            max(lat.gram_matrix().diagonal()) + 1)
        shortest = min(i for i, lst in enumerate(lam) if lst and i > 0)
        eq(ours, shortest, "минимум формы должен достигаться на найденных векторах")

def test_finke_pohst_reduces_basis_first():
    lat = Lattice(random_basis(3, bound=9))
    lat.finke_pohst()
    check(lat._lll_delta is not None, "finke_pohst должен предварительно вызвать LLL")

# ---------------------------------------------------------------------------
# same_norm (Алгоритм 10)
# ---------------------------------------------------------------------------

def test_same_norm_matches_reference():
    for _ in range(6):
        L1 = Lattice(random_basis(3, bound=4))
        L2 = Lattice(random_basis(3, bound=4))
        M1 = max(L1.gram_matrix().diagonal())
        S2 = L2.finke_pohst(bound=M1)
        eq(L1.same_norm(L2, S2),
           ref_same_norm(L1.gram_matrix(), L2.gram_matrix(), S2),
           "same_norm должен совпадать с Алгоритмом 10")

def test_same_norm_matches_part3_variant():
    lat, _ = fixture()
    S = lat.finke_pohst()
    eq([frozen(x) for x in lat.same_norm(lat, S)],
       [frozen(x) for x in ref_same_norm_p3(lat.gram_matrix(), S)],
       "same_norm должен совпадать с вариантом из vect_sort(part3)")

def test_same_norm_definition():
    L1 = Lattice(random_basis(3, bound=4))
    L2 = Lattice(random_basis(3, bound=4))
    S2 = L2.finke_pohst(bound=max(L1.gram_matrix().diagonal()))
    SN2 = L1.same_norm(L2, S2)
    diag = L1.gram_matrix().diagonal()
    for i, lst in enumerate(SN2):
        for u in lst:
            eq(L2.quadratic_form(u), diag[i], "в SN_i лежат векторы нормы F1[i,i]")
    for u in S2:
        for i, d in enumerate(diag):
            if L2.quadratic_form(u) == d:
                check(u in SN2[i], "вектор нужной нормы не должен теряться")

def test_same_norm_length_and_empty_input():
    L1 = Lattice(random_basis(3, bound=4))
    eq(len(L1.same_norm(L1, [])), 3, "длина результата = число базисных векторов")
    eq(L1.same_norm(L1, []), [[], [], []], "пустой вход даёт пустые множества")

def test_same_norm_repeated_norms_share_vectors():
    # у Z^3 все диагональные нормы равны, значит все SN_i совпадают
    lat = Lattice(identity_matrix(ZZ, 3))
    SN = lat.same_norm(lat, lat.finke_pohst())
    eq(frozen(SN[0]), frozen(SN[1]), "равные нормы -> одинаковые множества")
    eq(frozen(SN[1]), frozen(SN[2]), "равные нормы -> одинаковые множества")
    eq(len(SN[0]), 6, "у Z^3 шесть векторов нормы 1")

def test_same_norm_known_example_from_notebook():
    L1 = Lattice(matrix(ZZ, [[1, 1, 0], [1, -1, 0], [0, 0, 2]]))
    L2 = Lattice(identity_matrix(ZZ, 3))
    S2 = [vector(ZZ, v) for v in [(1, 1, 0), (2, 0, 0), (0, 2, 0), (1, 0, 0)]]
    SN2 = L1.same_norm(L2, S2)
    eq([len(x) for x in SN2], [1, 1, 2], "мощности множеств из Algs10-12_usage.ipynb")
    eq(SN2[0], [vector(ZZ, (1, 1, 0))], "SN_1")
    eq(SN2[2], [vector(ZZ, (2, 0, 0)), vector(ZZ, (0, 2, 0))], "SN_3")

# ---------------------------------------------------------------------------
# cand_vect / nb_ext (Алгоритм 11, случай автоморфизмов)
# ---------------------------------------------------------------------------

def _trivial(n, k):
    return [vector(ZZ, n, {idx: 1}) for idx in range(n)][:k]

def test_cand_vect_matches_definition():
    lat, SN = fixture()
    F = lat.gram_matrix()
    hits = 0
    for k in range(lat.n):
        for i in range(k, lat.n):
            kp = _trivial(lat.n, k)
            got = lat.cand_vect(SN[i], kp, k, i)
            exp = [u for u in SN[i] if all(Lattice.bilinear(F, u, kp[j]) == F[i, j] for j in range(k))]
            eq(got, exp, "cand_vect по определению (k=%d, i=%d)" % (k, i))
            hits += len(got)
    check(hits > 0, "тест не должен быть вырожденным")

def test_cand_vect_empty_when_i_less_than_k():
    lat, SN = fixture()
    eq(lat.cand_vect(SN[0], _trivial(lat.n, 2), 2, 0), [], "при i < k множество пусто")

def test_cand_vect_empty_sn():
    lat, _ = fixture()
    eq(lat.cand_vect([], _trivial(lat.n, 1), 1, 1), [], "пустой SN_i даёт пустой результат")

def test_cand_vect_k_zero_returns_everything():
    lat, SN = fixture()
    eq(lat.cand_vect(SN[1], [], 0, 1), SN[1], "при k=0 условий нет, проходят все")

def test_cand_vect_uses_supplied_gram():
    lat, SN = fixture()
    F2 = copy(lat.gram_matrix())
    F2.swap_rows(0, 1); F2.swap_columns(0, 1)
    kp = _trivial(lat.n, 1)
    got = lat.cand_vect(SN[1], kp, 1, 1, F2)
    exp = [u for u in SN[1] if Lattice.bilinear(F2, u, kp[0]) == F2[1, 0]]
    eq(got, exp, "переданная матрица Грама должна использоваться вместо self.F")

def test_cand_vect_result_is_subset_of_input():
    lat, SN = fixture()
    for i in range(lat.n):
        got = lat.cand_vect(SN[i], _trivial(lat.n, 1), 1, i)
        for u in got:
            check(u in SN[i], "кандидаты берутся из SN_i")

def test_nb_ext_is_cardinality_of_cand_vect():
    lat, SN = fixture()
    for k in range(lat.n):
        for i in range(lat.n):
            kp = _trivial(lat.n, k)
            eq(lat.nb_ext(SN[i], kp, k, i), len(lat.cand_vect(SN[i], kp, k, i)),
               "nb_ext = |cand_vect|")

def test_nb_ext_passes_gram_through():
    lat, SN = fixture()
    F2 = copy(lat.gram_matrix())
    F2.swap_rows(0, 1); F2.swap_columns(0, 1)
    eq(lat.nb_ext(SN[1], _trivial(lat.n, 1), 1, 1, F2),
       len(lat.cand_vect(SN[1], _trivial(lat.n, 1), 1, 1, F2)), "F пробрасывается в cand_vect")

# ---------------------------------------------------------------------------
# cand_vect_iso (Алгоритм 11, случай изометрий)
# ---------------------------------------------------------------------------

def _iso_fixture():
    L1 = Lattice(matrix(ZZ, [[1, 1, 2], [0, 1, 0], [0, 0, 1]]))
    L2 = Lattice(matrix(ZZ, [[1, 1, 2], [0, 1, 0], [0, 0, 1]]))
    F1 = L1.gram_matrix()
    S2 = L2.finke_pohst(bound=max(F1.diagonal()))
    return L1, L2, F1, L2.gram_matrix(), L1.same_norm(L2, S2)

def spec_cand_vect_iso(F1, F2, SN2, part_iso, k, i):
    """Алгоритм 11 по README/main.tex:
    C_i^k = {u in SN2_i : Phi2(u, v_j) = Phi1(b_i, b_j), j = 1..k-1}."""
    if i < k:
        return []
    return [u for u in SN2[i - 1]
            if all(Lattice.bilinear(F2, u, part_iso[j]) == F1[i - 1, j] for j in range(k - 1))]

def test_cand_vect_iso_matches_spec():
    # РЕГРЕССИЯ: раньше фильтрация шла по строке k-1 вместо i-1. При i == k
    # строки совпадают, поэтому баг был виден только вне диагонали.
    L1, L2, F1, F2, SN2 = _iso_fixture()
    checked = 0
    for k in range(1, L1.n + 1):
        for i in range(1, L1.n + 1):
            for u0 in SN2[0][:4]:
                part_iso = [u0] * (k - 1)
                eq(L1.cand_vect_iso(L2, SN2, part_iso, k, i),
                   spec_cand_vect_iso(F1, F2, SN2, part_iso, k, i),
                   "cand_vect_iso должен фильтровать по строке i, а не k (k=%d, i=%d)" % (k, i))
                checked += 1
    check(checked > 0, "фикстура пуста, тест ничего не проверил")

def test_cand_vect_iso_off_diagonal_is_exercised():
    # страховка: убеждаемся, что у фикстуры строки i-1 и k-1 реально различны,
    # иначе предыдущий тест прошёл бы и на багованной версии
    _, _, F1, _, _ = _iso_fixture()
    check(any(F1[a, j] != F1[b, j] for a in range(3) for b in range(3) for j in range(3)),
          "нужна матрица Грама с различающимися строками")

def test_cand_vect_iso_matches_allowed_vect():
    # vect_sort(part3).allowed_vect - тот же алгоритм для случая L1 == L2
    lat, SN = fixture()
    F = lat.gram_matrix()
    checked = 0
    for i in range(1, lat.n + 1):
        for k in range(1, i + 1):
            part_iso = [SN[0][0]] * (k - 1)
            eq(lat.cand_vect_iso(lat, SN, part_iso, k, i),
               ref_allowed_vect(F, SN[i - 1], part_iso, i - 1, k),
               "cand_vect_iso должен совпадать с allowed_vect (k=%d, i=%d)" % (k, i))
            checked += 1
    check(checked > 0, "тест ничего не проверил")

def test_cand_vect_iso_empty_when_i_less_than_k():
    _, L2, _, _, SN2 = _iso_fixture()
    L1 = Lattice(matrix(ZZ, [[1, 1, 2], [0, 1, 0], [0, 0, 1]]))
    eq(L1.cand_vect_iso(L2, SN2, [], 3, 1), [], "при i < k множество пусто")

def test_cand_vect_iso_k_one_returns_whole_sn():
    L1, L2, _, _, SN2 = _iso_fixture()
    for i in range(1, L1.n + 1):
        eq(L1.cand_vect_iso(L2, SN2, [], 1, i), SN2[i - 1], "при k=1 условий нет")

def test_cand_vect_iso_agrees_with_cand_vect_on_diagonal():
    lat, SN = fixture()
    for k in range(1, lat.n + 1):
        eq(lat.cand_vect_iso(lat, SN, _trivial(lat.n, k - 1), k, k),
           lat.cand_vect(SN[k - 1], _trivial(lat.n, k - 1), k - 1, k - 1),
           "на диагонали 1-based и 0-based версии должны совпадать")


# ---------------------------------------------------------------------------
# is_i_partial / auto_morph (Алгоритм 12)
# ---------------------------------------------------------------------------

def _random_partials(n, count, spread=2):
    out = []
    for _ in range(count):
        ln = randint(1, n)
        out.append([vector(ZZ, [randint(-spread, spread) for _ in range(n)]) for _ in range(ln)])
    return out

def test_is_i_partial_matches_reference():
    L1 = Lattice(random_basis(3, bound=4))
    L2 = Lattice(random_basis(3, bound=4))
    F1, F2 = L1.gram_matrix(), L2.gram_matrix()
    accepted = 0
    for p in _random_partials(3, 300):
        got = Lattice.is_i_partial(F1, F2, p)
        eq(got, ref_is_i_partial(F1, F2, p), "is_i_partial должен совпадать с Алгоритмом 12")
        accepted += bool(got)
    check(accepted > 0, "тест вырожден: ни один вход не принят")

def test_auto_morph_matches_reference():
    lat = Lattice(random_basis(3, bound=4))
    F = lat.gram_matrix()
    accepted = 0
    for p in _random_partials(3, 300):
        got = lat.auto_morph(p)
        eq(got, ref_auto_morph(F, p), "auto_morph должен совпадать с вариантом из vect_sort(part3)")
        eq(got, Lattice.is_i_partial(F, F, p), "auto_morph = is_i_partial при F1 = F2")
        accepted += bool(got)
    check(accepted > 0, "тест вырожден: ни один вход не принят")

def test_is_i_partial_empty_is_vacuously_true():
    F = Lattice(random_basis(3)).gram_matrix()
    check(Lattice.is_i_partial(F, F, []), "пустое отображение - 0-частичная изометрия")

def test_is_i_partial_accepts_trivial_automorphism():
    lat = Lattice(random_basis(3, bound=4))
    F = lat.gram_matrix()
    for k in range(1, 4):
        check(Lattice.is_i_partial(F, F, _trivial(3, k)), "тривиальный автоморфизм принимается")
        check(lat.auto_morph(_trivial(3, k)), "то же через auto_morph")

def test_is_i_partial_rejects_wrong_norm():
    F = Lattice(random_basis(3, bound=4)).gram_matrix()
    e0 = vector(ZZ, 3, {0: 1})
    check(not Lattice.is_i_partial(F, F, [2 * e0]), "удвоение вектора меняет норму")

def test_is_i_partial_rejects_wrong_inner_product():
    lat = Lattice(identity_matrix(ZZ, 3))
    F = lat.gram_matrix()
    e = _trivial(3, 3)
    check(not Lattice.is_i_partial(F, F, [e[0], e[0]]), "повтор вектора ломает <b1,b2> = 0")

def test_is_i_partial_checks_only_last_vector():
    # алгоритм предполагает, что префикс уже проверен: подсовываем битый префикс
    # и корректный последний вектор
    lat = Lattice(identity_matrix(ZZ, 3))
    F = lat.gram_matrix()
    e = _trivial(3, 3)
    check(Lattice.is_i_partial(F, F, [2 * e[0], e[1]]),
          "проверяется только последний вектор относительно предыдущих")

def test_is_i_partial_on_real_isometry():
    for _ in range(4):
        B = random_basis(3, bound=4)
        L1, L2 = Lattice(B), Lattice(B * unimodular(3))
        ok, M = L1.is_isometric(L2)
        check(ok, "решётки изометричны по построению")
        cols = [M.column(i) for i in range(3)]
        for k in range(1, 4):
            check(Lattice.is_i_partial(L1.gram_matrix(), L2.gram_matrix(), cols[:k]),
                  "каждый префикс найденной изометрии - частичная изометрия")

def test_is_i_partial_full_length_means_isometry():
    B = random_basis(3, bound=4)
    L1, L2 = Lattice(B), Lattice(B * unimodular(3))
    ok, M = L1.is_isometric(L2)
    check(ok, "решётки изометричны")
    eq(M.transpose() * L2.gram_matrix() * M, L1.gram_matrix(),
       "полная проверка эквивалентна M^T F2 M = F1")

# ---------------------------------------------------------------------------
# fingerprint
# ---------------------------------------------------------------------------

def test_fingerprint_matches_reference():
    for _ in range(5):
        lat, SN = fixture()
        f, F_new, SN_new, perm = lat.get_fingerprint_and_perm(SN)
        rf, rF, rSN = ref_fingerprint(lat.gram_matrix(), SN)
        eq(f, rf, "матрица отпечатка")
        eq(F_new, rF, "переставленная матрица Грама")
        eq([frozen(x) for x in SN_new], [frozen(x) for x in rSN], "переставленные SN")



def test_fingerprint_perm_is_permutation():
    lat, SN = fixture()
    _, _, _, perm = lat.get_fingerprint_and_perm(SN)
    eq(sorted(perm), list(range(lat.n)), "perm должна быть перестановкой 0..n-1")

def test_fingerprint_perm_conjugates_gram():
    for _ in range(4):
        lat, SN = fixture()
        _, F_new, _, perm = lat.get_fingerprint_and_perm(SN)
        n = lat.n
        P = matrix(ZZ, n, n)
        for k in range(n):
            P[k, perm[k]] = 1
        eq(F_new, P * lat.gram_matrix() * P.transpose(), "F_new = P F P^T")

def test_fingerprint_diagonal_counts_extensions():
    lat, SN = fixture()
    f, F_new, SN_new, _ = lat.get_fingerprint_and_perm(SN)
    for k in range(lat.n):
        expected = len([u for u in SN_new[k]
                        if all(Lattice.bilinear(F_new, u, _trivial(lat.n, k)[j]) == F_new[k, j]
                               for j in range(k))])
        eq(f[k, k], expected,
           "f[k,k] = число расширений тривиального k-частичного автоморфизма")

def test_fingerprint_diagonal_positive():
    lat, SN = fixture()
    f, _, _, _ = lat.get_fingerprint_and_perm(SN)
    for k in range(lat.n):
        check(f[k, k] >= 1, "тривиальный автоморфизм всегда продолжается")

def test_fingerprint_lower_triangle_is_zero():
    lat, SN = fixture()
    f, _, _, _ = lat.get_fingerprint_and_perm(SN)
    for k in range(lat.n):
        for i in range(k):
            eq(f[k, i], 0, "f верхнетреугольная")

def test_fingerprint_greedy_picks_minimum():
    for _ in range(4):
        lat, SN = fixture()
        f, _, _, _ = lat.get_fingerprint_and_perm(SN)
        for k in range(lat.n):
            tail = [f[k, i] for i in range(k + 1, lat.n) if f[k, i] > 0]
            if f[k, k] > 0 and tail:
                check(f[k, k] <= min(tail),
                      "на шаге %d должен выбираться столбец с минимумом кандидатов" % k)

def test_fingerprint_sn_norms_match_permuted_gram():
    lat, SN = fixture()
    _, F_new, SN_new, _ = lat.get_fingerprint_and_perm(SN)
    for k in range(lat.n):
        for u in SN_new[k]:
            eq(Lattice.bilinear(F_new, u, u), F_new[k, k], "нормы согласованы с F_new")

def test_fingerprint_does_not_mutate_input():
    lat, SN = fixture()
    before = [frozen(x) for x in SN]
    F_before = copy(lat.gram_matrix())
    lat.get_fingerprint_and_perm(SN)
    eq([frozen(x) for x in SN], before, "исходный SN не должен меняться")
    eq(lat.gram_matrix(), F_before, "матрица Грама решётки не должна меняться")

def test_fingerprint_vectors_are_immutable():
    lat, SN = fixture()
    _, _, SN_new, _ = lat.get_fingerprint_and_perm(SN)
    for lst in SN_new:
        for v in lst:
            check(v.is_immutable(), "векторы SN_new должны быть immutable")

def test_fingerprint_identity_perm_for_equal_norms():
    # у Z^3 все диагональные нормы и все f[k,i] равны, перестановка не нужна
    lat = Lattice(identity_matrix(ZZ, 3))
    SN = lat.same_norm(lat, lat.finke_pohst())
    _, F_new, _, perm = lat.get_fingerprint_and_perm(SN)
    eq(perm, [0, 1, 2], "для Z^3 перестановка тривиальна")
    eq(F_new, lat.gram_matrix(), "матрица Грама не меняется")

# ---------------------------------------------------------------------------
# is_isometric
# ---------------------------------------------------------------------------

def _assert_isometry(L1, L2, M):
    eq(M.transpose() * L2.gram_matrix() * M, L1.gram_matrix(), "M^T F2 M = F1")
    eq(abs(M.det()), 1, "матрица изометрии унимодулярна")

def test_is_isometric_self():
    for n in (1, 2, 3, 4):
        B = random_basis(n, bound=4)
        L1, L2 = Lattice(B), Lattice(copy(B))
        ok, M = L1.is_isometric(L2)
        check(ok, "решётка изометрична сама себе (n=%d)" % n)
        _assert_isometry(L1, L2, M)

def test_is_isometric_unimodular_transform():
    for n in (2, 3, 4):
        for _ in range(4):
            B = random_basis(n, bound=5)
            L1, L2 = Lattice(B), Lattice(B * unimodular(n))
            ok, M = L1.is_isometric(L2)
            check(ok, "унимодулярно связанные базисы задают изометричные решётки (n=%d)" % n)
            _assert_isometry(L1, L2, M)

def test_is_isometric_orthogonal_transform():
    # поворот и отражение - настоящие изометрии, базис при этом другой
    B = matrix(ZZ, [[2, 1], [1, 3]])
    for O in [matrix(ZZ, [[0, -1], [1, 0]]), matrix(ZZ, [[1, 0], [0, -1]]),
              matrix(ZZ, [[0, 1], [1, 0]])]:
        L1, L2 = Lattice(B), Lattice(O * B)
        ok, M = L1.is_isometric(L2)
        check(ok, "ортогональное преобразование сохраняет решётку с точностью до изометрии")
        _assert_isometry(L1, L2, M)

def test_is_isometric_agrees_with_sage_oracle_on_random_pairs():
    disagreements = []
    for _ in range(25):
        n = choice([2, 3])
        L1 = Lattice(random_basis(n, bound=4))
        L2 = Lattice(random_basis(n, bound=4))
        ours = bool(L1.is_isometric(L2)[0])
        ref = sage_equivalent(L1.gram_matrix(), L2.gram_matrix())
        if ours != ref:
            disagreements.append((L1.gram_matrix(), L2.gram_matrix(), ours, ref))
    eq(disagreements, [], "расхождение с is_globally_equivalent_to")

def test_is_isometric_agrees_with_sage_oracle_on_same_determinant_pairs():
    # интересная ветка - когда быстрый отсев по det не срабатывает
    pool = [Lattice(random_basis(3, bound=3)) for _ in range(24)]
    by_det = {}
    for lat in pool:
        by_det.setdefault(lat.determinant(), []).append(lat)
    compared = 0
    for dets, group in by_det.items():
        for a in range(len(group)):
            for b in range(a + 1, len(group)):
                L1, L2 = group[a], group[b]
                ours = bool(L1.is_isometric(L2)[0])
                ref = sage_equivalent(L1.gram_matrix(), L2.gram_matrix())
                eq(ours, ref, "расхождение с оракулом при равном det = %s" % dets)
                compared += 1
    check(compared > 0, "не нашлось пар с равным определителем")

def test_is_isometric_returned_matrix_is_valid():
    for _ in range(6):
        B = random_basis(3, bound=5)
        L1, L2 = Lattice(B), Lattice(B * unimodular(3))
        ok, M = L1.is_isometric(L2)
        check(ok, "пара изометрична")
        _assert_isometry(L1, L2, M)
        check(M.base_ring() is ZZ, "матрица должна быть целочисленной")

def test_is_isometric_rejects_different_rank():
    eq(Lattice(identity_matrix(ZZ, 2)).is_isometric(Lattice(identity_matrix(ZZ, 3))),
       (False, None), "разный ранг")

def test_is_isometric_rejects_different_determinant():
    eq(Lattice(matrix(ZZ, [[1, 0], [0, 1]])).is_isometric(Lattice(matrix(ZZ, [[2, 0], [0, 1]]))),
       (False, None), "разный определитель")

def test_is_isometric_rejects_scaled_lattice():
    eq(Lattice(identity_matrix(ZZ, 3)).is_isometric(Lattice(2 * identity_matrix(ZZ, 3))),
       (False, None), "масштабирование не изометрия")

def test_is_isometric_rejects_same_det_different_minimum():
    # обе формы det = 9, ранг 2, но минимумы 1 и 2
    L1 = Lattice(matrix(ZZ, [[1, 0], [0, 3], [0, 0]]))
    L2 = Lattice(matrix(ZZ, [[1, 1], [1, 0], [0, 2]]))
    eq(L1.gram_matrix().det(), 9, "det F1")
    eq(L2.gram_matrix().det(), 9, "det F2")
    check(not sage_equivalent(L1.gram_matrix(), L2.gram_matrix()), "оракул: не изометричны")
    eq(L1.is_isometric(L2), (False, None), "не изометричны")

def test_is_isometric_rejects_class_number_two_pair():
    # дискриминант -20, два класса форм: x^2+5y^2 и 2x^2+2xy+3y^2, оба det = 5
    L1 = Lattice(matrix(ZZ, [[1, 0], [0, 1], [0, 2]]))            # F = [[1,0],[0,5]]
    L2 = Lattice(matrix(ZZ, [[1, 1], [1, 0], [0, 1], [0, 1]]))    # F = [[2,1],[1,3]]
    eq(L1.gram_matrix(), matrix(ZZ, [[1, 0], [0, 5]]), "F1")
    eq(L2.gram_matrix(), matrix(ZZ, [[2, 1], [1, 3]]), "F2")
    eq(L1.determinant(), L2.determinant(), "определители совпадают")
    check(not sage_equivalent(L1.gram_matrix(), L2.gram_matrix()), "оракул: не изометричны")
    eq(L1.is_isometric(L2), (False, None), "не изометричны")

def test_is_isometric_hexagonal_vs_square():
    # A2 (гексагональная) и Z^2 - разные решётки, det 3 против 1
    A2 = Lattice(matrix(ZZ, [[1, 1], [1, -1], [1, 0]]))
    Z2 = Lattice(identity_matrix(ZZ, 2))
    eq(A2.is_isometric(Z2), (False, None), "A2 не изометрична Z^2")

def test_is_isometric_relation_is_symmetric():
    for _ in range(6):
        n = choice([2, 3])
        B = random_basis(n, bound=4)
        C = random_basis(n, bound=4)
        forward = bool(Lattice(B).is_isometric(Lattice(C))[0])
        backward = bool(Lattice(C).is_isometric(Lattice(B))[0])
        eq(forward, backward, "отношение изометрии симметрично")

def test_is_isometric_relation_is_transitive():
    B = random_basis(3, bound=4)
    L1, L2, L3 = Lattice(B), Lattice(B * unimodular(3)), Lattice(B * unimodular(3))
    check(L1.is_isometric(L2)[0] and L2.is_isometric(L3)[0], "звенья цепочки")
    check(L1.is_isometric(L3)[0], "транзитивность")

def test_is_isometric_is_repeatable():
    B = random_basis(3, bound=5)
    L1, L2 = Lattice(B), Lattice(B * unimodular(3))
    first = L1.is_isometric(L2)
    second = L1.is_isometric(L2)
    eq(first[0], second[0], "повторный вызов даёт тот же вердикт")
    _assert_isometry(L1, L2, second[1])

def test_is_isometric_preserves_lattice_invariants():
    B = random_basis(3, bound=5)
    L1, L2 = Lattice(B), Lattice(B * unimodular(3))
    d1, d2 = L1.determinant(), L2.determinant()
    L1.is_isometric(L2)
    eq(L1.gram_matrix().det(), d1, "определитель L1 не меняется")
    eq(L2.gram_matrix().det(), d2, "определитель L2 не меняется")
    eq(L1.gram_matrix(), L1.basis.transpose() * L1.basis, "F1 согласована с базисом")
    eq(L2.gram_matrix(), L2.basis.transpose() * L2.basis, "F2 согласована с базисом")

def test_is_isometric_composes_with_automorphism():
    # если M - изометрия, а A - автоморфизм L1, то M*A тоже изометрия
    B = random_basis(3, bound=4)
    L1, L2 = Lattice(B), Lattice(B * unimodular(3))
    ok, M = L1.is_isometric(L2)
    check(ok, "пара изометрична")
    F1 = L1.gram_matrix()
    A = -identity_matrix(ZZ, 3)          # -I всегда автоморфизм
    eq(A.transpose() * F1 * A, F1, "-I - автоморфизм")
    eq((M * A).transpose() * L2.gram_matrix() * (M * A), F1, "композиция тоже изометрия")

def test_is_isometric_dimension_one():
    check(Lattice(matrix(ZZ, [[3]])).is_isometric(Lattice(matrix(ZZ, [[-3]])))[0],
          "3Z и -3Z - одна решётка")
    eq(Lattice(matrix(ZZ, [[2]])).is_isometric(Lattice(matrix(ZZ, [[3]]))), (False, None),
       "2Z и 3Z различны")

def test_is_isometric_embedding_dimension_irrelevant():
    # одна и та же решётка, вложенная в Z^2 и в Z^4
    L1 = Lattice(matrix(ZZ, [[1, 0], [0, 1]]))
    L2 = Lattice(matrix(ZZ, [[1, 0], [0, 1], [0, 0], [0, 0]]))
    ok, M = L1.is_isometric(L2)
    check(ok, "размерность вложения не влияет на изометрию")
    _assert_isometry(L1, L2, M)

# ---------------------------------------------------------------------------
# Раннер
# ---------------------------------------------------------------------------

def main():
    filters = [a for a in sys.argv[1:] if not a.startswith("-")]
    verbose = "-v" in sys.argv

    tests, xfails = [], []
    for name, obj in sorted(globals().items()):
        if not callable(obj):
            continue
        if name.startswith("test_"):
            tests.append((name, obj))
        elif name.startswith("xfail_"):
            xfails.append((name, obj))

    if filters:
        tests = [t for t in tests if any(f in t[0] for f in filters)]
        xfails = [t for t in xfails if any(f in t[0] for f in filters)]

    failed, t_start = [], time.time()
    for name, fn in tests:
        # индивидуальный сид: тест воспроизводится в одиночку
        set_random_seed(zlib.crc32(name.encode()))
        t0 = time.time()
        try:
            fn()
            if verbose:
                print("  ok    %-58s %5.2fs" % (name, time.time() - t0))
            else:
                print("  ok    %s" % name)
        except Exception:
            failed.append(name)
            print("  FAIL  %s" % name)
            traceback.print_exc()

    for name, fn in xfails:
        set_random_seed(zlib.crc32(name.encode()))
        try:
            fn()
        except Exception as e:
            print("  xfail %s  (%s)" % (name, type(e).__name__))
        else:
            failed.append(name)
            print("  XPASS %s - ожидалось падение, тест пора включить в сюиту" % name)

    print("\n%d/%d passed, %d xfail, %.1fs"
          % (len(tests) - len([f for f in failed if f.startswith("test_")]),
             len(tests), len(xfails), time.time() - t_start))
    if failed:
        print("failed: %s" % ", ".join(failed))
        sys.exit(1)

main()
