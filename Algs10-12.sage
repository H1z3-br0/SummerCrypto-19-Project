def bilinear(F, x, y):
    return x.dot_product(F * y)

# Algorithm 10
# Construct the sets SN_i^(2).

# INPUT:
#         F1 -- Gram matrix of lattice L1
#         F2 -- Gram matrix of lattice L2
#         S2 -- list of short vectors of lattice L2

# OUTPUT:
#         SN2 -- list of sets SN2_i

def same_norm(F1, F2, S2):
    D1 = list(F1.diagonal())

    norm_to_indices = {}

    for i, d in enumerate(D1):
        norm_to_indices.setdefault(d, []).append(i)

    SN2 = [[] for _ in range(F1.ncols())]

    for u in S2:
        norm = bilinear(F2, u, u)

        for i in norm_to_indices.get(norm, []):
            SN2[i].append(u)

    return SN2

# Algorithm 11.
# Construct the candidate set C_i^k.

# INPUT:
#     F1       -- Gram matrix of L1
#     F2       -- Gram matrix of L2
#     SN2      -- output of same_norm()
#     part_iso -- [v1,...,v_{k-1}]
#     k        -- current basis vector (1-based)
#     i        -- candidate set index (1-based)

# OUTPUT:
#     C_i^k

def cand_vect_iso(F1, F2, SN2, part_iso, k, i):
    if i < k:
        return []

    C_i = []

    for u in SN2[i - 1]:
        ok = True

        for j in range(k - 1):
            if bilinear(F2, u, part_iso[j]) != F1[k - 1, j]:
                ok = False
                break

        if ok:
            C_i.append(u)

    return C_i

# Algorithm 12.
# Check whether [v1,...,vi] is an i-partial isometry.

# INPUT:
#     F1       -- Gram matrix of L1
#     F2       -- Gram matrix of L2
#     part_iso -- [v1,...,vi]

# OUTPUT:
#     True or False

def is_i_partial(F1, F2, part_iso):
    i = len(part_iso)

    ans = True

    for j in range(i):

        if bilinear(F2, part_iso[i - 1], part_iso[j]) != F1[i - 1, j]:
            ans = False
            break

    return ans