def cand_vect(F, SN_i, kpartial, k, i):
    if i < k:
        return []
        
    candidates = []
    for u in SN_i:
        if all((u * F * kpartial[j]) == F[i, j] for j in range(k)):
            candidates.append(u)
            
    return candidates

def nb_ext(F, SN_i, kpartial, k, i):
    return len(cand_vect(F, SN_i, kpartial, k, i))