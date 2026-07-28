def compute_fingerprint_optimized(F, SN):
    n = F.nrows()
    f_matrix = matrix(ZZ, n, n)
    b_trivial = [vector(ZZ, n, {idx: 1}) for idx in range(n)]
    
    F_new = copy(F)
    
    SN_new = []
    for lst in SN:
        new_lst = []
        for v in lst:
            v_copy = copy(v)
            v_copy.set_immutable(False)
            new_lst.append(v_copy)
        SN_new.append(new_lst)
    
    for k in range(n):
        kpartial = b_trivial[:k] 
        
        for i in range(k, n):
            f_matrix[k, i] = nb_ext(F_new, SN_new[i], kpartial, k, i)
            
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
            v.set_immutable(True)
            
    return f_matrix, F_new, SN_new