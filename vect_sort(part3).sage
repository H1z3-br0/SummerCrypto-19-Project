def same_norm(Gram,s):
    length = [0]*Gram.ncols()
    n
    result =[[] for _ in range(len(Gram))]
    
    for ind in range(len(Gram)):
        lenght[ind] = Gram[ind][ind]

    for ind_i in range(len(length)):
        for ind_j in range(len(s)):
            v = s[ind_j]
            if (v*Gram*v.column() == length[ind_i]):
                result[ind_i].append(v)

    return result

def allowed_vect(Gram, sn_res, found_vec_img, vect_ind, step):
    result = []
    for u in sn_res:
        flag = True
        
        for ind_i in range(step - 1):
            mult = u.dot_product(found_vec_img[ind_i] * Gram)
            if (Gram[vect_ind][ind_i] != mult):
                flag = False
                break
            else: continue 
                
        if (flag):
            result.append(u)

    return result
        
    
