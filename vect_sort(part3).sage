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
