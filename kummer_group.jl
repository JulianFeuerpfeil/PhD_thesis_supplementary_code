using Oscar

function kummer_group(K::AbsSimpleNumField, S, m::Int)
    @assert m > 0
    @assert all(is_prime, S)
    O_K=maximal_order(K)
    for P in S
        @assert order(P) == O_K
        @assert valuation(m,P)==0
    end
    # compute S-class group and generators; Can this be improved by using the fact that we only need the S-class group?
    Cl, cl_map = class_group(K)
    if order(Cl)==1 
        T=[]
        T_units, T_unit_map = unit_group(O_K)
    else
        T=[cl_map(g) for g in gens(Cl)]
        T_units, T_unit_map = sunit_group(T)
    end
    T_units_mod_m,T_units_mod_m_map = quo(T_units, m)
    
    #create the homomorphism from T_units_mod_m to drect sum of local conditions
    local_conditions = Dict{AbsSimpleNumFieldOrderIdeal, FinGenAbGroup}()
    local_maps = Dict{AbsSimpleNumFieldOrderIdeal, Map}() 
    for P in S
        res,res_map=quo(O_K,P)
        res_units,res_units_map=unit_group(res)
        res_units_mod_m,res_units_mod_m_map=quo(res_units,m)
        local_conditions[P]=res_units_mod_m
        local_maps[P]=hom(T_units_mod_m,res_units_mod_m,[res_units_mod_m_map(res_units_map\ res_map((O_K)(T_unit_map(T_units_mod_m_map \ e )))) for e in gens(T_units_mod_m)])
    end
    for P in T 
        Zm=abelian_group([m])
        g=gens(Zm)[1]
        local_conditions[P]=Zm
        local_maps[P]=hom(T_units_mod_m,local_conditions[P],[g*valuation(T_unit_map(T_units_mod_m_map \ e ),P) for e in gens(T_units_mod_m)])
    end
    key_list=collect(keys(local_conditions))
    if length(key_list)==0
        return T_units_mod_m
    end
    V,incs=direct_sum([local_conditions[key_list[i]] for i in 1:length(key_list)]...)
    tau_values=[]
    for e in gens(T_units_mod_m)
        a=zero(V)
        for i in 1:length(key_list)
            a=a+incs[i](local_maps[key_list[i]](e))
        end
        push!(tau_values,a)
    end
    tau=hom(T_units_mod_m,V,tau_values)
    return kernel(tau)[1]
end



function primes_above(L::NumField, S::Vector{AbsSimpleNumFieldOrderIdeal})
    isempty(S) && return AbsSimpleNumFieldOrderIdeal[]

    O_K = order(first(S))

    # Check all ideals belong to the same order
    all(I -> order(I) == O_K, S) || error("All ideals must belong to the same order")

    K = number_field(O_K)
    is_sub, inc = is_subfield(K, L)
    is_sub || error("K must be a subfield of L")

    # Collect all prime ideals above S in L
    return unique([P for I in S for (P, _) in factor(inc(I))])
end