include("search_for_mildness_number_field.jl")


struct inertial_graph
    vertices::Vector{Int}
    pseudoforest_edges::Vector{Tuple{Int, Int}}
    additional_edges::Vector{Tuple{Int, Int}}
end


function realization_of_inertial_graph(
    K::AbsSimpleNumField,
    p::Int,
    gamma::inertial_graph,
    SS::Vector{AbsSimpleNumFieldOrderIdeal},
    T::Vector{AbsSimpleNumFieldOrderIdeal};
    bound::Int = 10^3
    )
    @assert length(gamma.additional_edges) == length(SS)
    @assert length(gamma.pseudoforest_edges) == length(gamma.vertices)
    
    M = Matrix{Union{Missing, Int}}(missing,length(gamma.vertices) + length(gamma.additional_edges), length(gamma.vertices))
    for i in 1:(length(gamma.additional_edges) + length(gamma.vertices)), j in 1:length(gamma.vertices)
        M[i,j]=0
    end
    for i in 1:length(gamma.additional_edges)
        M[i,gamma.additional_edges[i][1]]=missing
        M[i,gamma.additional_edges[i][2]]=1
    end
    for i in 1:length(gamma.vertices), j in 1:length(gamma.vertices)
        if (gamma.vertices[i], gamma.vertices[j]) in gamma.pseudoforest_edges
            M[length(gamma.additional_edges)+i, j]=1
        end
    end
    @show M
    return realize_matrix_entries(K, p, M, SS, T; bound = bound)
end


function realize_matrix_entries(
    K::AbsSimpleNumField,
    p::Int,
    M::Matrix{Union{Missing, Int}},
    SS::Vector{AbsSimpleNumFieldOrderIdeal},
    T::Vector{AbsSimpleNumFieldOrderIdeal};
    bound::Int = 10^3, number_of_solutions::Int = 1
    )
    @assert size(M,1) - size(M,2) == length(SS)
    
    OK=maximal_order(K)
    dd=length(SS)
    mm = prod(SS; init = one(OK))

    excluded = Set(vcat(SS, T))

    primes = filter(
        q -> mod(norm(q), p) == 1 && !(q in excluded),
        prime_ideals_up_to(OK, bound)
    )
    
    list_of_S = Vector{Vector{AbsSimpleNumFieldOrderIdeal}}()

    for _ in 1:number_of_solutions
        S=AbsSimpleNumFieldOrderIdeal[]
        cyclic_extensions = Dict{AbsSimpleNumFieldOrderIdeal, ClassField}()
        for i in 1:size(M,2)
            bar = MiniProgressBar(
            header = "Going through candidate primes for $(i)",
            color = Base.info_color(),
            width = 40,
            )

            bar.max=length(primes)

            for k in 1:length(primes)
                bar.current=k
                show_progress(stdout, bar)
                q=primes[k]
                possible_cand=true            
                for j in 1:i-1
                    if M[i+dd, j] == 1
                        if prime_decomposition_type(cyclic_extensions[S[j]], q)[2] != p
                            possible_cand=false
                        end
                    else
                        if prime_decomposition_type(cyclic_extensions[S[j]], q)[3] != p
                            possible_cand=false
                        end
                    end
                end
                if !possible_cand
                    continue
                end
                Clq, Clq_map = ray_class_group(mm*q; n_quo = p)
                T_subgroup = sub(Clq, FinGenAbGroupElem[Clq_map \ t for t in T])[1]
                _, quo_map = quo(Clq, T_subgroup)
                Kq = ray_class_field(Clq_map, quo_map)
                for j in 1:dd
                    if isequal(M[j, i], missing)
                        if prime_decomposition_type(Kq, SS[j])[1] != p
                            possible_cand=false
                        end
                    elseif M[j, i] != 0
                        if prime_decomposition_type(Kq, SS[j])[2] != p
                            possible_cand=false
                        end
                    else
                        if prime_decomposition_type(Kq, SS[j])[3] != p
                            possible_cand=false
                        end
                    end
                end
                for j in 1:i-1
                    if M[j+dd, i] != 0
                        if prime_decomposition_type(Kq,S[j])[2] != p
                            possible_cand=false
                            break
                        end
                    else
                        if prime_decomposition_type(Kq,S[j])[3] != p
                            possible_cand=false
                            break
                        end
                    end
                end
                if possible_cand
                    push!(S, q)
                    cyclic_extensions[q] = Kq
                    break
                end
            end
            if length(S) < i
                @info "Could not find a suitable prime. Consider increasing the bound."
                break
            end
        end
        push!(list_of_S, S)
        filter!(q -> !(q in S), primes)
    end
    if number_of_solutions == 1
        return list_of_S[1]
    else 
        return list_of_S
    end
end