############################################################################
# Given a number field L and a set of ideals S of a subfield K. 
# The function determines the set of prime ideals of O_L, that 
# divide at least one ideal in S.
############################################################################

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

############################################################################
# Given an extension L/K of number fields and a set of ideals S of O_K.
# This function determines the primes e, f and g for every prime ideal
# of O_K dividing at least one ideal in S. 
# The output is structured as a dictionary having as keys the prime ideals 
# of O_L above S and as associated data a named tuple containing the prime
# below, e, f and g.
############################################################################

function ramification_data(L::NumField, K::NumField, S::Vector{AbsSimpleNumFieldOrderIdeal})
    # Ensure subfield relation
    is_sub, inc = is_subfield(K, L)
    is_sub || error("K must be a subfield of L")

    # Collect all primes of K above S
    S_K = primes_above(K, S)

    # Dictionary: prime in L ↦ (prime in K, ramification index, inertia degree,splitting number)
    data = Dict{AbsSimpleNumFieldOrderIdeal, NamedTuple}()

    for P in S_K
        factorization = factor(inc(P))
        nprimes = length(factorization)   # number of primes above P
        for (Q, e) in factorization
            data[Q] = (
                prime_in_K     = P,
				e   = e,
                f = div(degree(Q), degree(P)),
                g  = nprimes
            )
        end
    end

    return data
end

############################################################################
# This function is supplementary for local_power_rank and takes 
# as arguments the maximal order of a number field K, a set of 
# prime ideals of O_K and a prime p. It computes
#			U_(K_P) \otimes F_p
# for P in S, where S is a set of prime ideals of O_K, p together 
# with maps, allowing to reconstruct maps from O_K into these 
# abelian groups.
############################################################################


function local_data(O_K::NumFieldOrder, S::Vector{AbsSimpleNumFieldOrderIdeal}, p::Int)
    Rs     = Dict{AbsSimpleNumFieldOrderIdeal, Any}()
    Us     = Dict{AbsSimpleNumFieldOrderIdeal, Any}()
    Usmodp = Dict{AbsSimpleNumFieldOrderIdeal, Any}()

    for P in S
        Rs[P]     = quo(O_K, P^3)
        Us[P]     = unit_group(Rs[P][1])
        Usmodp[P] = quo(Us[P][1], p)
    end

    return Rs, Us, Usmodp
end


############################################################################
# This function computes the rank of tau^p.
# It takes as input a number field K and a prime number p and determines
# the rank of the map tau^p associated to a place above p. 
# If the optional parameter rand_choice is set to true, the place is
# chosen randomly otherwise a place with maximal inertia degree is 
# selected.
# It returns the rank of tau and the F_p-dimension of its codomain.
############################################################################


function local_power_rank(K::NumField, p; rand_choice::Bool = false)
    # Ensure p is prime
    is_prime(p) || error("Input $p must be a prime number")

    O_K = maximal_order(K)
    Q, _ = rationals_as_number_field()

    # Ramification data for (K/Q, p)
    ram_data = ramification_data(K, Q, [p * maximal_order(Q)])

    # If only one prime above p, trivial case
    if length(ram_data) == 1
        return 0, 0
    end

    # Select distinguished prime above p
    if rand_choice
        k0 = rand(keys(ram_data))
        f_max = ram_data[k0].f
    else
        f_max = maximum(v.f for v in values(ram_data))
        k0 = first(filter(k -> ram_data[k].f == f_max, keys(ram_data)))
    end

    r1, r2 = signature(K)
    n = degree(K)

    if f_max < r2
        return r1 + r2, n - f_max
    end

    # Remove chosen prime from ramification data
    delete!(ram_data, k0)

    # Local data setup factored out
	S = collect(keys(ram_data))
    Rs, Us, Usmodp = local_data(O_K, S, p)

    # Direct sum of residue unit groups
    V, incs = direct_sum([Usmodp[P][1] for P in S]...)

    # S-unit group at k0
    sUnits, sUnit_map = sunit_group([k0])
    l = Any[]  # relations list

    for e in gens(sUnits)
        l_entry = zero(V)
        a = sUnit_map(e)

        # Normalize a to be in O_K
        a = Hecke._check_elem_in_order(a, O_K)[1] ? O_K(a) : O_K(inv(a))

        # Accumulate images under inclusions
        for inc in incs
            P = first(filter(k -> domain(inc) == Usmodp[k][1], S))
            l_entry += inc(Usmodp[P][2](Us[P][2] \ Rs[P][2](a)))
        end

        push!(l, l_entry)
    end

    tau = hom(sUnits, V, l)

    return (
        Int(round(log(ZZ(p), order(image(tau)[1])))),
        Int(round(log(ZZ(p), order(V))))
    )
end

############################################################################
# This function is supplementary and outputs the probaility that
# a randomly chosen r x k matrix over F_p has full rank. Here p 
# can be a prime power.
############################################################################

function prob_full_rank(r::Int, k::Int, p; prec::Int = precision(BigFloat))
    q = BigFloat(p; precision = prec)
	if k==0 
		return 1
	end
    return prod(1 - inv(q^(r - i)) for i in 0:k-1)
end

############################################################################
# Given a number field K, a set of integers, this function computes how 
# many primes in the given set satisfy the conditions of Theorem 6.3.
# The optional parameter time_limit determines after how many seconds
# the computation is stopped. In this case an additional output shows 
# at which prime the process was aborted. The optional parameter 
# failed_list decides wether only the number of failed primes or the 
# set containing them is returned. 
#
# The output is a named tuple of the form 
# 	(
#	unramified = ..., 		(number of unramified primes)
#	trivial_negative = ..., 	(number of trivial negative cases)
#	valid = ..., 			(number of primes for which tau is surjective)
#	expected = ..., 			(expected number of valid primes)
#	failed = ..., 			(number or list of non-trivial failed primes)
#	stopped_at = ...			(only present if time_limit is set)
#	)
############################################################################

function rank_with_varying_prime(K::NumField, interval; time_limit::Real = 0, failed_list::Bool = false)
    r1, r2 = signature(K)
    O_K = maximal_order(K)
    r = r1 + r2

    unram_primes          = 0
    trivial_negative_cases = 0
    number_of_valid_primes = 0
    number_of_expected_primes = big"0.0"   # use BigFloat accumulator
    failed_primes = Int[]

    t0 = time()

    for p in interval
        # skip if not prime or ramified
        if !is_prime(p) || p ∈ ramified_primes(O_K)
            continue
        end
        unram_primes += 1

        # local rank computation
        rk, dim = local_power_rank(K, p)

        if rk < dim
            if r < dim
                trivial_negative_cases += 1
            else
                push!(failed_primes, p)
            end
        else
            number_of_valid_primes += 1
        end

        number_of_expected_primes += prob_full_rank(r, dim, p)

        # stop if time limit exceeded
        if time_limit > 0 && (time() - t0 > time_limit)
            return (;
                unramified 		= unram_primes,
                trivial_negative 	= trivial_negative_cases,
                valid    		= number_of_valid_primes,
                expected 		= number_of_expected_primes,
                failed   		= failed_list ? failed_primes : length(failed_primes),
                stopped_at 		= p,
            )
        end
    end

    return (;
        unramified 		= unram_primes,
        trivial_negative 	= trivial_negative_cases,
        valid    		= number_of_valid_primes,
        expected 		= (Float64)(number_of_expected_primes),
        failed   		= failed_list ? failed_primes : length(failed_primes),
    )
end

############################################################################
# Given an irreducible polynomial f(X,t)∈ Q[X,t], a prime p and a set of
# parameters, the function computes for how many parameters λ, f(X,λ) is
# irreducible and if the number field defined by f(X,λ) satsifies the 
# conditions of Theorem 6.3 with respect to the prime p. 
#
# The output is a named tuple of the form 
# 	(
#	possible 	= ...,		(number of parameters with f(X,λ) irreducible)
#	valid 		= ...,		(number of param. for which tau is surjective)
#	failed 		= ...,		(number of param. for which tau is not surjective)
#	expected 	= ...		(expected number of valid parameters)
#	)
############################################################################

function rank_with_varying_field(g::QQMPolyRingElem, p, range)
    Qt, t = polynomial_ring(QQ)

    is_irreducible(g) || error("The given polynomial is not irreducible!")

    possible_params = 0
	valid_params = 0
    failed_params = 0
    expected_number = big"0.0"

    for λ in range
        # Skip if specialization is reducible
        if !is_irreducible(g(t, λ))
            continue
        end
		
        K, _ = number_field(g(t, λ))
        O_K = maximal_order(K)

        # Skip if p is ramified
        if p ∈ ramified_primes(O_K)
            continue
        end
		
		possible_params += 1

        rk, dim = local_power_rank(K, p)
		
		if rk == dim
			valid_params += 1
		else
			failed_params += 1
		end 
        r1, r2 = signature(K)
        expected_number += prob_full_rank(r1+r2, dim, p)
    end

    return (;
        possible 	= possible_params,
        valid 		= valid_params,
        failed 		= failed_params,
        expected 	= (Float64)(expected_number),
    )
end