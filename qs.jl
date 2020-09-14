using Primes

# Solve x such that x^2 = a (mod p) when p is prime
function sqrtmod(a::Integer,p::Integer)
    aa=mod(a,p)

    for i in 1:p
        if isequal(mod(i*i,p), aa)
            return i
        end
    end
end


function sqrtmod2(a::Integer,p::Integer)
    # find biggest s s.t. p-1 = 2^e * s
    e=0
    s=p-1

    while iszero(mod(s, 2))
        s=div(s,2)
        e+=1
    end

    # find n s.t. n^(p-1)/2 = -1 (mod p)
    n = 3
    pp = div(p-1,2)

    while isone(powermod(n,pp,p))
        n += 1
    end

    x=powermod(a,div(s+1,2),p)
    b=powermod(a,s,p)
    g=powermod(n,s,p)
    r=e
    m=1

    while true
        # find m s.t. b^(2^m) = 1 (mod p)
        m=0
        bb=b

        while ! isone(mod(bb, p))
            bb = b*b
            m += 1
        end

        if iszero(m)
            return x
        end

        x = mod(x*powermod(g,(r-m-1)^2,p), p)
        b = mod(b*powermod(g,(r-m)^2,p), p)
        g = powermod(g,(r-m)^2,p)
        r = m
    end
end


function legendre(n, p)
    return powermod(n,div(p-1,2),p)
end


function get_smooths(n, prime_max, range_size, power_max)
    base_primes=Int64[]

    for p in primes(prime_max)
        if isone(legendre(n,p))
            push!(base_primes,p)
        end
    end

    n_base=length(base_primes)
    r=isqrt(n)
    lbound = r - range_size # lower bound
    ubound = r + range_size # upper bound
    size = ubound - lbound+1
    q = Array{BigInt, 1}(undef, size)
	n_bits_q = Array{Int64, 1}(undef, size)
    signs = zeros(Int64,size)
    pows = zeros(Int64,size,n_base)

    for k in lbound:ubound
        i = Int64(k-lbound+1)
        q[i] = k*k-n
        n_bits_q[i] = ndigits(q[i],base=2)

        if q[i]<0
            signs[i]=1
            q[i]=-q[i]
        end
    end

    # sieve for 2
    k = lbound + mod(lbound-1,2)
    while k<=ubound

        i=k-lbound+1
        pows[i,1]=1
        l=2
        pp=2*2

        while iszero(mod(q[i],pp))
            pows[i,1]+=1
            l+=1
            pp*=2
        end
        k+=2
    end

    # sieve for other primes
    for j in 2:n_base
        p=base_primes[j]
        log2p=floor(Int64,log2(p))
        r1=sqrtmod(n,p)
        r2=p-r1
        for r in [r1,r2]
            k = lbound + mod(r - lbound, p)
            @assert mod(k,p)==r

            while k<=ubound

                i=Int64(k-lbound+1)
                pows[i,j]=1
                n_bits_q[i]-=log2p
                l=2
                pp=p*p

                while iszero(mod(q[i],pp))
                    pows[i,j]+=1
                    l+=1
                    n_bits_q[i]-=log2p
                    pp*=p
                end

                k+=p
            end
        end
    end

    thredshold=floor(Int64,log2(n))
    k=lbound
	smooths=Array{Int64, 1}(undef, 0)

    while k<=ubound

        i=Int64(k-lbound+1)

        if n_bits_q[i]<thredshold
            prod=1
            for (p,l) in zip(base_primes,pows[i,:])
                prod*=p^l
            end
            if isequal(prod, q[i])
                push!(smooths,i)
            end
        end
        k+=1
    end

    return (lbound:ubound)[smooths],hcat(signs[smooths],pows[smooths,:])
end


function solve_eq_mod2(nums,pows)
    indices=Array(1:length(nums))
    n=size(pows)[2]
    encoded=mod.(pows, 2) .== 1 # convert array to boolean
	n_bases=size(pows)[2]
    n_nums=size(pows)[1]

    @assert n_nums>n_bases

    for j in 1:n_bases
        found=false

        for i in j:n_nums
            if encoded[i,j]
                if !found
                    found=true
                    encoded[i,:],encoded[j,:]=encoded[j,:],encoded[i,:]
                    indices[i],indices[j]=indices[j],indices[i]
                else
                    encoded[i,:] .⊻= encoded[j,:] # changed from $= from old 2016 code
					encoded[i,j] = true
                end
            end
        end
    end

    return indices,encoded
end


function decode_bits(n)
    a=Array(Int64,0)
    i=1
    j=1

    while n>0
        if isone(n&1)
            push!(a,j)
        end

        n >>= 1
        i <<= 1
        j+=1
    end

    return a
end


function quadratic_sieve(n)
	if isone(n)
		return 0
	end

	if isprime(n)
		return 0
	end

    nums, pows = get_smooths(n, 100000, 12*32768, 27)
    indices, encoded = solve_eq_mod2(nums, pows)
    n_bases=size(pows)[2]
    n_nums=size(pows)[1]

    for i in n_bases+1:n_nums
        prod1=mod(BigInt(nums[indices[i]]),n)
        prod2=BigInt(nums[indices[i]])^2 - n

        for j in (1:n_bases)[encoded[i,:][:]]
            prod1 = mod(prod1*nums[indices[j]],n)
            prod2 *= nums[indices[j]]^2 -n
        end

        r=isqrt(prod2)
        @assert r*r==prod2
        rr=mod(r,n)
        @assert mod(rr*rr-prod1*prod1,n)==0

        if !isequal(rr, prod1) && ! iszero(mod(rr+prod1,n))
            quotient=gcd(rr-prod1,n)

			return quotient
        end
    end
end


# @assert powermod(3,5,7) == 5
# @assert powermod(2,1000000000000000000000000000000000,11) == 1
#
# @assert powermod(4,div(29-1,2),29) == 1
# @assert sqrtmod(6,29) == 8
# @assert sqrtmod(1042387,17) == 7
#
# a=big(1825552363)
# b=big(1197489743)
#
# n=a*b
# @time factor(n)
# @time p=quadratic_sieve(n)
# @assert mod(n,p)==0
#
# print(@time factor(n))

output = quadratic_sieve(n)

if iszero(output)
	println(n, " is already a prime number.  It is not the product of any other primes except $n⋅1.")
else
	println("For input ", n, " (p, q) = ", output, ", ", div(n, output))
end
