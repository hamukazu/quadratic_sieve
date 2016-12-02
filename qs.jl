
# a^n mod m
function powmod(a::Integer,n::Integer,m::Integer)
    r=1
    b=a
    while n > 0
        if mod(n,2) == 1
            r=mod((r*b), m)
        end
        n=div(n,2)
        b=mod((b*b), m)
    end
    return r
end

# a^(n^2) mod m
function pow2mod(a::Integer,n::Integer,m::Integer)
    r=a
    for i=1:n
        r = mod((r*r), m)
    end
    return r
end

# Solve x such that x^2 = a (mod p) when p is prime
function sqrtmod(a::Integer,p::Integer)
    aa=a%p
    for i in 1:p
        if i*i%p==aa
            return i
        end
    end
end

function sqrtmod2(a::Integer,p::Integer)
    # find biggest s s.t. p-1 = 2^e * s
    e=0
    s=p-1
    while s % 2 == 0 
        s=div(s,2)
        e+=1
    end
    # find n s.t. n^(p-1)/2 = -1 (mod p)
    n = 3
    pp = div(p-1,2)
    while powmod(n,pp,p) == 1
        n += 1
    end
    x=powmod(a,div(s+1,2),p)
    b=powmod(a,s,p)
    g=powmod(n,s,p)
    r=e
    m=1
    @show x,b,g,r
    while true
        # find m s.t. b^(2^m) = 1 (mod p)
        m=0
        bb=b
        while bb % p !=1
            bb = b*b
            m += 1
        end
        if m==0
            return x
        end
        x = (x*pow2mod(g,r-m-1,p)) % p
        b = (b*pow2mod(g,r-m,p)) % p
        g = pow2mod(g,r-m,p)
        r = m
    end
end

function legendre(n, p)
    return powmod(n,div(p-1,2),p)
end

function get_smooths(n, prime_max, range_size, power_max)
    base_primes=Int64[]
    for p in primes(prime_max)
        if legendre(n,p)==1
            push!(base_primes,p)
        end
    end
    n_base=length(base_primes)
    r=isqrt(n)
    lbound=r-range_size # lower bound
    ubound=r+range_size # upper bound
    size=ubound-lbound+1
    q = Array(Int64,size)
    n_bits_q = Array(Int64,size)
    signs = zeros(Int64,size)
    pows = zeros(Int64,size,n_base)
    for k in lbound:ubound
        i=Int64(k-lbound+1)
        @show i
        q[i] = k*k-n
        n_bits_q[i] = ndigits(q[i],2)
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
        while mod(q[i],pp)==0
            pows[i,1]+=1
            l+=1
            pp*=p
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
                while mod(q[i],pp)==0
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
    smooths=Array(Int64,0)
    while k<=ubound
        i=Int64(k-lbound+1)
        if n_bits_q[i]<thredshold
            prod=1
            for (p,l) in zip(base_primes,pows[i,:])
                prod*=p^l
            end
            if prod==q[i]
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
    encoded=convert( Array{Bool},mod(pows,2) )
    n_bases=size(pows)[2]
    n_nums=size(pows)[1]
    for j in 1:n_bases
        found=false
        for i in j:n_nums
            if encoded[i,j]
                if !found
                    found=true
                    encoded[i,:],encoded[j,:]=encoded[j,:],encoded[i,:]
                    indices[i],indices[j]=indices[j],indices[i]
                else
                    encoded[i,:] $= encoded[j,:]
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
        if n&1==1
            push!(a,j)
        end
        n >>= 1
        i <<= 1
        j+=1
    end
    return a
end

function quadratic_sieve(n)
    m=floor(Int64, exp( 3/4*sqrt(2*log(n)*log(log(n))) ) )
    m=max(20,m)
    prime_max=200
    b=floor(Int64, log(n)/2+log(m)-2*log(prime_max) )
    b=max(5,b)
    @show m,b
    nums, pows = get_smooths(n, prime_max, 100000, b)
    indices, encoded = solve_eq_mod2(nums, pows)
    n_bases=size(pows)[2]
    n_nums=size(pows)[1]
    @assert n_nums>n_bases
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
        if rr!=prod1 && mod(rr+prod1,n)!=0
            quotient=gcd(rr-prod1,n)
            return quotient
        end
    end
end


@assert powmod(3,5,7) == 5
@assert powmod(2,1000000000000000000000000000000000,11) == 1

@assert powmod(4,div(29-1,2),29) == 1
@assert sqrtmod(6,29) == 8
@assert sqrtmod(1042387,17) == 7

nums,pows = get_smooths(930091,43,200,5)
@show nums
@show pows
indices,encoded = solve_eq_mod2(nums,pows)
@show indices
@show encoded

p=quadratic_sieve(930091)
@show p, 930091 % p
return

a=BigInt(12707341651684921770863912066739924799)
b=BigInt(559213569296432442040136986819559513221)
a=BigInt(21186486689341429849)
b=BigInt(35205422048983390723)
n=a*b
#@time factor(n)
@time p=quadratic_sieve(n)
@assert mod(n,p)==0
