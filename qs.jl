
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

function sieve(n, range_size, power_max)
    base_primes=[]
    for p in primes(43)
        if legendre(n,p)==1
            push!(base_primes,p)
        end
    end
    n_base=length(base_primes)
    r=isqrt(n)
    @show r
    lbound=r-range_size # lower bound
    ubound=r+range_size # upper bound
    size=ubound-lbound+1
    q = Array(Int64,size)
    n_bits_q = Array(Int64,size)
    signs = zeros(Int64,size)
    pows = zeros(Int64,size,n_base)
    for k in lbound:ubound
        i=k-lbound+1
        q[i] = k*k-n
        n_bits_q[i] = ndigits(q[i],2)
        if q[i]<0
            signs[i]=1
            q[i]=-q[i]
        end
    end
    @show base_primes
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
            @assert k%p==r
            while k<=ubound
                i=k-lbound+1
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
    smooths=[]
    while k<=ubound
        i=k-lbound+1
        if n_bits_q[i]<thredshold
            prod=1
            for (p,l) in zip(base_primes,pows[i,:])
                prod*=p^l
            end
            @show q[i],prod
            if prod==q[i]
                push!(smooths,i)
            end
        end                   
        k+=1
    end
    @show smooths
    return ((lbound:ubound)[smooths],signs[smooths],pows[smooths,:])
end

function solve_eq_mod2(nums,signs,pows)
    indices=1:len(nums)
    n=size(pows)[2]
    v=Array(n)
    s=2
    for i in 1:n
        v[2]=s
        s*2
    encoded=mod(pows,2)*v+signs
end

@show powmod(3,5,7)
@show powmod(2,1000000000000000000000000000000000,11)

@show powmod(4,div(29-1,2),29)
@show sqrtmod(6,29)

@show sqrtmod(1042387,17)
@show sieve(930091,200,5)
