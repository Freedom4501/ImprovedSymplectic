"New Symplectic implementation"
const all_single_qubit_patterns = (
    (true, false, false, true), # X, Z ↦ X, Z
    (false, true, true, true),  # X, Z ↦ Z, Y
    (true, true, true, false),  # X, Z ↦ Y, X
    (false, true, true, false), # X, Z ↦ Z, X - Hadamard
    (true, false, true, true),  # X, Z ↦ X, Y
    (true, true, false, true)   # X, Z ↦ Y, Z - Phase
)

"""Generate a symbolic single-qubit gate given its index. Optionally, set non-trivial phases.

See also: [`enumerate_cliffords`](@ref)."""
function enumerate_single_qubit_gates(index; qubit=1, phases=(false,false))
    @assert index<=6 "Only 6 single-qubit gates exit, up to the choice of phases"
    if phases==(false,false)
        if index==4
            return sHadamard(qubit)
        elseif index==6
            return sPhase(qubit)
        else
            return SingleQubitOperator(qubit, all_single_qubit_patterns[index]..., false, false)
        end
    else
        if index==1
            if     (phases[1], phases[2]) == (false, false)
                return sId1(qubit)
            elseif (phases[1], phases[2]) == (false,  true)
                return sX(qubit)
            elseif (phases[1], phases[2]) == (true,  false)
                return sZ(qubit)
            else
                return sY(qubit)
            end
        else
            return SingleQubitOperator(qubit, all_single_qubit_patterns[index]..., phases...)
        end
    end
end

"""The size of the Clifford group over a given number of qubits, possibly modulo the phases.

For n qubits, not accounting for phases is 2ⁿⁿΠⱼ₌₁ⁿ(4ʲ-1). There are 4ⁿ different phase configurations.

See also: [`enumerate_cliffords`](@ref).
"""
function clifford_cardinality(n::Int; phases=true)
    base = BigInt(2)^(n^2) * prod(1:n) do j; BigInt(4)^j-1 end
    if phases
        base*BigInt(2)^(2n)
    else
        base
    end
end

@inline function _findanticommGS(basis, start, n, padded_n, δn)
    for i in δn+start+1:padded_n
        comm(basis, δn+start, i)==0x1 && return i
    end
    for i in padded_n+δn+start:2padded_n+1
        comm(basis, δn+start, i)==0x1 && return i
    end
    # the following hapens only if the input is P"X___..."
    rowswap!(basis, δn+start, 2padded_n+1; phases=Val(false))
    _findanticommGS(basis, start, n, padded_n, δn)
end

@inline function _eliminateGS(basis, start, n, padded_n, δn)
    for i in δn+start+1:padded_n
        x = comm(basis, δn+start, i)==0x1
        z = comm(basis, padded_n+δn+start, i)==0x1
        z && mul_left!(basis, i, δn+start; phases=Val(false))
        x && mul_left!(basis, i, padded_n+δn+start; phases=Val(false))
    end
    for i in padded_n+δn+start+1:2padded_n+1
        x = comm(basis, δn+start, i)==0x1
        z = comm(basis, padded_n+δn+start, i)==0x1
        z && mul_left!(basis, i, δn+start; phases=Val(false))
        x && mul_left!(basis, i, padded_n+δn+start; phases=Val(false))
    end
end

"""Perform the Symplectic Gram-Schmidt procedure that gives a Clifford operator canonically related to a given Pauli operator.

The algorithm is detailed in [koenig2014efficiently](@cite).

See also: [`enumerate_cliffords`](@ref), [`clifford_cardinality`](@ref)."""
function symplecticGS(pauli::PauliOperator; padded_n=nqubits(pauli))
    n = nqubits(pauli)
    basis = zero(Stabilizer, 2padded_n+1, padded_n)
    δn = padded_n-n
    # fillup the padded tableau
    for i in 1:δn
        basis[i,i] = (true,false)
        basis[padded_n+i,i] = (false,true)
    end
    for i in δn+1:padded_n-1
        basis[i+1,i] = (true,false)
        basis[padded_n+i+1,i] = (false,true)
    end
    for i in 1:n basis[δn+1,δn+i] = pauli[i] end
    basis[padded_n+δn+1,padded_n] = (true,false)
    basis[2padded_n+1,padded_n] = (false,true)
    # end fillup
    doneupto = 1
    while doneupto <= n
        i = _findanticommGS(basis, doneupto, n, padded_n, δn)
        rowswap!(basis, padded_n+δn+doneupto, i; phases=Val(false))
        _eliminateGS(basis, doneupto, n, padded_n, δn)
        doneupto += 1
    end
    CliffordOperator((@view basis[1:2padded_n]))
end

@inline function int_to_bits(n,i)
    Bool[i>>d&0x1 for d in 0:n-1]
end

"""Give the i-th n-qubit Clifford operation, where i∈{1..2ⁿⁿΠⱼ₌₁ⁿ(4ʲ-1)}

The algorithm is detailed in [koenig2014efficiently](@cite).

See also: [`symplecticGS`](@ref), [`clifford_cardinality`](@ref)."""
function enumerate_cliffords(n,i;padded_n=n,onlycoset=false)
    enumerate_cliffords_slow(n,i;padded_n,onlycoset)
end

"""The O(n^4) implementation from [koenig2014efficiently](@cite) -- their algorithm seems wrong as ⟨w'₁|wₗ⟩=bₗ which is not always zero."""
function enumerate_cliffords_slow(n,i;padded_n=n,onlycoset=false) # TODO implement the faster n^3 algorithm
    @assert n<32 # Assuming 64 bit system
    s = 2^(2n)-1
    k = (i-1)%s+1
    pauli = PauliOperator(int_to_bits(2n,k))
    op = symplecticGS(pauli;padded_n)
    basis = tab(op)
    δn = padded_n-n
    idivs = (i-1)÷s
    for j in 0:n-1 # first n bits # w₁ ← w₁+vⱼ
        iszero(idivs>>j&0x1) || mul_left!(basis, padded_n+δn+1, δn+j+1; phases=Val(false))
    end
    for j in n:2n-2 # following n-1 bits # w₁ ← w₁+wⱼ
        iszero(idivs>>j&0x1) || mul_left!(basis, padded_n+δn+1, 2δn+j+2; phases=Val(false))
    end
    for j in 1:n-1 # first n-1 bits after first bit # wⱼ ← wⱼ+v₁ # missing from koenig2014efficiently
        iszero(idivs>>j&0x1) || mul_left!(basis, padded_n+δn+j+1, δn+1; phases=Val(false)) # δn+j+1+n
    end
    for j in n:2n-2 # following n-1 bits # vⱼ ← vⱼ+v₁ # missing from koenig2014efficiently
        iszero(idivs>>j&0x1) || mul_left!(basis, δn+j+2-n, δn+1; phases=Val(false))
    end
    if n==1 || onlycoset
        return op
    else
        subop = enumerate_cliffords(n-1,idivs÷2^(2n-1)+1;padded_n)
        return apply!(subop, op; phases=false)
    end
end


"""
Calculates the symplectic inner product
"""
function inner(v, w)
    t = 0
    for i in 0:(sizeof(v) >> 1)
        t = t + v[2i + 1] * w[2i + 2]
        t = t + w[2i + 1] * v[2i + 2]
    end
    return t % 2
end

"""
Applies transvection Z_k to v
"""
function transvection(k, v)
    return (v + inner(k, v) * k) % 2
end

"""
finds h1, h2 such that y = Z_h1 Z_h2 x
Transvection as described in Lemma 2
Followed the procedure mentioned in the proof of lemma 2
"""
function findTransvection(x, y)
    otp = zeros(Int8, 2, sizeof(x))
    if x == y
        return otp
    end
    if inner(x, y) == 1
        otp[1] = (x + y) % 2
        return otp
    end

    # find a pair both not 00
    z = zeros(sizeof(x))
    for i in 0:(sizeof(x) >> 1)
        if ((x[2i + 1] + x[2i + 2]) != 0) & ((y[2i + 1] + y[2i + 2]) != 0)
            z[2i + 1] = (x[2i + 1] + y[2i + 1]) % 2
            z[2i + 2] = (x[2i + 2] + y[2i + 2]) % 2
            if x[2i + 1] != x[2i + 2]
                z[2i + 1] = 1
            end
        end
        otp[1] = (x + z) % 2
        otp[2] = (y + z) % 2
        return otp
    end

    # didn't find a pair, look for x has 00 and y doesn't, and vice versa

    # first y == 00 and x doesn't
    for i in 1:(sizeof(x) >> 1)
        if ((x[2i + 1] + x[2i + 2]) == 0) & ((y[2i + 1] + y[2i + 2]) != 0)
            if y[2i + 1] == y[2i + 2]
                z[2i + 2] = 1
            else
                z[2i + 2] = y[2i + 1]
                z[2i + 1] = y[2i + 2]
            break
            end 
        end
    end
    otp[1] = (x + z) % 2
    otp[2] = (y + z) % 2
    return otp
end

"""
Returns the number of symplectic group elements
"""
function numOfSymplectic(n)
    x = 1
    for j in 1:n+1
        x = x * numOfCosets(j)
    end
    return x
end

"""
Returns the number of different cosets
"""
function numOfCosets(n) 
    return (2^(2n - 1))*((2^2n)-1)
end

function directSum(m1, m2)
    n1 = length(m1[1])
    n2 = length(m2[1])
    otp = zeros(Int8, n1 + n2, n1 + n2)
    for i in 1:(n1 + 1)
        for j in 1:(n1 + 1)
            otp[i, j] = m1[i, j]
        end
    end

    for i in 1:(n2 + 1)
        for j in 1:(n2 + 1)
            otp[i + n1, j + n1] = m2[i, j]
        end
    end

    return otp
end

function symplectic(i, n)
    # step 1
    s = (1<<2n) - 1
    k = (i % s) + 1
    i = floor(i / s)
    # step 2
    f1 = int_to_bits(2n, k)
    # step 3
    e1 = zeros(Int8, 2n) # define first basis vectors
    e1[0] = 1
    T = findTransvection(e1, f1) # Lemma 2
    # step 4
    # b[0] = b in the text, b[1] ... b[2n−2] are b_3 ... b_2n in the text
    bits = int_to_bits(2n - 1, i % (1<<(2n - 1)))
    # step 5
    eprime = copy(e1) # constructing vector
    for j in 3:(2n + 1)
        eprime[j] = bits[j - 1]
    end
    h0 = transvection(T[1], eprime) # computes h0 using (h1. h2) specifying T
    h0 = transvection(T[1], h0)
    
    # step 6
    if bits[1] == 1
        f1 = f1 * 0
    end
    # f2 is not computed here because step 7 recomputes f2 for us

    # step 7 
    # identity matrix
    id2 = zeros(Int8, 2, 2)
    id2[1, 1] = 1
    id2[2, 2] = 1

    if n != 1
        g = directSum(id2, symplectic(i >> (2n - 1), n - 1))
    else
        # columns f1, f2 as gj
        g = id2
    end

    for j in 1:(2n + 1)
        g[j] = transvection(T[1], g[j])
        g[j] = transvection(T[2], g[j])
        g[j] = transvection(h0, g[j])
        g[j] = transvection(f1, g[j])
    end

    return g
end

function enumerate_cliffords_fast(n, i; padded_n = n, onlycoset = false)
    return symplectic(i, n)
end

"""Give all n-qubit Clifford operations.

The algorithm is detailed in [koenig2014efficiently](@cite).

See also: [`symplecticGS`](@ref), [`clifford_cardinality`](@ref)."""
function enumerate_cliffords(n;padded_n=n,onlycoset=false) # TODO make an enumerator that does not compute the cosets from scratch each time
    if onlycoset
        cosetsize = (2^(2n)-1)*2^(2n-1)
        (enumerate_cliffords(n,i;padded_n,onlycoset=true) for i in 1:cosetsize)
    else
        (enumerate_cliffords(n,i;padded_n,onlycoset=false) for i in 1:clifford_cardinality(n;phases=false))
    end
end

@inline function _change_phases!(op, phases)
    tab(op).phases .= 0x2 .* phases
    op
end

"""Given an operator, return all operators that have the same tableau but different phases.

```jldoctest
julia> length(collect(enumerate_phases(tCNOT)))
16
```

See also: [`enumerate_cliffords`](@ref), [`clifford_cardinality`](@ref)."""
function enumerate_phases(op::CliffordOperator)
    n = nqubits(op)
    (_change_phases!(copy(op), int_to_bits(2n,i)) for i in 0:2^(2n)-1)
end

"""Given a set of operators, return all operators that have the same tableaux but different phases.

```jldoctest
julia> length(collect(enumerate_phases(enumerate_cliffords(2))))
11520
```

See also: [`enumerate_cliffords`](@ref), [`clifford_cardinality`](@ref)."""
function enumerate_phases(ops::Union{AbstractVector,Base.Generator})
    Iterators.flatten(Iterators.map(enumerate_phases, ops))
end
