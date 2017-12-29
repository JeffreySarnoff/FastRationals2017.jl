using FastRationals
using BenchmarkTools

function hilbert_matrix(::Type{T}, n::Int=7) where T<:Signed
    num = one(FastRational{T})
    return [num // (T(idx) + T(inx) - one1) for idx in 1:n, inx in 1:n]
end
