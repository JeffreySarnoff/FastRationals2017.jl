module FastRationals

export FastRational


import Base: show, read, write, convert, promote_rule, widen,
    checked_add, checked_sub, checked_mul, power_by_squaring,
    numerator, denominator, rationalize, isinteger, iszero,
    sign, signbit, copysign, typemin, typemax,
    ==, <=, <, cmp, -, +, *, inv, /, //, rem, mod, fma, div, fld, cld,
    trunc, floor, ceil, round, ^

import Base.Checked: add_with_overflow, sub_with_overflow, mul_with_overflow


const ISREDUCED = Val{:ISREDUCED}
const MAYREDUCE = Val{:MAYREDUCE}


struct FastRational{R, T} <: Real
    numer::T
    denom::T
end

FastRational{T}(numer::T) = FastRational{MAYREDUCE, T}(numer, one(T))
FastRational{T}(::Type{MAYREDUCE}, numer::T) = FastRational{MAYREDUCE, T}(numer, one(T))
FastRational{T}(::Type{ISREDUCED}, numer::T) = FastRational{ISREDUCED, T}(numer, one(T))

FastRational{T}(numer::T, denom::T) = FastRational{MAYREDUCE, T}(numer, denom)
FastRational{T}(::Type{MAYREDUCE}, numer::T, denom::T) = FastRational{MAYREDUCE, T}(numer, denom)
FastRational{T}(::Type{ISREDUCED}, numer::T, denom::T) = FastRational{ISREDUCED, T}(numer, denom)

numerator{R, T}(q::FastRational{R, T}) = q.numer
denominator{R, T}(q::FastRational{R, T}) = q.denom

isreduced{R,T}(q::FastRational{R, T}) = R === ISREDUCED
mayreduce{R,T}(q::FastRational{R, T}) = R === MAYREDUCE

# http://lemire.me/blog/2013/12/26/fastest-way-to-compute-the-greatest-common-divisor/
function fastgcd{T}(u::T, v::T)
    u===zero(T) && return v
    v===zero(T) && return u
    shift = trailing_zeros(u|v)
    u = u >> trailing_zeros(u)
    v = v >> trailing_zeros(v)
    u, v = minmax(u, v)
    v = v - u
    while (v !== zero(T))
        v = v >> trailing_zeros(v)
        u, v = minmax(u, v)
        v = v - u
     end
     return u << shift
end


function cannonical{T}(numer::T, denom::T)
    denom = abs(denom)
    gcdivisor = fastgcd(denom, numer)
    FastRational(ISREDUCED, div(numer, gcdivisor), div(denom, gcdivisor))
end

function cannonical{R,T}(q::FastRational{R,T})
    denom = abs(q.denom)
    gcdivisor = fastgcd(denom, q.numer)
    FastRational(ISREDUCED, div(q.numer, gcdivisor), div(denom, gcdivisor))
end


function show{R,T}(io::IO, x::FastRational{R,T})
    z = isreduced(x) ? x : cannonical(x)
    print(io, numerator(z), "//", denominator(z))
end

function read{R, T}(s::IO, ::Type{FastRational{R, T}})
    r = read(s,T)
    i = read(s,T)
    return cannonical(r,i)
end

function write{R,T}(s::IO, x::FastRational{R,T})
    z = isreduced(x) ? x : cannonical(x)
    return write(s, numerator(z), denominator(z))
end



sign(x::FastRational) = oftype(x, sign(x.numer))
signbit(x::FastRational) = signbit(x.numer)
copysign(x::FastRational, y::Real) = FastRational(copysign(x.numer, y), x.denom)
copysign(x::FastRational, y::FastRational) = FastRational(copysign(x.numer, y.numer), x.denom)


isinteger{R,T}(x::FastRational{R,T}) = abs(x.denom) === one(T)
iszero{R,T}(x::FastRational{R,T}) = abs(x.numer) === zero(T)



Base.Math.abs{R,T}(x::FastRational{R,T}) = FastRational{R,T}(abs(x.numer), x.denom)

Base.Math.inv{R,T}(x::FastRational{R,T}) = FastRational{R,T}(x.denom, x.numer)

function Base.:(-){R,T}(x::FastRational{R,T})
    x.numer === typemin(T) && throw(OverflowError())
    return FastRational{R,T}(-x.numer, x.denom)
end

function Base.:(+){R,T}(x::FastRational{R,T}, y::FastRational{R,T})
    ovf = false
    numer_a, ovfl = mul_with_overflow(x.numer, y.denom)
    ovf = ovf | ovfl
    numer_b, ovfl = mul_with_overflow(x.denom, y.numer)
    ovf = ovf | ovfl
    numer, ovfl = add_with_overflow(numer_a, numer_b)
    ovf = ovf | ovfl
    denom, ovfl = mul_with_overflow(x.denom, y.denom)
    ovf = ovf | ovfl

    !ovf && return FastRational(MAYREDUCE, numer, denom)

    x = ifelse(isreduced(x), x, cannonical(x))
    y = ifelse(isreduced(y), y, cannonical(y))

    numer_a, ovfl = mul_with_overflow(x.numer, y.denom)
    ovf = ovf | ovfl
    numer_b, ovfl = mul_with_overflow(x.denom, y.numer)
    ovf = ovf | ovfl
    numer, ovfl = add_with_overflow(numer_a, numer_b)
    ovf = ovf | ovfl
    denom, ovfl = mul_with_overflow(x.denom, y.denom)
    ovf = ovf | ovfl

    ovf && throw(OverflowError())

    return FastRational(MAYREDUCE, numer, denom)
end


function Base.:(-){R,T}(x::FastRational{R,T}, y::FastRational{R,T})
    ovf = false
    numer_a, ovfl = mul_with_overflow(x.numer, y.denom)
    ovf = ovf | ovfl
    numer_b, ovfl = mul_with_overflow(x.denom, y.numer)
    ovf = ovf | ovfl
    numer, ovfl = sub_with_overflow(numer_a, numer_b)
    ovf = ovf | ovfl
    denom, ovfl = mul_with_overflow(x.denom, y.denom)
    ovf = ovf | ovfl

    !ovf && return FastRational(MAYREDUCE, numer, denom)

    x = ifelse(isreduced(x), x, cannonical(x))
    y = ifelse(isreduced(y), y, cannonical(y))

    numer_a, ovfl = mul_with_overflow(x.numer, y.denom)
    ovf = ovf | ovfl
    numer_b, ovfl = mul_with_overflow(x.denom, y.numer)
    ovf = ovf | ovfl
    numer, ovfl = sub_with_overflow(numer_a, numer_b)
    ovf = ovf | ovfl
    denom, ovfl = mul_with_overflow(x.denom, y.denom)
    ovf = ovf | ovfl

    ovf && throw(OverflowError())

    return FastRational(MAYREDUCE, numer, denom)
end


function Base.:(*){R,T}(x::FastRational{R,T}, y::FastRational{R,T})
    ovf = false
    numer, ovfl = mul_with_overflow(x.numer, y.numer)
    ovf = ovf | ovfl
    denom, ovfl = mul_with_overflow(x.denom, y.denom)
    ovf = ovf | ovfl

    if ovf
       x = ifelse(isreduced(x), x, cannonical(x))
       y = ifelse(isreduced(y), y, cannonical(y))

       ovf = false
       numer, ovfl = mul_with_overflow(x.numer, y.numer)
       ovf = ovf | ovfl
       denom, ovfl = mul_with_overflow(x.denom, y.denom)
       ovf = ovf | ovfl

       ovf && throw(OverflowError())
    end

    return FastRational(MAYREDUCE, numer, denom)
end


function Base.:(//){R,T}(x::FastRational{R,T}, y::FastRational{R,T})
    ovf = false
    numer, ovfl = mul_with_overflow(x.numer, y.denom)
    ovf = ovf | ovfl
    denom, ovfl = mul_with_overflow(x.denom, y.numer)
    ovf = ovf | ovfl

    if ovf
       x = ifelse(isreduced(x), x, cannonical(x))
       y = ifelse(isreduced(y), y, cannonical(y))

       ovf = false
       numer, ovfl = mul_with_overflow(x.numer, y.denom)
       ovf = ovf | ovfl
       denom, ovfl = mul_with_overflow(x.denom, y.numer)
       ovf = ovf | ovfl

       ovf && throw(OverflowError())
    end

    return FastRational(MAYREDUCE, numer, denom)
end


end # module
