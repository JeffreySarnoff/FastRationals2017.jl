module FastRationals

export FastRational


import Base: promote_rule, convert,
    show, read, write, convert, promote_rule, widen,
    checked_add, checked_sub, checked_mul, power_by_squaring,
    numerator, denominator, rationalize, isinteger, iszero,
    sign, signbit, copysign, flipsign, typemin, typemax,
    ==, <=, <, cmp, -, +, *, inv, /, //, rem, mod, fma, div, fld, cld,
    trunc, floor, ceil, round, ^

import Base.Checked: add_with_overflow, sub_with_overflow, mul_with_overflow

const SignedInt  = Union{Int64, Int32, Int16, Int128, BigInt, Int8}

const IsReduced  = Val{:IsReduced}
const MayReduce  = Val{:MayReduce}
const Reduceable = Union{IsReduced, MayReduce}

# T is a primitive Signed type
# R is the IsReduced or MayReduce parameter

struct FastRational{T, R} <: Real
    num::T
    den::T
end

@inline numer(q::FastRational{T, R}) where {T<:SignedInt, R<:Reduceable} = q.num
@inline denom(q::FastRational{T, R}) where {T<:SignedInt, R<:Reduceable} = q.den
@inline numerator(q::FastRational{T, R}) where {T<:SignedInt, R<:Reduceable} = q.num
@inline denominator(q::FastRational{T, R}) where {T<:SignedInt, R<:Reduceable} = q.den

FastRational(::Type{R}, num::T, den::T) where {T<:SignedInt, R<:Reduceable} = FastRational{T, R}(num, den)

@inline isreduced(q::FastRational{T, R}) where {T<:SignedInt, R<:Reduceable} = R === IsReduced
@inline mayreduce(q::FastRational{T, R}) where {T<:SignedInt, R<:Reduceable} = R === MayReduce

@inline FastRational(numer::T) where {T<:SignedInt} = FastRational{T, MayReduce}(numer, one(T))
@inline FastRational(::Type{MayReduce}, numer::T) where {T<:SignedInt} = FastRational{T, MayReduce}(numer, one(T))
@inline FastRational(::Type{IsReduced}, numer::T) where {T<:SignedInt} = FastRational{T, IsReduced}(numer, one(T))

@inline FastRational(numer::T, denom::T) where {T<:SignedInt} = FastRational{T, MayReduce}(numer, denom)
@inline FastRational(::Type{MayReduce}, numer::T, denom::T) where {T<:SignedInt} = FastRational{T, MayReduce}(numer, denom)
@inline FastRational(::Type{IsReduced}, numer::T, denom::T) where {T<:SignedInt} = FastRational{T, IsReduced}(numer, denom)



# FastRationals are created with denom == abs(denom)
function cannonical(num::T, den::T) where {T<:SignedInt}
    num = flipsign(num, den)
    den = abs(den)
    gcdivisor = gcd(den, num)
    gcdivisor === one(T) && return FastRational{T, IsReduced}(num, den)
    num = div(num, gcdivisor)
    den = div(den, gcdivisor)
    return FastRational{T, IsReduced}(num, den)
end

# FastRationals are created with denom == abs(denom)
function cannonical(q::FastRational{T, R}) where {T<:SignedInt, R<:Reduceable}
    den = denom(q)
    num = numer(q)
    gcdivisor = gcd(den, num)
    gcdivisor === one(T) && return FastRational{T, IsReduced}(num, den)
    num = div(num, gcdivisor)
    den = div(den, gcdivisor)
    return FastRational{T, IsReduced}(num, den)
end



@inline sign(x::FastRational{T, R})  where {T<:SignedInt, R<:Reduceable} = oftype(x, sign(numer(x)))
@inline signbit(x::FastRational{T, R})  where {T<:SignedInt, R<:Reduceable} = signbit(numer(x))
@inline copysign(x::FastRational{T,R}, y::Real) where {T<:SignedInt, R<:Reduceable} = FastRational{T, R}(copysign(numer(x), y), denom(x))
@inline copysign(x::FastRational{T, R}, y::FastRational{T, R})  where {T<:SignedInt, R<:Reduceable} = FastRational{T,R}(copysign(numer(x), numer(y)), denom(x))
@inline flipsign(x::FastRational{T, R}, y::Real)  where {T<:SignedInt, R<:Reduceable} = FastRational{T, R}(flipsign(numer(x), y), denom(x))
@inline flipsign(x::FastRational{T, R}, y::FastRational{T, R})  where {T<:SignedInt, R<:Reduceable} = FastRational{T, R}(flipsign(numer(x), numer(y)), denom(x))

@inline isinteger(x::FastRational{T, R}) where {T<:SignedInt, R<:Reduceable} = abs(denom(x)) === one(T)
@inline iszero(x::FastRational{T, R})  where {T<:SignedInt, R<:Reduceable} = abs(numer(x)) === zero(T)

@inline Base.Math.abs(x::FastRational{T, R})  where {T<:SignedInt, R<:Reduceable}  = FastRational{T, R}(abs(numer(x)), denom(x))

@inline Base.Math.inv(x::FastRational{T, R})  where {T<:SignedInt, R<:Reduceable} = FastRational{T, R}(denom(x), numer(x))

@inline function Base.:(-)(x::FastRational{T, R})  where {T<:SignedInt, R<:Reduceable} 
    numer(x) === typemin(T) && throw(OverflowError())
    return FastRational{T, R}(-numer(x), denom(x))
end

function Base.:(+)(x::FastRational{T, IsReduced}, y::FastRational{T, IsReduced})  where {T<:SignedInt} 
    ovf = false
    num_a, ovfl = mul_with_overflow(numer(x), denom(y))
    ovf |= ovfl
    num_b, ovfl = mul_with_overflow(denom(x), numer(y))
    ovf |= ovfl
    num, ovfl = add_with_overflow(num_a, num_b)
    ovf |= ovfl
    den, ovfl = mul_with_overflow(denom(x), denom(y))
    ovf |= ovfl

    ovf && throw(OverflowError())

    return FastRational{T, MayReduce}(num, den)
end

function Base.:(+)(x::FastRational{T, MayReduce}, y::FastRational{T, MayReduce})  where {T<:SignedInt} 
    ovf = false
    num_a, ovfl = mul_with_overflow(numer(x), denom(y))
    ovf |= ovfl
    num_b, ovfl = mul_with_overflow(denom(x), numer(y))
    ovf |= ovfl
    num, ovfl = add_with_overflow(num_a, num_b)
    ovf |= ovfl
    den, ovfl = mul_with_overflow(denom(x), denom(y))
    ovf |= ovfl

    !ovf && return FastRational{T, MayReduce}(num, den)

    x = cannonical(x)
    y = cannonical(y)

    num_a, ovfl = mul_with_overflow(numer(x), denom(y))
    ovf |= ovfl
    num_b, ovfl = mul_with_overflow(denom(x), numer(y))
    ovf |= ovfl
    num, ovfl = add_with_overflow(num_a, num_b)
    ovf |= ovfl
    den, ovfl = mul_with_overflow(denom(x), denom(y))
    ovf |= ovfl

    ovf && throw(OverflowError())

    return FastRational{T, MayReduce}(num, den)
end

function Base.:(+)(x::FastRational{T, R}, y::FastRational{T, R}) where {T<:SignedInt, R<:Reduceable} 
    ovf = false
    num_a, ovfl = mul_with_overflow(numer(x), denom(y))
    ovf |= ovfl
    num_b, ovfl = mul_with_overflow(denom(x), numer(y))
    ovf |= ovfl
    num, ovfl = add_with_overflow(num_a, num_b)
    ovf |= ovfl
    den, ovfl = mul_with_overflow(denom(x), denom(y))
    ovf |= ovfl

    !ovf && return FastRational{T, MayReduce}(num, den)

    x = isreduced(x) ? x : cannonical(x)
    y = isreduced(y) ? y : cannonical(y)

    num_a, ovfl = mul_with_overflow(numer(x), denom(y))
    ovf |= ovfl
    num_b, ovfl = mul_with_overflow(denom(x), numer(y))
    ovf |= ovfl
    num, ovfl = add_with_overflow(num_a, num_b)
    ovf |= ovfl
    den, ovfl = mul_with_overflow(denom(x), denom(y))
    ovf |= ovfl

    ovf && throw(OverflowError())

    return FastRational{T, MayReduce}(num, den)
end

function Base.:(+)(x::FastRational{T, IsReduced}, y::FastRational{T, MayReduce}) where {T<:SignedInt} 
    ovf = false
    num_a, ovfl = mul_with_overflow(numer(x), denom(y))
    ovf |= ovfl
    num_b, ovfl = mul_with_overflow(denom(x), numer(y))
    ovf |= ovfl
    num, ovfl = add_with_overflow(num_a, num_b)
    ovf |= ovfl
    den, ovfl = mul_with_overflow(denom(x), denom(y))
    ovf |= ovfl

    !ovf && return FastRational{T, MayReduce}(num, den)

    y = cannonical(y)

    num_a, ovfl = mul_with_overflow(numer(x), denom(y))
    ovf |= ovfl
    num_b, ovfl = mul_with_overflow(denom(x), numer(y))
    ovf |= ovfl
    num, ovfl = add_with_overflow(num_a, num_b)
    ovf |= ovfl
    den, ovfl = mul_with_overflow(denom(x), denom(y))
    ovf |= ovfl

    ovf && throw(OverflowError())

    return FastRational{T, MayReduce}(num, den)
end

@inline Base.:(+)(x::FastRational{T, MayReduce}, y::FastRational{T, IsReduced})  where {T<:SignedInt} = y+x

function Base.:(-)(x::FastRational{T, R}, y::FastRational{T, R}) where {T<:SignedInt, R<:Reduceable} 
    ovf = false
    num_a, ovfl = mul_with_overflow(numer(x), denom(y))
    ovf |= ovfl
    num_b, ovfl = mul_with_overflow(denom(x), numer(y))
    ovf |= ovfl
    num, ovfl = sub_with_overflow(num_a, num_b)
    ovf |= ovfl
    den, ovfl = mul_with_overflow(denom(x), denom(y))
    ovf |= ovfl

    !ovf && return FastRational{T, MayReduce}(num, den)

    x = isreduced(x) ? x : cannonical(x)
    y = isreduced(y) ? y : cannonical(y)

    num_a, ovfl = mul_with_overflow(numer(x), denom(y))
    ovf |= ovfl
    num_b, ovfl = mul_with_overflow(denom(x), numer(y))
    ovf |= ovfl
    num, ovfl = sub_with_overflow(num_a, num_b)
    ovf |= ovfl
    den, ovfl = mul_with_overflow(denom(x), denom(y))
    ovf |= ovfl

    ovf && throw(OverflowError())

    return FastRational{T, MayReduce}(num, den)
end


function Base.:(*)(x::FastRational{T, R}, y::FastRational{T, R}) where {T<:SignedInt, R<:Reduceable} 
    ovf = false
    num, ovfl = mul_with_overflow(numer(x), numer(y))
    ovf |= ovfl
    den, ovfl = mul_with_overflow(denom(x), denom(y))
    ovf |= ovfl

    if ovf
       x = isreduced(x) ? x : cannonical(x)
       y = isreduced(y) ? y : cannonical(y)

       ovf = false
       num, ovfl = mul_with_overflow(numer(x), numer(y))
       ovf |= ovfl
       den, ovfl = mul_with_overflow(denom(x), denom(y))
       ovf |= ovfl

       ovf && throw(OverflowError())
    end

    return FastRational{T, MayReduce}(num, den)
end


function Base.:(//)(x::FastRational{T, R}, y::FastRational{T, R}) where {T<:SignedInt, R<:Reduceable} 
    ovf = false
    num, ovfl = mul_with_overflow(numer(x), denom(y))
    ovf |= ovfl
    den, ovfl = mul_with_overflow(denom(x), numer(y))
    ovf |= ovfl

    if ovf
       #x = ifelse(isreduced(x), x, cannonical(x))
       #y = ifelse(isreduced(y), y, cannonical(y))
       x = isreduced(x) ? x : cannonical(x)
       y = isreduced(y) ? y : cannonical(y)

       ovf = false
       num, ovfl = mul_with_overflow(numer(x), denom(y))
       ovf |= ovfl
       den, ovfl = mul_with_overflow(denom(x), numer(y))
       ovf |= ovfl

       ovf && throw(OverflowError())
    end

    return FastRational{T, MayReduce}(num, den)
end

Base.:(/)(x::FastRational{T, R}, y::FastRational{T, R}) where {T<:SignedInt, R<:Reduceable} = x // y


function show(io::IO, x::FastRational{T, R}) where {T<:SignedInt, R<:Reduceable}
    z = isreduced(x) ? x : cannonical(x)
    print(io, numer(z), "//", denom(z))
end

function read(s::IO, ::Type{FastRational{T, R}}) where {T<:SignedInt, R<:Reduceable}
    r = read(s,T)
    i = read(s,T)
    return cannonical(r,i)
end

function write(s::IO, x::FastRational{T, R}) where {T<:SignedInt, R<:Reduceable}
    z = isreduced(x) ? x : cannonical(x)
    return write(s, numer(z), denom(z))
end

promote_rule(::Type{FastRational{T, R}}, ::Type{Rational{T}}) where {T<:SignedInt, R<:Reduceable} =
    FastRational{T, R}

Base.promote_type(::Type{FastRational{T, R}}, ::Type{Rational{S}}) where {T<:SignedInt, R<:Reduceable, S<:SignedInt} =
    sizeof(T) >= sizeof(S) ? FastRational{T, R} : FastRational{S, R}

convert(::Type{FastRational{T, R}}, x::Rational{T}) where {T<:SignedInt, R<:Reduceable} =
    FastRational(R, numerator(x), denominator(x))

convert(::Type{Rational{T}}, x::FastRational{T, R}) where {T<:SignedInt, R<:Reduceable} =
    Rational(numer(x), denom(x))

convert(::Type{Rational{S}}, x::FastRational{T, R}) where {T<:SignedInt, R<:Reduceable, S<:SignedInt} =
    Rational(S(numer(x)), S(denominator(x)))

FastRational(x::Rational{T}) where {T<:SignedInt, R<:Reduceable} =
    convert(FastRational{T, R}, x)

Rational(x::FastRational{T, R}) where {T<:SignedInt, R<:Reduceable} =
    convert(Rational{T}, x)

Base.:(==)(x::Rational{T}, y::FastRational{T, IsReduced}) where {T<:SignedInt} =
   numerator(x) == numerator(y) && denominator(x) == denominator(y)
Base.:(!=)(x::Rational{T}, y::FastRational{T, IsReduced}) where {T<:SignedInt} =
   !(x == y)
Base.:(==)(x::FastRational{T, IsReduced}, y::Rational{T}) where {T<:SignedInt} =
   numerator(x) == numerator(y) && denominator(x) == denominator(y)
Base.:(!=)(x::FastRational{T, IsReduced}, y::Rational{T}) where {T<:SignedInt} =
   !(x == y)

Base.:(<)(x::Rational{T}, y::FastRational{T, IsReduced}) where {T<:SignedInt} =
    x < Rational{T}(y)
Base.:(<=)(x::Rational{T}, y::FastRational{T, IsReduced}) where {T<:SignedInt} =
    x <= Rational{T}(y)
Base.:(<)(x::FastRational{T, IsReduced}, y::Rational{T}) where {T<:SignedInt} =
    Rational{T}(x) < y
Base.:(<=)(x::FastRational{T, IsReduced}, y::Rational{T}) where {T<:SignedInt} =
    Rational{T}(x) <= y

Base.:(<)(x::Rational{T}, y::FastRational{T, MayReduce}) where {T<:SignedInt} =
    x < cannonical(y)   
Base.:(<=)(x::Rational{T}, y::FastRational{T, MayReduce}) where {T<:SignedInt} =
   x <= cannonical(y)
Base.:(<)(x::FastRational{T, MayReduce}, y::Rational{T}) where {T<:SignedInt} =
   cannonical(x) < y
Base.:(<=)(x::FastRational{T, MayReduce}, y::Rational{T}) where {T<:SignedInt} =
   cannonical(x) <= y


end # module
