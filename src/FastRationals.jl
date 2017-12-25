module FastRationals

export FastRational


import Base: convert, promote_rule, eltype,
    show, read, write,
    checked_add, checked_sub, checked_mul, power_by_squaring,
    numerator, denominator, widen, rationalize, 
    isinteger, iszero, isone,
    sign, signbit, copysign, flipsign, typemin, typemax,
    ==, !=, <=, <, >=, >, cmp, -, +, *, inv, /, //, rem, mod, fma, div, fld, cld,
    trunc, floor, ceil, round, ^

import Base.Checked: add_with_overflow, sub_with_overflow, mul_with_overflow

const SignedInt  = Union{Int64, Int32, Int16, Int128, BigInt, Int8}

const IsReduced  = Val{:IsReduced}
const MayReduce  = Val{:MayReduce}
const Reduceable = Union{IsReduced, MayReduce}

abstract type AbstractRational{T} <: Real end
abstract type GenericRational{T}  <: AbstractRational{T} end
abstract type ReducedRational{T}  <: GenericRational{T}  end

struct PlainRational{T} <: GenericRational{T}
    num::T
    den::T
end

@inline numerator(x::PlainRational{T}) where T = x.num
@inline denominator(x::PlainRational{T}) where T = x.den
@inline value(x::PlainRational{T}) where T = (x.num, x.den)
eltype(x::PlainRational{T}) where T = T

struct FastRational{T} <: ReducedRational{T}
    num::T
    den::T
end

@inline numerator(x::FastRational{T}) where T = x.num
@inline denominator(x::FastRational{T}) where T = x.den
@inline value(x::FastRational{T}) where T = (x.num, x.den)
eltype(x::FastRational{T}) where T = T

# FastRationals are created with denom == abs(denom)
function canonical(num::T, den::T) where {T<:SignedInt}
    num = flipsign(num, den)
    den = abs(den)
    no_trailingzeros = num >> trailing_zeros(num)
    if den >> trailing_zeros(den) !== no_trailingzeros
        gcdenom = gcd(num, den)
        num = div(num, gcdenom)
        den = div(den, gcdenom)
    else
        num = no_trailingzeros
        den = one(T)
    end
    return num, den
end

function canonical(num::T, den::T) where {T}
    gcdenom = gcd(num, den)
    if gcdenom !== one(T)
        num = div(num, gcdenom)
        den = div(den, gcdenom)
    end
    return num, den
end

@inline canonical(x::PlainRational{T}) where {T} =
    FastRational(canonical(numerator(x), denominator(x))...,)

@inline function convert(::Type{FastRational{T}}, x::PlainRational{T}) where T<:Union{Int128, Int64, Int32, Int16, Int8}
    return canonical(x)
end
        
function convert(::Type{PlainRational{T}}, x::FastRational{T}) where T
    throw(ErrorException("disallowed: convert(PlainRational, x::FastRational)"))
end
# !!! Target != typeof(convert(::Type{Target}, x::Source)) !!!
convert(::Type{PlainRational{T}}, x::T) where {T<:Signed} =
    FastRational(x, one(T))
        
convert(::Type{Rational{T}}, x::R) where {T<:Signed, R<:Union{FastRational{T}, PlainRational{T}}} =
    Rational(numerator(x), denominator(x))
convert(::Type{T}, x::FastRational{T}) where {T} =
    denominator(x) === one(T) ? numerator(x) : throw(InexactError())
convert(::Type{T}, x::PlainRational{T}) where {T} =
    convert(T, convert(FastRational{T}, x))

promote_rule(::Type{R}, ::Type{T}) where {T, R<:Union{FastRational{T}, PlainRational{T}}} =
    R
promote_rule(::Type{R}, x::Rational{T}) where {T<:Signed, R<:Union{FastRational{T}, PlainRational{T}}} =
    R
promote_rule(::Type{FastRational{T}}, ::Type{PlainRational{T}}) where T<:Signed =
    FastRational{T}

"""
      FastRationals are always in reduced terms
"""
const FastRationalNT  = NamedTuple{(:num, :den)}

@inline numerator(x::FastRationalNT) where T = x.num
@inline denominator(x::FastRationalNT) where T = x.den
@inline value(x::FastRationalNT) = (x.num, x.den)
eltype(x::FastRationalNT) where T = T

const PlainRationalNT = NamedTuple{(:num, :den, :void)}
@inline numerator(x::PlainRationalNT) where T = x.num
@inline denominator(x::PlainRationalNT) where T = x.den
@inline value(x::PlainRationalNT) = (x.num, x.den)
eltype(x::PlainRationalNT) where T = T


@inline NT_PlainRational(num::T, den::T) where T = PlainRationalNT((num, den, nothing))
@inline NT_FastRational(num::T, den::T) where T = FastRationalNT((num, den))
@inline NT_PlainRational(numden::Tuple{T,T}) where T = PlainRationalNT(numden.num, numden.den, nothing)
@inline NT_FastRational(numden::Tuple{T,T}) where T = FastRationalNT(numden)
@inline NT_FastRational(nt::PlainRationalNT) = NT_FastRational(canonical(nt.num, nt.den))

@inline Base.convert(::Type{PlainRationalNT}, x::PlainRational{T}) where T =
    NT_PlainRational(numerator(x), denominator(x))
@inline Base.convert(::Type{FastRationalNT}, x::FastRational{T}) where T =
    NT_FastRational(numerator(x), denominator(x))
@inline Base.convert(::Type{FastRationalNT}, x::PlainRational{T}) where T =
    NT_FastRational(canonical(numerator(x), denominator(x)))



function Base.:(+)(x::FastRationalNT, y::FastRationalNT) 
    ovf = false
    x_den, y_den = denominator(x), denominator(y)
    den, ovfl = mul_with_overflow(den_x, den_y)
    ovf |= ovfl
    num_a, ovfl = mul_with_overflow(numerator(x), y_den)
    ovf |= ovfl
    num_b, ovfl = mul_with_overflow(den_x, numerator(y))
    ovf |= ovfl
    num, ovfl = add_with_overflow(num_a, num_b)
    ovf |= ovfl

    ovf && throw(OverflowError())

    return PlainRationalNT(num, den)
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

    x = canonical(x)
    y = canonical(y)

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

    x = isreduced(x) ? x : canonical(x)
    y = isreduced(y) ? y : canonical(y)

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

    y = canonical(y)

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
                
                
                

@inline function convert(::Type{FastRational{T}}, x::PlainRational{T}) where T<:Union{Int128, Int64, Int32, Int16, Int8}
    return canonical(x)
end
        
function convert(::Type{PlainRational{T]}, x::FastRational{T}) where T
    throw(ErrorException("disallowed: convert(PlainRational, x::FastRational)"))
end
# !!! Target != typeof(convert(::Type{Target}, x::Source)) !!!
convert(::Type{PlainRational{T}}, x::T) where {T<:Signed} =
    FastRational(x, one(T))
        
convert(::Type{Rational{T}, x::R) where {T<:Signed, R<:Union{FastRational{T}, PlainRational{T}}} =
    Rational(numerator(x), denominator(x))
convert(::Type{T}, x::FastRational{T}) where {T} =
    denominator(x) === one(T) ? numerator(x) : throw(InexactError())
convert(::Type{T}, x::PlainRational{T}) where {T} =
    convert(T, convert(FastRational{T}, x))

promote_rule(::Type{R}, ::Type{T}) where {T, R<:Union{FastRational{T}, PlainRational{T}}} =
    R
promote_rule(::Type{R}, x::Rational{T}}) where {T<:Signed, R<:Union{FastRational{T}, PlainRational{T}}} =
    R
promote_rule(::Type{FastRational{T}}, ::Type{PlainRational{T}}) where T<:Signed =
    FastRational{T}

const PlainRationalNT = NamedTuple{(:num, :den)}
const FastRationalNT  = NamedTuple{(:num, :den)}
@inline NT_PlainRational(num::T, den::T) where T = PlainRationalNT((num, den))
@inline NT_FastRational(num::T, den::T) where T = FastRationalNT((num, den))
@inline NT_PlainRational(numden::Tuple{T,T}) where T = PlainRationalNT(numden)
@inline NT_FastRational(numden::Tuple{T,T}) where T = FastRationalNT(numden)
@inline NT_FastRational(nt::PlainRationalNT) = NT_FastRational(canonical(nt.num, nt.den)))

@inline Base.convert(::Type{PlainRationalNT}, x::PlainRational{T}) where T =
    NT_PlainRational(numerator(x), denominator(x))
@inline Base.convert(::Type{FastRationalNT}, x::FastRational{T}) where T =
    NT_FastRational(numerator(x), denominator(x))
@inline Base.convert(::Type{FastRationalNT}, x::PlainRational{T}) where T =
    NT_FastRational(canonical(numerator(x), denominator(x)))


        
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

    x = canonical(x)
    y = canonical(y)

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

    x = isreduced(x) ? x : canonical(x)
    y = isreduced(y) ? y : canonical(y)

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

    y = canonical(y)

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

    x = isreduced(x) ? x : canonical(x)
    y = isreduced(y) ? y : canonical(y)

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
       x = isreduced(x) ? x : canonical(x)
       y = isreduced(y) ? y : canonical(y)

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
       #x = ifelse(isreduced(x), x, canonical(x))
       #y = ifelse(isreduced(y), y, canonical(y))
       x = isreduced(x) ? x : canonical(x)
       y = isreduced(y) ? y : canonical(y)

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
    z = isreduced(x) ? x : canonical(x)
    print(io, numer(z), "//", denom(z))
end

function read(s::IO, ::Type{FastRational{T, R}}) where {T<:SignedInt, R<:Reduceable}
    r = read(s,T)
    i = read(s,T)
    return canonical(r,i)
end

function write(s::IO, x::FastRational{T, R}) where {T<:SignedInt, R<:Reduceable}
    z = isreduced(x) ? x : canonical(x)
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
    Rational(S(numer(x)), S(denom(x)))

FastRational(x::Rational{T}) where {T<:SignedInt} =
    convert(FastRational{T, IsReduced}, x)

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

Base.:(==)(x::Rational{T}, y::FastRational{T, MayReduce}) where {T<:SignedInt} =
   x == canonical(y)
Base.:(!=)(x::Rational{T}, y::FastRational{T, MayReduce}) where {T<:SignedInt} =
   x != canonical(y)
Base.:(==)(x::FastRational{T, MayReduce}, y::Rational{T}) where {T<:SignedInt} =
   canonial(x) == y
Base.:(!=)(x::FastRational{T, MayReduce}, y::Rational{T}) where {T<:SignedInt} =
   canonical(x) != y

Base.:(<)(x::Rational{T}, y::FastRational{T, IsReduced}) where {T<:SignedInt} =
    x < Rational{T}(y)
Base.:(<=)(x::Rational{T}, y::FastRational{T, IsReduced}) where {T<:SignedInt} =
    x <= Rational{T}(y)
Base.:(<)(x::FastRational{T, IsReduced}, y::Rational{T}) where {T<:SignedInt} =
    Rational{T}(x) < y
Base.:(<=)(x::FastRational{T, IsReduced}, y::Rational{T}) where {T<:SignedInt} =
    Rational{T}(x) <= y

Base.:(==)(x::FastRational{T, IsReduced}, y::FastRational{T, IsReduced}) where {T<:SignedInt} =
   numer(x) === numer(y) && denom(x) === denom(y)
Base.:(!=)(x::FastRational{T, IsReduced}, y::FastRational{T, IsReduced}) where {T<:SignedInt} =
   numer(x) !== numer(y) || denom(x) !== denom(y)

for F in (:(>), :(>=), :(<=), :(<))
    @eval $F(x::FastRational{T, IsReduced}, y::FastRational{T, IsReduced}) where {T<:SignedInt} =
   $F(numer(x)*denom(y), numer(y)*denom(x))
end


for F in (:(==), :(!=), :(>), :(>=), :(<=), :(<))
    @eval $F(x::FastRational{T, IsReduced}, y::FastRational{T, MayReduce}) where {T<:SignedInt} =
   $F(x, canonical(y))
end
for F in (:(==), :(!=), :(>), :(>=), :(<=), :(<))
    @eval $F(x::FastRational{T, MayReduce}, y::FastRational{T, IsReduced}) where {T<:SignedInt} =
   $F(canonical(x), y)
end
for F in (:(==), :(!=), :(>), :(>=), :(<=), :(<))
    @eval $F(x::FastRational{T, MayReduce}, y::FastRational{T, MayReduce}) where {T<:SignedInt} =
   $F(canonical(x), canonical(y))
end


Base.isequal(x::FastRational{T, R1}, y::FastRational{T, R2}) where {T<:SignedInt, R1<:Reduceable, R2<:Reduceable} =
   x == y
Base.isless(x::FastRational{T, R1}, y::FastRational{T, R2}) where {T<:SignedInt, R1<:Reduceable, R2<:Reduceable} =
   x < y

end # module
