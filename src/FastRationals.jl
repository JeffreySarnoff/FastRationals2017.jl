module FastRationals

export FastRational


import Base: convert, promote_rule, eltype,
    string, show, read, write,
    checked_add, checked_sub, checked_mul, power_by_squaring,
    numerator, denominator, widen, rationalize, 
    isinteger, iszero, isone,
    sign, signbit, copysign, flipsign, typemin, typemax, abs,
    ==, !=, <=, <, >=, >, isless, isequal, cmp,
    -, +, *, inv, /, //, rem, mod, fma, div, fld, cld,
    trunc, floor, ceil, round, ^

import Base.Checked: add_with_overflow, sub_with_overflow, mul_with_overflow


const SignedInt = Union{Int64, Int32, Int16, Int8, Int128, BigInt}

"""
    canonical(numerator::T, denominator::T) where T<:Signed
Rational numbers that are finite and normatively bounded by
the extremal magnitude of an underlying signed type have a
canonical representation.
- numerator and denominator have no common factors
- numerator may be negative, zero or positive
- denominator is strictly positive (d > 0)
""" canonical

function canonical(num::T, den::T) where {T<:SignedInt}
    num, den = canonical_signed(num, den)
    num, den = canonical_valued(num, den)
    return num, den
end

@inline function canonical_signed(num::T, den::T) where {T<:SignedInt}
    return flipsign(num, den), abs(den)
end

@inline function canonical_valued(num::T, den::T) where {T<:SignedInt}
    gcdval = gcd(num, den)
    gcdval === one(T) && return num, den
    num = div(num, gcdval)
    den = div(den, gcdval)
    return num, den
end


abstract type AbstractRational{Q}  <: Real end  # Q is underlying type (Int64 ?Poly)
abstract type SignedRational{Q}    <: AbstractRational{Q} end  # may be reduceable  
abstract type CanonicalRational{Q} <: SignedRational{Q}   end  # already reduced

@inline numerator(q::T)   where {Q, T<:AbstractRational{Q}} = q.num
@inline denominator(q::T) where {Q, T<:AbstractRational{Q}} = q.den
@inline value(q::T) where {Q, T<:AbstractRational{Q}} =
    numerator(a), denominator(q)
@inline value(q::T) where {Q, T<:Rational{Q}} =
    numerator(a), denominator(q)


mutable struct SignedRatio{Q} <: SignedRational{Q}
    num::Q    # numerator
    den::Q    # denominator > 0
    can::Bool # in canonical form?
end

struct RationalNum{Q} <: CanonicalRational{Q}
    num::Q
    den::Q
end

# tuples pass the given values to the constructor
@inline SignedRatio(numden::Tuple{I,I}) where I<:SignedInt =
    SignedRatio(numden[1], numden[2], false)
SignedRatio(numden::Tuple{I,I,Bool}) where {I<:SignedInt} =
    SignedRatio(numden...,)
SignedRatio(numden::Tuple{I,I}, can::Bool) where {I<:SignedInt} =
    SignedRatio(numden[1], numden[2], can)

# explicitly type qualified dispatch *may* modify given values
@inline SignedRatio(::Type{I}, num::I, den::I) where I<:SignedInt =
    SignedRatio(num, den)

# applicative constructors work properly
@inline SignedRatio(q::RationalNum{I}) where I<:SignedInt =
    SignedRatio(value(q))

# applicative constructors work properly
@inline SignedRatio(q::Rational{I}) where I<:SignedInt =
    SignedRatio(value(q))

# tuples pass the given values to the constructor
@inline RationalNum(numden::Tuple{I,I}) where I<:SignedInt =
    RationalNum(numden[1], numden[2])

# explicitly type qualified dispatch *may* modify given values
@inline RationalNum(::Type{I}, num::I, den::I) where I<:SignedInt =
    RationalNum(canonical(num, den))

# applicative constructors work properly
@inline RationalNum(q::SignedRatio{I}) where I<:SignedInt =
    q.can ? RationalNum(numerator(q), denominator(q)) :
            RationalNum(canonical(numerator(q), denominator(q)))

# applicative constructors work properly
@inline RationalNum(q::Rational{I}) where I<:SignedInt =
    RationalNum(value(q))

# Rational as an applicative constructor

@inlinevRational(q::SignedRatio{I}) where I<:SignedInt =
    Rational(RationalNum(q))

@inline Rational(q::RationalNum{I}) where I<:SignedInt =
    Rational(numerator(q), denominator(q))



const PlainRational = NamedTuple{(:num, :den, :void)}

@inline numerator(x::PlainRational) = x.num
@inline denominator(x::PlainRational) = x.den
@inline value(x::PlainRational) = (x.num, x.den)
eltype(x::PlainRational) = typeof(x.num)

@inline canonical(x::PlainRational) = canonical(numerator(x), denominator(x))

@inline PlainRational(num::T, den::T) where T = PlainRational((num, den, nothing))
@inline PlainRational(numden::Tuple{T,T}) where T = PlainRational((numden..., nothing))


const FastRational = NamedTuple{(:num, :den)}

@inline numerator(x::FastRational) = x.num
@inline denominator(x::FastRational) = x.den
@inline value(x::FastRational) = (x.num, x.den)
eltype(x::FastRational) = typeof(x.num)

@inline canonical(x::FastRational) = values(x)

@inline FastRational(num::T, den::T) where T = FastRational(canonical(num, den))
@inline FastRational(q::Rational{T}) where T = FastRational((q.num, q.den))
@inline FastRational(q::PlainRational) = FastRational(canonical(q.num, q.den))

@inline canonize(q::PlainRational) = FastRational(canonical(q))
@inline canonize(q::FastRational) = q

convert(::Type{FastRational}, q::PlainRational) = FastRational( canonical(q) )
promote_rule(::Type{FastRational}, ::Type{PlainRational}) = FastRational
convert(::Type{FastRational}, q::Rational{T}) where T<:Signed = FastRational(numerator(q), denominator(q))
convert(::Type{Rational{T}}, q::FastRational) where T<:Signed = Rational(numerator(q), denominator(q))
promote_rule(::Type{FastRational}, ::Type{Rational{T}}) where T<:Signed = FastRational

PlainRational(q::Rational{T}) where T = throw(ErrorException("PlainRational(Rational) is disallowed."))
PlainRational(q::FastRational) = throw(ErrorException("PlainRational(FastRational) is disallowed."))
convert(::Type{PlainRational}, x::FastRational) = throw(ErrorException("conversion from FastRational to PlainRational is disallowed."))



@inline sign(x::FastRational)  = oftype(x, sign(numerator(x)))
@inline signbit(x::FastRational)  = signbit(numerator(x))
@inline copysign(x::FastRational, y::Real) = FastRational(copysign(numerator(x), y), denominator(x))
@inline copysign(x::FastRational, y::FastRational)  = FastRational(copysign(numerator(x), numerator(y)), denominator(x))
@inline flipsign(x::FastRational, y::Real)  = FastRational(flipsign(numerator(x), y), denominator(x))
@inline flipsign(x::FastRational, y::FastRational)  = FastRational(flipsign(numerator(x), numerator(y)), denominator(x))

@inline isinteger(x::FastRational) = abs(denominator(x)) === one(T)
@inline iszero(x::FastRational)  = abs(numerator(x)) === zero(T)

@inline abs(x::FastRational)   = FastRational((abs(numerator(x)), denominator(x)))

@inline inv(x::FastRational)  = FastRational((denominator(x), numerator(x)))

@inline function (-)(x::FastRational)  
    numerator(x) === typemin(T) && throw(OverflowError())
    return FastRational((-numerator(x), denominator(x)))
end

(/)(x::FastRational, y::FastRational) = x // y


# add

function (+)(x::FastRational, y::FastRational) 
    numer, denom, ovf = add_with_overflow_for_rational(x, y)
    ovf && throw(OverflowError("$x + $y overflowed"))
    
    return PlainRational(numer, denom)
end

function (+)(x::PlainRational, y::PlainRational) 
    numer, denom, ovf = add_with_overflow_for_rational(x, y)
    !ovf && return PlainRational(numer, denom)

    x = canonize(x)
    y = canonize(y)
    numer, denom, ovf = add_with_overflow_for_rational(x, y)
    ovf && throw(OverflowError("$x + $y overflowed"))

    return PlainRational(numer, denom)
end

function (+)(x::FastRational, y::PlainRational) 
    numer, denom, ovf = add_with_overflow_for_rational(x, y)
    !ovf && return PlainRational(numer, denom)

    y = canonize(y)
    numer, denom, ovf = add_with_overflow_for_rational(x, y)
    ovf && throw(OverflowError("$x + $y overflowed"))

    return PlainRational(numer, denom)
end

function (+)(x::PlainRational, y::FastRational) 
    numer, denom, ovf = add_with_overflow_for_rational(x, y)
    !ovf && return PlainRational(numer, denom)

    y = canonize(y)
    numer, denom, ovf = add_with_overflow_for_rational(x, y)
    ovf && throw(OverflowError("$x + $y overflowed"))

    return PlainRational(numer, denom)
end

(+)(x::FastRational, y::Rational{T})  where T = (+)(promote(x, y)...)
(+)(x::Rational{T}, y::FastRational)  where T = (+)(promote(x, y)...)
(+)(x::PlainRational, y::Rational{T}) where T = (+)(promote(x, y)...)
(+)(x::Rational{T}, y::PlainRational) where T = (+)(promote(x, y)...)


# subtract

function (-)(x::FastRational, y::FastRational) 
    numer, denom, ovf = sub_with_overflow_for_rational(x, y)
    ovf && throw(OverflowError("$x - $y overflowed"))
    
    return PlainRational(numer, denom)
end

function (-)(x::PlainRational, y::PlainRational) 
    numer, denom, ovf = sub_with_overflow_for_rational(x, y)
    !ovf && return PlainRational(numer, denom)

    x = canonize(x)
    y = canonize(y)
    numer, denom, ovf = sub_with_overflow_for_rational(x, y)
    ovf && throw(OverflowError("$x - $y overflowed"))

    return PlainRational(numer, denom)
end

function (-)(x::FastRational, y::PlainRational) 
    numer, denom, ovf = sub_with_overflow_for_rational(x, y)
    !ovf && return PlainRational(numer, denom)

    y = canonize(y)
    numer, denom, ovf = sub_with_overflow_for_rational(x, y)
    ovf && throw(OverflowError("$x - $y overflowed"))

    return PlainRational(numer, denom)
end

function (-)(x::PlainRational, y::FastRational) 
    numer, denom, ovf = sub_with_overflow_for_rational(x, y)
    !ovf && return PlainRational(numer, denom)

    y = canonize(y)
    numer, denom, ovf = sub_with_overflow_for_rational(x, y)
    ovf && throw(OverflowError("$x - $y overflowed"))

    return PlainRational(numer, denom)
end

(-)(x::FastRational, y::Rational{T})  where T = (-)(promote(x, y)...)
(-)(x::Rational{T}, y::FastRational)  where T = (-)(promote(x, y)...)
(-)(x::PlainRational, y::Rational{T}) where T = (-)(promote(x, y)...)
(-)(x::Rational{T}, y::PlainRational) where T = (-)(promote(x, y)...)

# multiply

function (*)(x::FastRational, y::FastRational) 
    numer, denom, ovf = mul_with_overflow_for_rational(x, y)
    ovf && throw(OverflowError("$x * $y overflowed"))
    
    return PlainRational(numer, denom)
end

function (*)(x::PlainRational, y::PlainRational) 
    numer, denom, ovf = mul_with_overflow_for_rational(x, y)
    !ovf && return PlainRational(numer, denom)

    x = canonize(x)
    y = canonize(y)
    numer, denom, ovf = mul_with_overflow_for_rational(x, y)
    ovf && throw(OverflowError("$x * $y overflowed"))

    return PlainRational(numer, denom)
end

function (*)(x::FastRational, y::PlainRational) 
    numer, denom, ovf = mul_with_overflow_for_rational(x, y)
    !ovf && return PlainRational(numer, denom)

    y = canonize(y)
    numer, denom, ovf = mul_with_overflow_for_rational(x, y)
    ovf && throw(OverflowError("$x * $y overflowed"))

    return PlainRational(numer, denom)
end

function (*)(x::PlainRational, y::FastRational) 
    numer, denom, ovf = mul_with_overflow_for_rational(x, y)
    !ovf && return PlainRational(numer, denom)

    y = canonize(y)
    numer, denom, ovf = mul_with_overflow_for_rational(x, y)
    ovf && throw(OverflowError("$x * $y overflowed"))

    return PlainRational(numer, denom)
end

(*)(x::FastRational, y::Rational{T})  where T = (*)(promote(x, y)...)
(*)(x::Rational{T}, y::FastRational)  where T = (*)(promote(x, y)...)
(*)(x::PlainRational, y::Rational{T}) where T = (*)(promote(x, y)...)
(*)(x::Rational{T}, y::PlainRational) where T = (*)(promote(x, y)...)

# divide

function (//)(x::FastRational, y::FastRational) 
    numer, denom, ovf = div_with_overflow_for_rational(x, y)
    ovf && throw(OverflowError("$x // $y overflowed"))
    
    return PlainRational(numer, denom)
end

function (//)(x::PlainRational, y::PlainRational) 
    numer, denom, ovf = div_with_overflow_for_rational(x, y)
    !ovf && return PlainRational(numer, denom)

    x = canonize(x)
    y = canonize(y)
    numer, denom, ovf = div_with_overflow_for_rational(x, y)
    ovf && throw(OverflowError("$x // $y overflowed"))

    return PlainRational(numer, denom)
end

function (//)(x::FastRational, y::PlainRational) 
    numer, denom, ovf = div_with_overflow_for_rational(x, y)
    !ovf && return PlainRational(numer, denom)

    y = canonize(y)
    numer, denom, ovf = div_with_overflow_for_rational(x, y)
    ovf && throw(OverflowError("$x // $y overflowed"))

    return PlainRational(numer, denom)
end

function (//)(x::PlainRational, y::FastRational) 
    numer, denom, ovf = div_with_overflow_for_rational(x, y)
    !ovf && return PlainRational(numer, denom)

    y = canonize(y)
    numer, denom, ovf = div_with_overflow_for_rational(x, y)
    ovf && throw(OverflowError("$x // $y overflowed"))

    return PlainRational(numer, denom)
end

(//)(x::FastRational, y::Rational{T})  where T = (//)(promote(x, y)...)
(//)(x::Rational{T}, y::FastRational)  where T = (//)(promote(x, y)...)
(//)(x::PlainRational, y::Rational{T}) where T = (//)(promote(x, y)...)
(//)(x::Rational{T}, y::PlainRational) where T = (//)(promote(x, y)...)


# core parts of add, sub

@inline function add_with_overflow_for_rational(x, y)
    ovf = false
    numer, ovfl = mul_with_overflow(numerator(x), denominator(y)) # here, numer is a temp
    ovf |= ovfl
    denom, ovfl = mul_with_overflow(denominator(x), numerator(y)) # here, denom is a temp
    ovf |= ovfl
    numer, ovfl = add_with_overflow(numer, denom) # numerator of sum
    ovf |= ovfl
    denom, ovfl = mul_with_overflow(denominator(x), denominator(y)) # denominator of sum
    ovf |= ovfl

    return numer, denom, ovf
end

@inline function sub_with_overflow_for_rational(x, y)
    ovf = false
    numer, ovfl = mul_with_overflow(numerator(x), denominator(y)) # here, numer is a temp
    ovf |= ovfl
    denom, ovfl = mul_with_overflow(denominator(x), numerator(y)) # here, denom is a temp
    ovf |= ovfl
    numer, ovfl = sub_with_overflow(numer, denom) # numerator of difference
    ovf |= ovfl
    denom, ovfl = mul_with_overflow(denominator(x), denominator(y)) # denominator of difference
    ovf |= ovfl

    return numer, denom, ovf
end

@inline function mul_with_overflow_for_rational(x, y)
    ovf = false
    numer, ovfl = mul_with_overflow(numerator(x), numerator(y))
    ovf |= ovfl
    denom, ovfl = mul_with_overflow(denominator(x), denominator(y))
    ovf |= ovfl

    return numer, denom, ovf
end

@inline function div_with_overflow_for_rational(x, y)
    ovf = false
    numer, ovfl = mul_with_overflow(numerator(x), denominator(y))
    ovf |= ovfl
    denom, ovfl = mul_with_overflow(denominator(x), numerator(y))
    ovf |= ovfl

    return numer, denom, ovf
end

(==)(x::Rational{T}, y::FastRational) where T =
   numerator(x) == numerator(y) && denominator(x) == denominator(y)
(!=)(x::Rational{T}, y::FastRational) where T = !(x == y)
(==)(x::FastRational, y::Rational{T}) where T =
   numerator(x) == numerator(y) && denominator(x) == denominator(y)
(!=)(x::FastRational, y::Rational{T}) where T = !(x == y)

(==)(x::Rational{T}, y::PlainRational) where T = (numerator(x), denominator(x)) == canonical(y)
(!=)(x::Rational{T}, y::PlainRational) where T = (numerator(x), denominator(x)) != canonical(y)
(==)(x::PlainRational, y::Rational{T}) where T = canonical(x) == (numerator(t), denominator(y))
(!=)(x::PlainRational, y::Rational{T}) where T = canonical(x) != (numerator(y), denominator(y))

(<)(x::Rational{T}, y::FastRational) where T = x < Rational{T}(y)
(<=)(x::Rational{T}, y::FastRational) where T = x <= Rational{T}(y)
(<)(x::FastRational, y::Rational{T}) where T = Rational{T}(x) < y
(<=)(x::FastRational, y::Rational{T}) where T = Rational{T}(x) <= y

(==)(x::FastRational, y::FastRational) =
   numerator(x) === numerator(y) && denominator(x) === denominator(y)
(!=)(x::FastRational, y::FastRational) =
   numerator(x) !== numerator(y) || denominator(x) !== denominator(y)

for F in (:(>), :(>=), :(<=), :(<))
    @eval $F(x::FastRational, y::FastRational) =
   $F(numerator(x)*denominator(y), numerator(y)*denominator(x))
end


for F in (:(==), :(!=), :(>), :(>=), :(<=), :(<))
    @eval $F(x::FastRational, y::PlainRational) = $F(x, canonical(y))
end
for F in (:(==), :(!=), :(>), :(>=), :(<=), :(<))
    @eval $F(x::PlainRational, y::FastRational) = $F(canonical(x), y)
end
for F in (:(==), :(!=), :(>), :(>=), :(<=), :(<))
    @eval $F(x::PlainRational, y::PlainRational) = $F(canonical(x), canonical(y))
end


isequal(x::FastRational, y::FastRational) = x == y
isless(x::FastRational, y::FastRational) = x <= y
isequal(x::FastRational, y::PlainRational) = x == y
isless(x::FastRational, y::PlainRational) = x <= y
isequal(x::PlainRational, y::FastRational) = x == y
isless(x::PlainRational, y::FastRational) = x <= y
isequal(x::PlainRational, y::PlainRational) = x == y
isless(x::PlainRational, y::PlainRational) = x <= y




string(x::FastRational) = string(numerator(x), "//", denominator(x))
@inline string(x::PlainRational) = string(FastRational(x))

function show(io::IO, x::FastRational)
    print(io, string(x))
end
@inline show(io::IO, x::PlainRational) = show(io, FastRational(x))
show(x::FastRational) = show(Base.STDOUT, "text/plain", string(x))
@inline show(x::PlainRational) = show(FastRational(x))

function string(x::Vector{Q}) where Q<:FastRational
    str = string((x...,))
    str = string("FastRational[", str[2:end-1], "]")
    return str
end
string(x::Vector{Q}) where Q<:PlainRational = string(map(FastRational, x))

function show(io::IO, x::Vector{Q}) where Q<:Union{FastRational, PlainRational}
    print(io, string(x))
end
function show(x::Vector{Q}) where Q<:Union{FastRational, PlainRational}
    show(Base.STDOUT, "text/plain", string(x))
end

function read(io::IO, ::Type{T}) where T<:FastRational
    num = read(io,T)
    den = read(io,T)
    return FastRational(num, den)
end
@inline read(io::IO, x::PlainRational) = read(io, FastRational(x))

function write(io::IO, x::FastRational)
    return write(io, numerator(z), denominator(z))
end
@inline write(io::IO, x::PlainRational) = write(io, FastRational(x))


end # module
