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


const SysInt = Union{Int64, Int32, Int16, Int8}
const SignedInt = Union{SysInt, Int128, BigInt}

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

function canonical(num::T, den::T) where {T<:SysInt}
    gcdenom = gcd(num, den)
    if gcdenom !== one(T)
        num = div(num, gcdenom)
        den = div(den, gcdenom)
    end
    return num, den
end


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

@inline FastRational(num::T, den::T) where T = FastRational((num, den))
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

# add

function Base.:(+)(x::FastRational, y::FastRational) 
    numer, denom, ovf = add_with_overflow_for_rational(x, y)
    ovf && throw(OverflowError())
    
    return PlainRational(numer, denom)
end

function Base.:(+)(x::PlainRational, y::PlainRational) 
    numer, denom, ovf = add_with_overflow_for_rational(x, y)
    !ovf && return PlainRational(numer, denom)

    x = canonize(x)
    y = canonize(y)
    numer, denom, ovf = add_with_overflow_for_rational(x, y)
    ovf && throw(OverflowError())

    return PlainRational(numer, denom)
end

function Base.:(+)(x::FastRational, y::PlainRational) 
    numer, denom, ovf = add_with_overflow_for_rational(x, y)
    !ovf && return PlainRational(numer, denom)

    y = canonize(y)
    numer, denom, ovf = add_with_overflow_for_rational(x, y)
    ovf && throw(OverflowError())

    return PlainRational(numer, denom)
end

function Base.:(+)(x::PlainRational, y::FastRational) 
    numer, denom, ovf = add_with_overflow_for_rational(x, y)
    !ovf && return PlainRational(numer, denom)

    y = canonize(y)
    numer, denom, ovf = add_with_overflow_for_rational(x, y)
    ovf && throw(OverflowError())

    return PlainRational(numer, denom)
end

Base.:(+)(x::FastRational, y::Rational{T})  where T = (+)(promote(x, y)...)
Base.:(+)(x::Rational{T}, y::FastRational)  where T = (+)(promote(x, y)...)
Base.:(+)(x::PlainRational, y::Rational{T}) where T = (+)(promote(x, y)...)
Base.:(+)(x::Rational{T}, y::PlainRational) where T = (+)(promote(x, y)...)


# subtract

function Base.:(-)(x::FastRational, y::FastRational) 
    numer, denom, ovf = sub_with_overflow_for_rational(x, y)
    ovf && throw(OverflowError())
    
    return PlainRational(numer, denom)
end

function Base.:(-)(x::PlainRational, y::PlainRational) 
    numer, denom, ovf = sub_with_overflow_for_rational(x, y)
    !ovf && return PlainRational(numer, denom)

    x = canonize(x)
    y = canonize(y)
    numer, denom, ovf = sub_with_overflow_for_rational(x, y)
    ovf && throw(OverflowError())

    return PlainRational(numer, denom)
end

function Base.:(-)(x::FastRational, y::PlainRational) 
    numer, denom, ovf = sub_with_overflow_for_rational(x, y)
    !ovf && return PlainRational(numer, denom)

    y = canonize(y)
    numer, denom, ovf = sub_with_overflow_for_rational(x, y)
    ovf && throw(OverflowError())

    return PlainRational(numer, denom)
end

function Base.:(-)(x::PlainRational, y::FastRational) 
    numer, denom, ovf = sub_with_overflow_for_rational(x, y)
    !ovf && return PlainRational(numer, denom)

    y = canonize(y)
    numer, denom, ovf = sub_with_overflow_for_rational(x, y)
    ovf && throw(OverflowError())

    return PlainRational(numer, denom)
end

Base.:(-)(x::FastRational, y::Rational{T})  where T = (-)(promote(x, y)...)
Base.:(-)(x::Rational{T}, y::FastRational)  where T = (-)(promote(x, y)...)
Base.:(-)(x::PlainRational, y::Rational{T}) where T = (-)(promote(x, y)...)
Base.:(-)(x::Rational{T}, y::PlainRational) where T = (-)(promote(x, y)...)

# multiply

function Base.:(*)(x::FastRational, y::FastRational) 
    numer, denom, ovf = mul_with_overflow_for_rational(x, y)
    ovf && throw(OverflowError())
    
    return PlainRational(numer, denom)
end

function Base.:(*)(x::PlainRational, y::PlainRational) 
    numer, denom, ovf = mul_with_overflow_for_rational(x, y)
    !ovf && return PlainRational(numer, denom)

    x = canonize(x)
    y = canonize(y)
    numer, denom, ovf = mul_with_overflow_for_rational(x, y)
    ovf && throw(OverflowError())

    return PlainRational(numer, denom)
end

function Base.:(*)(x::FastRational, y::PlainRational) 
    numer, denom, ovf = mul_with_overflow_for_rational(x, y)
    !ovf && return PlainRational(numer, denom)

    y = canonize(y)
    numer, denom, ovf = mul_with_overflow_for_rational(x, y)
    ovf && throw(OverflowError())

    return PlainRational(numer, denom)
end

function Base.:(*)(x::PlainRational, y::FastRational) 
    numer, denom, ovf = mul_with_overflow_for_rational(x, y)
    !ovf && return PlainRational(numer, denom)

    y = canonize(y)
    numer, denom, ovf = mul_with_overflow_for_rational(x, y)
    ovf && throw(OverflowError())

    return PlainRational(numer, denom)
end

Base.:(*)(x::FastRational, y::Rational{T})  where T = (*)(promote(x, y)...)
Base.:(*)(x::Rational{T}, y::FastRational)  where T = (*)(promote(x, y)...)
Base.:(*)(x::PlainRational, y::Rational{T}) where T = (*)(promote(x, y)...)
Base.:(*)(x::Rational{T}, y::PlainRational) where T = (*)(promote(x, y)...)

# divide

function Base.:(//)(x::FastRational, y::FastRational) 
    numer, denom, ovf = div_with_overflow_for_rational(x, y)
    ovf && throw(OverflowError())
    
    return PlainRational(numer, denom)
end

function Base.:(//)(x::PlainRational, y::PlainRational) 
    numer, denom, ovf = div_with_overflow_for_rational(x, y)
    !ovf && return PlainRational(numer, denom)

    x = canonize(x)
    y = canonize(y)
    numer, denom, ovf = div_with_overflow_for_rational(x, y)
    ovf && throw(OverflowError())

    return PlainRational(numer, denom)
end

function Base.:(//)(x::FastRational, y::PlainRational) 
    numer, denom, ovf = div_with_overflow_for_rational(x, y)
    !ovf && return PlainRational(numer, denom)

    y = canonize(y)
    numer, denom, ovf = div_with_overflow_for_rational(x, y)
    ovf && throw(OverflowError())

    return PlainRational(numer, denom)
end

function Base.:(//)(x::PlainRational, y::FastRational) 
    numer, denom, ovf = div_with_overflow_for_rational(x, y)
    !ovf && return PlainRational(numer, denom)

    y = canonize(y)
    numer, denom, ovf = div_with_overflow_for_rational(x, y)
    ovf && throw(OverflowError())

    return PlainRational(numer, denom)
end

Base.:(//)(x::FastRational, y::Rational{T})  where T = (//)(promote(x, y)...)
Base.:(//)(x::Rational{T}, y::FastRational)  where T = (//)(promote(x, y)...)
Base.:(//)(x::PlainRational, y::Rational{T}) where T = (//)(promote(x, y)...)
Base.:(//)(x::Rational{T}, y::PlainRational) where T = (//)(promote(x, y)...)


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



@inline sign(x::FastRational)  = oftype(x, sign(numerator(x)))
@inline signbit(x::FastRational)  = signbit(numerator(x))
@inline copysign(x::FastRational{T,R}, y::Real) = FastRational(copysign(numerator(x), y), denominator(x))
@inline copysign(x::FastRational, y::FastRational)  = FastRational{T,R}(copysign(numerator(x), numerator(y)), denominator(x))
@inline flipsign(x::FastRational, y::Real)  = FastRational(flipsign(numerator(x), y), denominator(x))
@inline flipsign(x::FastRational, y::FastRational)  = FastRational(flipsign(numerator(x), numerator(y)), denominator(x))

@inline isinteger(x::FastRational) = abs(denominator(x)) === one(T)
@inline iszero(x::FastRational)  = abs(numerator(x)) === zero(T)

@inline Base.Math.abs(x::FastRational)   = FastRational(abs(numerator(x)), denominator(x))

@inline Base.Math.inv(x::FastRational)  = FastRational(denominator(x), numerator(x))

@inline function Base.:(-)(x::FastRational)  
    numerator(x) === typemin(T) && throw(OverflowError())
    return FastRational(-numerator(x), denominator(x))
end

Base.:(/)(x::FastRational, y::FastRational) = x // y


function show(io::IO, x::FastRational)
    print(io, numerator(z), "//", denominator(z))
end

function show(io::IO, x::PlainRational)
    num, den = canonical(x)
    print(io, num, "//", den)
end

function read(s::IO, ::Type{T}) where T<:FastRational
    num = read(s,T)
    den = read(s,T)
    return FastRational(num,den)
end

function write(s::IO, x::FastRational)
    return write(s, numerator(z), denominator(z))
end

function read(s::IO, ::Type{T}) where T<:PlainRational
    num = read(s,T)
    den = read(s,T)
    return FastRational(r,i)
end

function write(s::IO, x::PlainRational)
    num, den = canonical(x)
    return write(s, numerator(z), denominator(z))
end


Base.:(==)(x::Rational{T}, y::FastRational) where T =
   numerator(x) == numerator(y) && denominator(x) == denominator(y)
Base.:(!=)(x::Rational{T}, y::FastRational) where T = !(x == y)
Base.:(==)(x::FastRational, y::Rational{T}) where T =
   numerator(x) == numerator(y) && denominator(x) == denominator(y)
Base.:(!=)(x::FastRational, y::Rational{T}) where T = !(x == y)

Base.:(==)(x::Rational{T}, y::PlainRational) where T = (numerator(x), denominator(x)) == canonical(y)
Base.:(!=)(x::Rational{T}, y::PlainRational) where T = (numerator(x), denominator(x)) != canonical(y)
Base.:(==)(x::PlainRational, y::Rational{T}) where T = canonical(x) == (numerator(t), denominator(y))
Base.:(!=)(x::PlainRational, y::Rational{T}) where T = canonical(x) != (numerator(y), denominator(y))

Base.:(<)(x::Rational{T}, y::FastRational) where T = x < Rational{T}(y)
Base.:(<=)(x::Rational{T}, y::FastRational) where T = x <= Rational{T}(y)
Base.:(<)(x::FastRational, y::Rational{T}) where T = Rational{T}(x) < y
Base.:(<=)(x::FastRational, y::Rational{T}) where T = Rational{T}(x) <= y

Base.:(==)(x::FastRational, y::FastRational) =
   numerator(x) === numerator(y) && denominator(x) === denominator(y)
Base.:(!=)(x::FastRational, y::FastRational) =
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


Base.isequal(x::FastRational, y::FastRational) = x == y
Base.isless(x::FastRational, y::FastRational) = x <= y
Base.isequal(x::FastRational, y::PlainRational) = x == y
Base.isless(x::FastRational, y::PlainRational) = x <= y
Base.isequal(x::PlainRational, y::FastRational) = x == y
Base.isless(x::PlainRational, y::FastRational) = x <= y
Base.isequal(x::PlainRational, y::PlainRational) = x == y
Base.isless(x::PlainRational, y::PlainRational) = x <= y

end # module
