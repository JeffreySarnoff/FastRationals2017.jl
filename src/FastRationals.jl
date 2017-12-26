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
@inline canonize(x::PlainRational) = x(canonical(x))

@inline PlainRational(num::T, den::T) where T = PlainRational((num, den, nothing))
@inline PlainRational(numden::Tuple{T,T}) where T = PlainRational((numden.num, numden.den, nothing))


const FastRational = NamedTuple{(:num, :den)}

@inline numerator(x::FastRational) = x.num
@inline denominator(x::FastRational) = x.den
@inline value(x::FastRational) = (x.num, x.den)
eltype(x::FastRational) = typeof(x.num)

@inline canonical(x::FastRational) = values(x)

@inline FastRational(num::T, den::T) where T = FastRational((num, den))
@inline FastRational(q::Rational{T}) where T = FastRational((q.num, q.den))
@inline FastRational(q::PlainRational) = FastRational(canonical(q.num, q.den))


convert(::Type{FastRational}, q::PlainRational) = FastRational( canonical(q) )
promote_rule(::Type{FastRational}, ::Type{PlainRational}) = FastRational
convert(::Type{FastRational}, q::Rational{T}) where T<:Signed = FastRational(numerator(q), denominator(q))
convert(::Type{Rational{T}}, q::FastRational) where T<:Signed = Rational(numerator(q), denominator(q))
promote_rule(::Type{FastRational}, ::Type{Rational{T}}) where T<:Signed = FastRational

PlainRational(q::Rational{T}) where T = throw(ErrorException("PlainRational(Rational) is disallowed."))
PlainRational(q::FastRational) = throw(ErrorException("PlainRational(FastRational) is disallowed."))
convert(::Type{PlainRational}, x::FastRational) = throw(ErrorException("conversion from FastRational to PlainRational is disallowed."))


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
    
    return numer, denom, ovfl
end    

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
