using FastRationals
if VERSION >= v"0.7.0-"
    using Test
else
    using Base.Test
end

using BenchmarkTools

macro fastest_time(this)
   :((@benchmark $this).times[1])
end

# using Int32s

numer_a, denom_a = Int32(5), Int32(77)
numer_b, denom_b = Int32(100), Int32(17)
a = Rational(numer_a, denom_a); b = Rational(numer_b, denom_b);
afast = FastRational(numer_a, denom_a); bfast = FastRational(numer_b, denom_b);

@test a + b == afast + bfast
@test a - b == afast - bfast
@test a * b == afast * bfast
@test a // b == afast // bfast

@test fld( (@fastest_time $a + $b), (@fastest_time $afast + $bfast) ) >= 1
@test fld( (@fastest_time $a * $b), (@fastest_time $afast * $bfast) ) >= 1


# using Int64s

numer_a, denom_a = Int64(5), Int64(77)
numer_b, denom_b = Int64(100), Int64(17)
a = Rational(numer_a, denom_a); b = Rational(numer_b, denom_b);
afast = FastRational(numer_a, denom_a); bfast = FastRational(numer_b, denom_b);

@test a + b == afast + bfast
@test a - b == afast - bfast
@test a * b == afast * bfast
@test a // b == afast // bfast

@test fld( (@fastest_time $a + $b), (@fastest_time $afast + $bfast) ) >= 1
@test fld( (@fastest_time $a * $b), (@fastest_time $afast * $bfast) ) >= 1

# using Int128s

numer_a, denom_a = Int128(5), Int128(77)
numer_b, denom_b = Int128(100), Int128(17)
a = Rational(numer_a, denom_a); b = Rational(numer_b, denom_b);
afast = FastRational(numer_a, denom_a); bfast = FastRational(numer_b, denom_b);

@test a + b == afast + bfast
@test a - b == afast - bfast
@test a * b == afast * bfast
@test a // b == afast // bfast

@test fld( (@fastest_time $a + $b), (@fastest_time $afast + $bfast) ) >= 1
@test fld( (@fastest_time $a * $b), (@fastest_time $afast * $bfast) ) >= 1

# using BigInt

numer_a, denom_a = BigInt(5), BigInt(77)
numer_b, denom_b = BigInt(100), BigInt(17)
a = Rational(numer_a, denom_a); b = Rational(numer_b, denom_b);
afast = FastRational(numer_a, denom_a); bfast = FastRational(numer_b, denom_b);

@test a + b == afast + bfast
@test a - b == afast - bfast
@test a * b == afast * bfast
@test a // b == afast // bfast

@test fld( (@fastest_time $a + $b), (@fastest_time $afast + $bfast) ) >= 1
@test fld( (@fastest_time $a * $b), (@fastest_time $afast * $bfast) ) >= 1
