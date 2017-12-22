# FastRationals.jl

###### Copyright ©2017 by Jeffrey Sarnoff.

------------

### proof-of-concept


------------

```julia
Pkg.clone(...)

using FastRationals
using BenchmarkTools

macro fastest_time(this)
   :((@benchmark $this).times[1])
end

# using Int32s

numer_a, denom_a = Int32(5), Int32(77)
numer_b, denom_b = Int32(100), Int32(17)
a = Rational(numer_a, denom_a); b = Rational(numer_b, denom_b);
afast = FastRational(numer_a, denom_a); bfast = FastRational(numer_b, denom_b);
                                                             
fld( (@fastest_time $a + $b), (@fastest_time $afast + $bfast) )  # I get 20x
fld( (@fastest_time $a * $b), (@fastest_time $afast * $bfast) )  # I get 40x

# using Int64s

numer_a, denom_a = Int64(5), Int64(77)
numer_b, denom_b = Int64(100), Int64(17)
a = Rational(numer_a, denom_a); b = Rational(numer_b, denom_b);
afast = FastRational(numer_a, denom_a); bfast = FastRational(numer_b, denom_b);

fld( (@fastest_time $a + $b), (@fastest_time $afast + $bfast) )  # I get 8x
fld( (@fastest_time $a * $b), (@fastest_time $afast * $bfast) )  # I get 10x

# using Int128s

numer_a, denom_a = Int128(5), Int128(77)
numer_b, denom_b = Int128(100), Int128(17)
a = Rational(numer_a, denom_a); b = Rational(numer_b, denom_b);
afast = FastRational(numer_a, denom_a); bfast = FastRational(numer_b, denom_b);

fld( (@fastest_time $a + $b), (@fastest_time $afast + $bfast) )  # I get 1x
fld( (@fastest_time $a * $b), (@fastest_time $afast * $bfast) )  # I get 2x

# using BigInt

numer_a, denom_a = BigInt(5), BigInt(77)
numer_b, denom_b = BigInt(100), BigInt(17)
a = Rational(numer_a, denom_a); b = Rational(numer_b, denom_b);
afast = FastRational(numer_a, denom_a); bfast = FastRational(numer_b, denom_b);

fld( (@fastest_time $a + $b), (@fastest_time $afast + $bfast) )  # I get 2x
fld( (@fastest_time $a * $b), (@fastest_time $afast * $bfast) )  # I get 5x


```
