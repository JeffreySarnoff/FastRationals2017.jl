# FastRationals.jl

###### Copyright ©2017 by Jeffrey Sarnoff.

------------

### proof-of-concept


------------

```julia
Pkg.clone(...)

using FastRationals
using BenchmarkTools

macro fastest(this)
   :((@benchmark $this).times[1])
end

a_numer, a_denom = Int64(5), Int64(77)
b_numer, b_denom = Int64(100), Int64(17)

a_q = Rational(a_numer, a_denom);         b_q = Rational(b_numer, b_denom);
a_fastq = FastRational(a_numer, a_denom); b_fastq = FastRational(b_numer, b_denom);

fld( (@fastest $a_q + $b_q), (@fastest $a_fastq + $b_fastq) )  # I get 6.0
fld( (@fastest $a_q * $b_q), (@fastest $a_fastq * $b_fastq) )  # I get 7.0

a_numer, a_denom = Int32(5), Int32(77)
b_numer, b_denom = Int32(100), Int32(17)

a_q = Rational(a_numer, a_denom);         b_q = Rational(b_numer, b_denom);
a_fastq = FastRational(a_numer, a_denom); b_fastq = FastRational(b_numer, b_denom);

fld( (@fastest $a_q + $b_q), (@fastest $a_fastq + $b_fastq) ) # I get  9.0
fld( (@fastest $a_q * $b_q), (@fastest $a_fastq * $b_fastq) ) # I get 15.0


```
