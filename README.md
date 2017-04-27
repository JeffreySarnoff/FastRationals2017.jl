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

a_q = Rational{Int64}(5,77);         b_q = Rational{Int64}(100, 17);
a_fastq = FastRational{Int64}(5,77); b_fastq = FastRational{Int64}(100,17);

fld( (@fastest $a_q + $b_q), (@fastest $a_fastq + $b_fastq) )
fld( (@fastest $a_q * $b_q), (@fastest $a_fastq * $b_fastq) )

a_q = Rational{Int32}(5,77);         b_q = Rational{Int32}(100, 17);
a_fastq = FastRational{Int32}(5,77); b_fastq = FastRational{Int32}(100,17);

fld( (@fastest $a_q + $b_q), (@fastest $a_fastq + $b_fastq) )
fld( (@fastest $a_q * $b_q), (@fastest $a_fastq * $b_fastq) )


```
