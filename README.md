# FastRationals.jl

##### Copyright ©2017 by Jeffrey Sarnoff.   Available to Julia without restriction.

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

a_q = Rational(5,77);         b_q = Rational(100, 17);
a_fastq = FastRational(5,77); b_fastq =FastRational(100,17);

round( (@fastest $a_q + $b_q) / (@fastest $a_fastq + $b_fastq), 1 )

round( (@fastest $a_q * $b_q) / (@fastest $a_fastq * $b_fastq), 1 )
```
