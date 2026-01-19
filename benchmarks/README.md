# Origin of the Benchmark Files

## Benchmarks from ByMC

The benchmark files in the directories `BYMC` and `TACO` have been taken from
the
[`fault-tolerant-benchmarks`](https://github.com/konnov/fault-tolerant-benchmarks)
repository owned by Igor Konnov. Please note the license under which they are
distributed (see section [License](#license)).

In benchmarks in the `BYMC` folder, liveness properties have been removed (for
benchmarking purposes). Additionally, the formatting might be altered
for some of these benchmarks.

For compatibility with TACO we need to modify

- `tendermint-1round-safety.ta` from the folder `lmcs`
- the benchmarks in `random19`,

as not all rules in these benchmarks have unique ids. TACO does not allow
clashes in rule ids, as it would make the counter example imprecise. We only
modified the ids of the rules.

### Selected Benchmarks

The original repo contains multiple versions of some benchmarks (for more
information see the
[repo](https://github.com/konnov/fault-tolerant-benchmarks/tree/master)).

We exclude:

- `spin13`: as they were designed for SPIN not for ByMC.
- `fmcad13`: as the Promela translation fails with syntax errors.
- `forte20`: as they were only example files that were used for a tutorial.
- `opodis17`: as they are benchmarks for synthesis (which is not supported by TACO).
- `cav15/ta`: as these benchmarks do not contain specifications.

### Generation of the Benchmarks

Benchmarks that are not already in the `.ta` format have been first translated
using [ByMC] (using ByMC inside a container built from
[this Dockerfile](https://github.com/pleich/bymc/blob/0bca349cc7d3e8511f649726be4ce990f458c00a/bymc/Dockerfile)).

ByMC outputs the threshold automaton generated from a Promela specification
inside the output directory (`x/<BENCHMARK_NAME_+_RANDOM_STRING>/`) as a file
named `fuse.sk`.

### License

These benchmarks fall under the following license:

```
(C) 2012-2014, Igor Konnov, Josef Widder, Annu Gmeiner, Helmut Veith, Ulrich Schmid,
Forsyte, Institute of Information Systems, Vienna University of Technology

All rights reserved. Redistribution and use in source and binary forms, with
or without modification, are permitted provided that the following
conditions are met:

  1. Redistributions of source code must retain the above copyright
     notice, this list of conditions and the following disclaimer.

  2. Redistributions in binary form must reproduce the above copyright
     notice, this list of conditions and the following disclaimer in the
     documentation and/or other materials provided with the distribution.

  3. All advertising materials mentioning features or use of this software
     must display the following acknowledgement:

     This product includes software developed by
     Igor Konnov, Josef Widder, Annu Gmeiner, Helmut Veith, Ulrich Schmid,
     Forsyte, Institute of Information Systems, Vienna University of Technology

  4. Neither the name of the University nor the names of its contributors
     may be used to endorse or promote products derived from this software
     without specific prior written permission.


THIS SOFTWARE IS PROVIDED BY THE REGENTS AND CONTRIBUTORS `AS IS'' AND ANY
EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
DISCLAIMED.  IN NO EVENT SHALL THE REGENTS OR CONTRIBUTORS BE LIABLE FOR ANY
DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
(INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
(INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF
THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
```

Taken from <https://github.com/konnov/fault-tolerant-benchmarks/blob/master/LICENSE>
on 01.12.2025.

The benchmarks in the folders `BYMC/big-benchmarks` and `TACO/big-benchmarks`
have been generated from the respective PROMELA files (also taken from the
above repository) the benchmarks files and have been generated using
[ByMC](https://github.com/konnov/bymc).

ByMC is distributed under the following license:

```
Copyright 2012-2017 Igor Konnov, Josef Widder, Helmut Veith,
Forsyte, Institute of Information Systems, Vienna University of Technology

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions are met:

1. Redistributions of source code must retain the above copyright notice, this
list of conditions and the following disclaimer.

2. Redistributions in binary form must reproduce the above copyright notice,
this list of conditions and the following disclaimer in the documentation
and/or other materials provided with the distribution.

3. Neither the name of the copyright holder nor the names of its contributors
may be used to endorse or promote products derived from this software without
specific prior written permission.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND
ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE
FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
```

Taken from <https://github.com/konnov/bymc/blob/master/LICENSE> on 01.12.2025.

## RedBelly & Reset Benchmarks

The benchmarks in the folders `reset-benchmarks` and `red-belly` have been
created by Mouhammad Skar, Tom Baumeister and are distributed under the same
[Apache-2.0 license](../LICENSE) as the rest of TACO.

[ByMC]: https://github.com/konnov/bymc
