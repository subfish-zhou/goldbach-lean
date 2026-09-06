# Clean-build benchmark

## What is timed

The benchmark starts with cached, pinned third-party dependencies and **no
compiled project `.olean` files**. It measures the complete default Lake build:
`AnalyticNumberTheory`, `PrimeNumberTheoremAnd`, `MathlibNt`, and `Goldbach`,
including the public theorem checks and the Lean Blueprint annotations.

Toolchain installation, dependency downloads, cache preparation, API HTML
generation, and Blueprint web rendering are outside this timing interval.
An incremental build is not a substitute for this measurement.

The release-candidate baseline used `LEAN_NUM_THREADS=2` and
`lake -Kjobs=8 build`. The v1.0.0 benchmark preserves these settings and adds
`--wfail`, so warnings make the build fail. The `-Kjobs=8` setting is recorded
as part of the invocation; it is not a measurement of simultaneous processes.

## Reproduce

Use a fresh checkout. Do not copy project build outputs into it.

```sh
git clone https://github.com/subfish-zhou/goldbach-lean.git
cd goldbach-lean
git checkout v1.0.0
lake exe cache get
lake --wfail build Architect
python3 scripts/benchmark_build.py --output ../goldbach-build-benchmark
```

The `Architect` target prepares the new Blueprint dependency without compiling
project modules. A run that still compiles third-party modules is rejected as
a cached-dependency benchmark.

The script refuses to run if project `.olean` files already exist, and refuses
to overwrite an existing output directory. It writes the complete build log
and a JSON record containing the exit status, source revision, source-file
fingerprint, machine information, elapsed time, and sampled process memory.
The fingerprint covers the four libraries and the core Lake/toolchain files;
subsequent changes to this report do not alter that fingerprint.

Run `python3 scripts/check.py` separately to check the public statement and
axiom reports. A fast build alone does not establish the mathematical meaning
or unconditionality of a theorem.

## Historical baseline

The original `v1.0.0-rc1` run took **2183.42 seconds (36 minutes 23 seconds)**
on an Intel Xeon Platinum 8370C host with 32 logical CPUs. Its record is
[`benchmarks/v1.0.0-rc1.json`](benchmarks/v1.0.0-rc1.json).
It is an existing measurement, not a new run of the old source.

Elapsed-time comparisons are single-run observations, not controlled causal
estimates of optimization speedup. They depend on machine load and cache state.
The new version also contains Blueprint annotations absent from the old build.
Sampled resident/proportional memory is a process-tree observation, not a
minimum-RAM requirement.
