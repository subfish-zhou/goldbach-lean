# Clean-build benchmark

## Recorded results

| Measurement | v1.0.0-rc1 | v1.0.0 |
|---|---:|---:|
| Elapsed time | 2,183.42 seconds (36:23) | 1,806.48 seconds (30:06) |
| Sampled peak proportional memory (PSS) | 5.97 GiB | 6.85 GiB |
| Sampled peak resident memory (RSS) | 10.48 GiB | 10.43 GiB |
| Samples | 1,919 | 1,609 |
| PSS read failures | 102 | 100 |

The v1.0.0 run took 376.94 fewer seconds, a 17.3% reduction in elapsed time.
Its sampled proportional-memory peak increased. Both records use an Intel Xeon
Platinum 8370C with 32 logical CPUs, `LEAN_NUM_THREADS=2`, and `lake -Kjobs=8`.
The v1.0.0 invocation also uses `--wfail` and completed with zero warnings.

Each entry is a single recorded run. Timing depends on machine load and cache
state. The release-candidate entry is the original recorded measurement; the
v1.0.0 run uses a separate clean checkout and includes the new Blueprint module.

The full records are [v1.0.0-rc1](benchmarks/v1.0.0-rc1.json) and
[v1.0.0](benchmarks/v1.0.0.json). The latter records proof-source revision
`86fca7d54db4f431b64f52596519d275f05c28c6` and matching source fingerprints before
and after the build. The fingerprint covers the four libraries and core
Lake/toolchain files. Website and Markdown edits are tracked separately in Git.

## What is timed

The benchmark starts with cached, pinned third-party dependencies and zero
compiled project `.olean` files. It measures the complete default Lake build:
`AnalyticNumberTheory`, `PrimeNumberTheoremAnd`, `MathlibNt`, and `Goldbach`,
including the public theorem checks and the Lean Blueprint annotations.

Toolchain installation, dependency downloads, cache preparation, documentation
rendering, and independent proof replay are performed outside the timing interval.
The `-Kjobs=8` setting is part of the recorded invocation; the sampler separately
records the observed process count.

## Memory measurement

The sampler records Lake and its observed descendants approximately once per
second. Proportional set size (PSS) apportions shared pages among processes;
resident set size (RSS) counts each process's resident pages, including shared
pages in each process. The table reports process-tree sample peaks in gibibytes
(GiB, 2^30 bytes). Filesystem cache and unrelated jobs are outside the sample.
The JSON records retain exact byte values and PSS read-failure counts.

These observations describe the memory used during the recorded builds.
Determining a minimum RAM configuration requires a separate constrained-memory
experiment.

## Reproduce

Start from a fresh checkout with uncompiled project sources:

```sh
git clone https://github.com/subfish-zhou/goldbach-lean.git
cd goldbach-lean
git checkout v1.0.0
unset LEAN_PATH LEAN_SRC_PATH
lake exe cache get
lake --wfail build Architect
python3 scripts/benchmark_build.py --output ../goldbach-build-benchmark
```

The `Architect` target prepares the Blueprint dependency while leaving project
modules uncompiled. The benchmark script checks this starting state, rejects
runs that compile third-party modules inside the measured interval, and requires
a fresh output directory. It writes the complete build log and a JSON record
containing exit status, source revision and fingerprint, machine information,
elapsed time, and sampled process memory.

Run `python3 scripts/check.py` and
`lake env leanchecker --verbose Goldbach.Theorem` separately for the public
statement, axiom reports, and independent replay. The full verification procedure
is in [VERIFICATION.md](VERIFICATION.md).
