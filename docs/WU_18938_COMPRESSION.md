> Historical second-phase snapshot. The subsequent [structural simplification](WU_STRUCTURAL_SIMPLIFICATION.md) records current source counts and acceptance.

# Wu: public 1+1.8938 and a second compression preserving precision

This phase exposes the already certified internal parameter as the public
unconditional theorem `WuPaper.ClassicalSlots.one8938`: there exists `T ≥ 512`
such that every even `N ≥ T` has `N = p + r*q`, where `p` and `q` are prime,
`r = 1` or prime, and

```text
r^5000 ≤ q^4469
```

This is the natural-power form of `r ≤ q^(4469/5000)`, corresponding to
1+1.8938. The existing `one894` interface and its exact condition
`r^500 ≤ q^447` are also retained.

## Why stronger numerical certificates are unnecessary

`WRefinedCountBridge.from_actual_count` already proves a positive margin on the
`9469/5000` counting carrier and returns actual representations satisfying the
`4469/5000` power constraint. The new
`WR2XiSourceRefinedTarget.one8938_of_coefficient` converts it to a natural-power
comparison using the existing `MathlibNt.nat_pow_le_iff_le_rpow`.
The final entry uses the original `target_of_integral_bounds`, `classical_lower`
and `sixth_gain_lower`. Integral errors, logarithm orders, rounding precision
and coefficient budgets are unchanged.

## Further duplicate proofs removed

The C term still uses 4,096 midpoints and the original eighth-term integral
still uses 2,048. Both payment tables are byte-for-byte unchanged. The new
`WR2ClassicalCTableCheck` and `WR2ClassicalEighthTableCheck` prove that embedding
the exact rational formulas into the reals gives the original formulas.
Blocks of 64 points are checked by `decide +kernel`, replacing individual
`norm_num` expansions and repeated coordinate substitutions. Block size affects
proof organization, without changing the integration mesh.

The two original families of 770 generated proof modules, including their
aggregate entries, become 98 modules plus two shared helpers: a net reduction
of 670 modules. Size measurements include the new public theorem and helpers.

This phase starts from the previously accepted 5,441-module version, rather
than the original 8,826-module version. The
[previous report](WU_PRECISION_COMPRESSION.md) remains historical evidence.

## Validation and measurements

| Scope | Modules: previous → current | Effective code lines: previous → current | Net saving |
|---|---:|---:|---:|
| Final theorem import closure | 5,059 → 4,389 | 755,925 → 688,336 | 67,589 (8.94%) |
| Complete research tree | 5,441 → 4,771 | 796,263 → 728,674 | 67,589 (8.49%) |

This phase also removes 73,714 physical lines and 4,039,754 source bytes.
Compared with the original 1,126,636-line closure, the two phases save
**438,300 lines (38.90%)**. All additions are included. External Lake dependencies
are excluded; these figures do not measure a minimal declaration-level proof.

All **4,771** modules pass the build and source/object/dependency receipt checks.
Both new and legacy literal propositions, axiom checks, independent kernel
replays of the two new public modules, the refined counting conversion module
and the final module pass. Only the standard logical axioms `propext`,
`Classical.choice` and `Quot.sound` occur.

Declaration comparison preserves the kinds and types of 216,096 public
declarations. Changes are explicitly limited to internal finite blocks, their
generated coverage/simplification helpers, and the added public result. Existing
public mathematical interfaces are unchanged. One generated payment equality
moves to a shared module; its old and new types were additionally checked to
match. The 13 numerical tables involved across both phases are byte-for-byte
unchanged, as are the 4,669 original modules outside this phase's cohort.

See the [size record](../research/wu18938-audit/source-size.json),
[declaration comparison](../research/wu18938-audit/type-comparison.json) and
[validation record](../research/wu18938-audit/validation.json).

## Reproduction

Run in `research/wu2008`:

```sh
python3 diagnostics/classical_c_eighth_certificates.py --check src
python3 verify_sources.py
python3 build.py --all --jobs 4 --lean-threads 2
python3 check_classical.py
```

`check_classical.py` checks the literal propositions of both the new `one8938`
and compatible `one894`, rejecting nonstandard axiom dependencies. Independent
kernel replays use imports rebuilt in this research tree. Measurement tools and
the per-module baseline are in `research/wu18938-audit`.
