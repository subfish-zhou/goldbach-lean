import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiSourceRoundedGeometryPacket

open scoped Classical BigOperators Interval
open Finset MeasureTheory Set

namespace MathlibNt.SieveTheory

open LinearSieve SwitchingPrinciple
open SwitchingPrinciple.SuzukiLemma144KappaOne

set_option maxHeartbeats 800000

/-- Geometry and analytic contraction at Suzuki's source cutoff and the two
natural-ceiling Case-II cutoffs.  `bracket` is the explicit relative coefficient
closed by the analytic module; keeping it as a function makes this threshold
module independent of the currently unavailable Task-1 endpoint assembly. -/
structure SourceCaseIIEventualClosurePacket
    (S : BoundingSieve) (D : ℕ) (d s : ℝ) (bracket : ℝ → ℝ) : Prop where
  geometry : SourceRoundedGeometryPacket S D
    ⌈(D : ℝ) ^ (1 / (3 : ℝ))⌉₊
    ⌈(D : ℝ) ^ (1 / s)⌉₊ d s
  bracket_lt_one : bracket (D : ℝ) < 1


/-- Pure terminal algebra for Claim 14.5 Case II.  Under the intended
instantiation,

* `sourceSum` is the source parity sum;
* `V` is `suzukiVProduct S z`;
* `finiteLayer` is `finiteSourceLayer 1 2 N s`;
* `scale` is `C * exp (sqrt K) * errorEnvelope * (log D)^(-Δ)`.

Thus contraction of the relative bracket gives exactly
`sourceSum ≤ B0 + V * (finiteLayer + scale)`. -/
theorem source_caseII_close_relative_bracket
    {sourceSum V B0 finiteLayer scale bracket : ℝ}
    (hV : 0 ≤ V) (hscale : 0 ≤ scale) (hbracket : bracket < 1)
    (hassembled : sourceSum ≤ B0 + V * (finiteLayer + scale * bracket)) :
    sourceSum ≤ B0 + V * (finiteLayer + scale) := by
  have hc : scale * bracket ≤ scale := by
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left (le_of_lt hbracket) hscale
  have hadd : finiteLayer + scale * bracket ≤ finiteLayer + scale :=
    add_le_add le_rfl hc
  have hmul : V * (finiteLayer + scale * bracket) ≤
      V * (finiteLayer + scale) := mul_le_mul_of_nonneg_left hadd hV
  exact hassembled.trans (add_le_add le_rfl hmul)

/-!
## Exact residual production premises

After Task 1 exports the direct double-rounded endpoint theorem, the final
consumer should retain only the following genuine premises (with
`σ = sourceSigma D d`, `y = ⌈D^(1/3)⌉₊`, and `z = ⌈D^(1/s)⌉₊`):

1. `Section13HatContract H 2`, odd `N`, and `2 ≤ N`;
2. the recursive Claim-14.5 source bound at depth `N-1`;
3. source nonnegativity, logarithm, inherited/recursive-coordinate domain,
   Claim-14.6(i), and pointwise induction premises on `sigmaOneCarrier`;
4. the error-threshold, dimension-one local-product, Claim-14.6(ii), full-ceil,
   `T`-positivity, and Claim-14.13 pointwise premises;
5. `0 < Δ < 1`, `1 < s ≤ 3`, `2 ≤ K`, and the fixed constant signs;
6. Claim-14.6(iii), the source-correct cubic lambda comparison, and the
   nonnegative final scale.

The following are intentionally absent: every large-`D`/size hypothesis,
`D^(1/3) = y`, any perfect-power hypothesis, `hRaw`, and any abstract endpoint
packet.  `SourceCaseIIEventualClosurePacket.geometry` supplies all cutoff facts;
`bracket_lt_one` and `source_caseII_close_relative_bracket` perform analytic and
terminal closure.
-/


end MathlibNt.SieveTheory
