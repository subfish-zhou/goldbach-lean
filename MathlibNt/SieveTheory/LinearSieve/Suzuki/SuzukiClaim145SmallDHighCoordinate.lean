import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma143FullTail
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144ExplicitRemaindersSourceOrder

open scoped Classical BigOperators Interval
open Finset MeasureTheory Set Filter Topology
open Asymptotics

namespace MathlibNt.SieveTheory

open LinearSieve SwitchingPrinciple SuzukiFiniteContinuousLayers
open SwitchingPrinciple.SuzukiLemma144Equation1410
open SwitchingPrinciple.SuzukiLemma144KappaOne

set_option maxHeartbeats 1200000

/-!
# Claim 14.5, source-small-D high-coordinate branch

Suzuki's Case A assumes `2 ≤ s` and `log D ≤ C₁ K^ΘK`; it then applies
Lemma 14.3 and compares that explicit exponential-tail majorant with (14.6).
The definitions below retain those exact inputs.  In particular, no
`Claim14_5Bound` or final Lemma-14.4 estimate is accepted as a premise.
-/

/-- The scalar comparison in Suzuki Claim 14.5, Case A, after Lemma 14.3.
The source-small-D condition is an argument of the comparison rather than being
silently replaced by an arbitrary finite-cutoff condition. -/
def Claim145SmallDCaseAScalarComparison
    (S : BoundingSieve) (H : Section13HatLayers)
    (d Δ C145 K C1 ΘK : ℝ) : Prop :=
  ∀ (n q p : ℕ) (x : ℝ), 2 ≤ q →
    p = ⌈(q : ℝ) ^ (1 / x)⌉₊ → 2 ≤ x →
    Real.log (q : ℝ) ≤ C1 * K ^ ΘK →
    suzukiSourceL (p : ℝ) K ^ (⌊x - 2⌋₊ + 1) /
          ((⌊x - 2⌋₊ + 1).factorial : ℝ) *
        Real.exp (suzukiSourceL (p : ℝ) K) ≤
      C145 * claim14_5Scale S H n (q : ℝ) d Δ
        (sourceSigma (q : ℝ) d) K x


/-- The moving source cutoff is positive already for every natural `q ≥ 2`;
no eventual threshold is needed in the finite quotient branch. -/
theorem sourceSigma_pos_of_nat_two_le
    {q : ℕ} {d : ℝ} (hq : 2 ≤ q) :
    0 < sourceSigma (q : ℝ) d := by
  have hq1 : (1 : ℝ) < (q : ℝ) := by exact_mod_cast (show 1 < q by omega)
  have hlogq : 0 < Real.log (q : ℝ) := Real.log_pos hq1
  have harg : 0 < 27 * (q : ℝ) := by positivity
  have hexp : Real.exp 1 < 27 * (q : ℝ) := by
    refine Real.exp_one_lt_d9.trans ?_
    have hqR : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    nlinarith
  have honeLog : 1 < Real.log (27 * (q : ℝ)) :=
    (Real.lt_log_iff_exp_lt harg).2 hexp
  unfold sourceSigma
  exact mul_pos (Real.rpow_pos_of_pos hlogq _) (Real.log_pos honeLog)

/-- The logarithmic side condition used below is not valid for every `K > 1`,
but it is uniform on the source high-coordinate region once `K` crosses a fixed
threshold.  This isolates exactly the small-`K` split hidden by `≪`: `log K` is
positive for `K > 1`, and `log log K = o(log K)` gives, eventually,
`log K ≤ 4 log s` for every `s ≥ √K / log K`. -/
theorem claim145_caseA_highS_log_relation_eventually :
    ∀ᶠ K : ℝ in atTop, 1 < K ∧ ∀ s : ℝ,
      Real.sqrt K / Real.log K ≤ s → Real.log K ≤ 4 * Real.log s := by
  have hlo := Real.isLittleO_log_id_atTop.bound
    (show (0 : ℝ) < 1 / 4 by norm_num)
  have hcomp : ∀ᶠ K : ℝ in atTop,
      |Real.log (Real.log K)| ≤ (1 / 4 : ℝ) * |Real.log K| :=
    Real.tendsto_log_atTop.eventually hlo
  filter_upwards [eventually_gt_atTop (1 : ℝ),
      Real.tendsto_log_atTop.eventually_ge_atTop 1, hcomp] with K hK hlogK1 hll
  refine ⟨hK, ?_⟩
  intro s hs
  have hlogK : 0 < Real.log K := Real.log_pos hK
  have hsqrt : 0 < Real.sqrt K := Real.sqrt_pos.2 (by linarith)
  have hs0 : 0 < s := (div_pos hsqrt hlogK).trans_le hs
  have hsqrtle : Real.sqrt K ≤ s * Real.log K :=
    (div_le_iff₀ hlogK).mp hs
  have hlogineq := Real.log_le_log hsqrt hsqrtle
  rw [Real.log_sqrt (by linarith),
    Real.log_mul (ne_of_gt hs0) (ne_of_gt hlogK)] at hlogineq
  rw [abs_of_nonneg (Real.log_nonneg hlogK1),
    abs_of_nonneg hlogK.le] at hll
  nlinarith

/-- The first `≪` in Suzuki Claim 14.5, Case A, high-`s` branch, with
the implicit constant made explicit.  Positivity of `log K` is exactly `1 < K`;
`log K ≤ 4 log s` is the large-`K` threshold consequence used to square
`s ≥ √K / log K`.  The result is the literal
`log D ≪ K^Θ ≪ s^(2Θ) (log s)^(2Θ)` chain. -/
theorem claim145_caseA_highS_power_chain
    {D K s C1 Θ : ℝ}
    (hK : 1 < K) (hs : Real.sqrt K / Real.log K ≤ s)
    (hlogs : Real.log K ≤ 4 * Real.log s)
    (hC1 : 0 ≤ C1) (hΘ : 0 ≤ Θ)
    (hsmall : Real.log D ≤ C1 * K ^ Θ) :
    Real.log D ≤ C1 * (16 : ℝ) ^ Θ * s ^ (2 * Θ) * (Real.log s) ^ (2 * Θ) := by
  have hlogK : 0 < Real.log K := Real.log_pos hK
  have hsqrt : 0 < Real.sqrt K := Real.sqrt_pos.2 (by linarith)
  have hs0 : 0 < s := (div_pos hsqrt hlogK).trans_le hs
  have hlogs0 : 0 < Real.log s := by nlinarith [hlogs]
  have hsqrt_le : Real.sqrt K ≤ s * Real.log K := by
    exact (div_le_iff₀ hlogK).mp hs
  have hsqrt_le' : Real.sqrt K ≤ 4 * s * Real.log s := by
    calc
      Real.sqrt K ≤ s * Real.log K := hsqrt_le
      _ ≤ s * (4 * Real.log s) := mul_le_mul_of_nonneg_left hlogs hs0.le
      _ = 4 * s * Real.log s := by ring
  have hKnonneg : 0 ≤ K := by linarith
  have hKbound : K ≤ 16 * s ^ 2 * (Real.log s) ^ 2 := by
    have hrhs0 : 0 ≤ 4 * s * Real.log s := by positivity
    have hsquare : (Real.sqrt K) ^ 2 ≤ (4 * s * Real.log s) ^ 2 :=
      (sq_le_sq₀ hsqrt.le hrhs0).2 hsqrt_le'
    rw [Real.sq_sqrt hKnonneg] at hsquare
    nlinarith
  have hrpow := Real.rpow_le_rpow hKnonneg hKbound hΘ
  have hfactor : (16 * s ^ 2 * (Real.log s) ^ 2) ^ Θ =
      (16 : ℝ) ^ Θ * s ^ (2 * Θ) * (Real.log s) ^ (2 * Θ) := by
    rw [Real.mul_rpow (by positivity : (0 : ℝ) ≤ 16 * s ^ 2) (sq_nonneg _),
      Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 16) (sq_nonneg s)]
    have hs2 : s ^ (2 : ℕ) = s ^ (2 : ℝ) := by norm_num [Real.rpow_two]
    have hls2 : (Real.log s) ^ (2 : ℕ) = (Real.log s) ^ (2 : ℝ) := by
      norm_num [Real.rpow_two]
    rw [hs2, hls2, ← Real.rpow_mul hs0.le, ← Real.rpow_mul hlogs0.le]
  rw [hfactor] at hrpow
  calc
    Real.log D ≤ C1 * K ^ Θ := hsmall
    _ ≤ C1 * ((16 : ℝ) ^ Θ * s ^ (2 * Θ) * (Real.log s) ^ (2 * Θ)) :=
      mul_le_mul_of_nonneg_left hrpow hC1
    _ = _ := by ring


end MathlibNt.SieveTheory
