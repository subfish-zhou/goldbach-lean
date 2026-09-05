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

/-- The actual `Claim14_5Bound` in the source-small-D alternative follows from
production Lemma 14.3 and the Case-A scalar comparison. -/
theorem claim14_5Bound_of_smallD_caseA_scalarComparison
    (S : BoundingSieve) (H : Section13HatLayers)
    {n q p : ℕ} {x d Δ C145 K C1 ΘK : ℝ}
    (hlocal : HasDimensionOneLocalProductBound S K)
    (hq : 2 ≤ q) (hp : p = ⌈(q : ℝ) ^ (1 / x)⌉₊) (hx : 2 ≤ x)
    (hsmall : Real.log (q : ℝ) ≤ C1 * K ^ ΘK)
    (hscalar : Claim145SmallDCaseAScalarComparison
      S H d Δ C145 K C1 ΘK) :
    Claim14_5Bound
      (fun m D' z' => suzukiActualT S m ⌈D'⌉₊ ⌈z'⌉₊)
      S H n (q : ℝ) (p : ℝ) d Δ
        (sourceSigma (q : ℝ) d) K x C145 := by
  have h143 := suzukiLemma14_3_natCeil_uniform_explicit
    (S := S) (N := n) (D := q) (z := p) (s := x) (K := K)
    hlocal (by omega) hx hp
  unfold Claim14_5Bound
  simpa using h143.trans (hscalar n q p x hq hp hx hsmall)

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

/-- The decisive logarithmic gain in the same source branch.  The displayed
`hgrowth` is the exact threshold inequality hidden by the source `O(1)`; under
it the error can be taken to be zero.  No compactness or finite-quotient
maximum is used. -/
theorem claim145_caseA_highS_log_gain_of_growth
    {D K s d C1 Θ : ℝ}
    (hD : 1 < D) (hK : 1 < K) (hs : 1 < s)
    (hC1 : 0 < C1)
    (hchain : Real.log D ≤ C1 * (16 : ℝ) ^ Θ * s ^ (2 * Θ) *
      (Real.log s) ^ (2 * Θ))
    (hgrowth :
      (C1 * (16 : ℝ) ^ Θ) * (Real.log s) ^ (2 * Θ) *
          (Real.log (3 * K) * (Real.log (3 * s)) ^ 2) ≤
        s ^ (d - 2 * Θ)) :
    s * (Real.log (Real.log (3 * K)) +
        2 * Real.log (Real.log (3 * s))) ≤
      s * Real.log (1 + s ^ d / Real.log D) := by
  have hlogD : 0 < Real.log D := Real.log_pos hD
  have hlogK3 : 0 < Real.log (3 * K) := Real.log_pos (by nlinarith)
  have hlogs3 : 0 < Real.log (3 * s) := Real.log_pos (by nlinarith)
  have hs0 : 0 < s := by linarith
  have hlogs : 0 < Real.log s := Real.log_pos hs
  have hA : 0 < C1 * (16 : ℝ) ^ Θ := mul_pos hC1 (Real.rpow_pos_of_pos (by norm_num) _)
  let B : ℝ := Real.log (3 * K) * (Real.log (3 * s)) ^ 2
  have hB : 0 < B := mul_pos hlogK3 (sq_pos_of_pos hlogs3)
  have hdenBound : Real.log D * B ≤ s ^ d := by
    have hchain' := mul_le_mul_of_nonneg_right hchain hB.le
    have hpowid : s ^ d = s ^ (d - 2 * Θ) * s ^ (2 * Θ) := by
      rw [← Real.rpow_add hs0]
      congr 1
      ring
    rw [hpowid]
    dsimp [B] at hchain' ⊢
    have hsPow : 0 ≤ s ^ (2 * Θ) := Real.rpow_nonneg hs0.le _
    calc
      Real.log D * (Real.log (3*K) * Real.log (3*s)^2) ≤
          (C1 * 16 ^ Θ * s ^ (2*Θ) * Real.log s ^ (2*Θ)) *
            (Real.log (3*K) * Real.log (3*s)^2) := hchain'
      _ = ((C1 * 16 ^ Θ) * Real.log s ^ (2*Θ) *
            (Real.log (3*K) * Real.log (3*s)^2)) * s ^ (2*Θ) := by ring
      _ ≤ s ^ (d - 2*Θ) * s ^ (2*Θ) :=
        mul_le_mul_of_nonneg_right hgrowth hsPow
  have hratio : B ≤ s ^ d / Real.log D := by
    exact (le_div_iff₀ hlogD).2 (by simpa [mul_comm] using hdenBound)
  have hBone : B ≤ 1 + s ^ d / Real.log D := hratio.trans (le_add_of_nonneg_left (by norm_num))
  have hbase : 0 < 1 + s ^ d / Real.log D := by positivity
  have hlog := Real.log_le_log hB hBone
  have hlogB : Real.log B = Real.log (Real.log (3*K)) +
      2 * Real.log (Real.log (3*s)) := by
    dsimp [B]
    rw [Real.log_mul (ne_of_gt hlogK3) (ne_of_gt (sq_pos_of_pos hlogs3)),
      Real.log_pow]
    norm_num
  rw [hlogB] at hlog
  exact mul_le_mul_of_nonneg_left hlog hs0.le

/-- Equation (14.3), namely `d - 2Θ > 0`, supplies the omitted threshold:
the logarithmic factor in the preceding theorem is eventually dominated by
`s^(d-2Θ)`.  This is the source route, via the standard
`(log s)^a = o(s^b)` estimate, rather than a finite-`q` maximum. -/
theorem claim145_caseA_highS_growth_eventually
    {K d C1 Θ : ℝ} (hK : 1 < K) (hC1 : 0 < C1)
    (hgap : 0 < d - 2 * Θ) :
    ∀ᶠ s : ℝ in Filter.atTop,
      (C1 * (16 : ℝ) ^ Θ) * (Real.log s) ^ (2 * Θ) *
          (Real.log (3 * K) * (Real.log (3 * s)) ^ 2) ≤
        s ^ (d - 2 * Θ) := by
  let A : ℝ := 4 * (C1 * (16 : ℝ) ^ Θ) * Real.log (3 * K)
  have hlog3K : 0 < Real.log (3 * K) := Real.log_pos (by nlinarith)
  have hA : 0 < A := by dsimp [A]; positivity
  have heps : 0 < 1 / (A + 1) := by positivity
  have hlo := (isLittleO_log_rpow_rpow_atTop (2 * Θ + 2) hgap).bound heps
  filter_upwards [hlo, Filter.eventually_ge_atTop 3] with s hlo hs3
  have hs0 : 0 < s := by linarith
  have hlogs : 0 < Real.log s := Real.log_pos (by linarith)
  have hlog3s : Real.log (3 * s) ≤ 2 * Real.log s := by
    rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) (ne_of_gt hs0)]
    have hlog3le : Real.log 3 ≤ Real.log s :=
      Real.strictMonoOn_log.monotoneOn (by norm_num) hs0 hs3
    linarith
  have hlog3s0 : 0 ≤ Real.log (3 * s) :=
    (Real.log_pos (by nlinarith)).le
  have hsPow : 0 ≤ s ^ (d - 2 * Θ) := Real.rpow_nonneg hs0.le _
  have hmain : A * (Real.log s) ^ (2 * Θ + 2) ≤ s ^ (d - 2 * Θ) := by
    change |(Real.log s) ^ (2 * Θ + 2)| ≤
      1 / (A + 1) * |s ^ (d - 2 * Θ)| at hlo
    rw [abs_of_nonneg (Real.rpow_nonneg hlogs.le _), abs_of_nonneg hsPow] at hlo
    have hscaled := mul_le_mul_of_nonneg_left hlo hA.le
    have hfrac : A * (1 / (A + 1)) ≤ 1 := by
      rw [div_eq_mul_inv, ← mul_assoc]
      exact (div_le_one (by positivity : 0 < A + 1)).2 (by linarith)
    calc
      A * (Real.log s) ^ (2 * Θ + 2) ≤
          (A * (1 / (A + 1))) * s ^ (d - 2 * Θ) := by
            nlinarith
      _ ≤ 1 * s ^ (d - 2 * Θ) := mul_le_mul_of_nonneg_right hfrac hsPow
      _ = _ := one_mul _
  have hlogSquare : (Real.log (3 * s)) ^ 2 ≤ 4 * (Real.log s) ^ 2 := by
    nlinarith [sq_le_sq₀ hlog3s0 (by positivity : 0 ≤ 2 * Real.log s) |>.2 hlog3s]
  have hfront : 0 ≤ (C1 * (16 : ℝ) ^ Θ) * (Real.log s) ^ (2 * Θ) *
      Real.log (3 * K) := by positivity
  calc
    (C1 * 16 ^ Θ) * Real.log s ^ (2 * Θ) *
        (Real.log (3 * K) * Real.log (3 * s) ^ 2) =
      ((C1 * 16 ^ Θ) * Real.log s ^ (2 * Θ) * Real.log (3 * K)) *
        Real.log (3 * s) ^ 2 := by ring
    _ ≤ ((C1 * 16 ^ Θ) * Real.log s ^ (2 * Θ) * Real.log (3 * K)) *
        (4 * Real.log s ^ 2) := mul_le_mul_of_nonneg_left hlogSquare hfront
    _ = A * Real.log s ^ (2 * Θ + 2) := by
      dsimp [A]
      rw [Real.rpow_add hlogs]
      norm_num [Real.rpow_two]
      ring
    _ ≤ s ^ (d - 2 * Θ) := hmain

/-- The complete analytic chain on the source high-`s` side of Case A.  After
one source threshold in `s`, the hypotheses `s ≥ √K/log K` and
`log K ≤ 4 log s` turn the small-`D` alternative into the logarithmic gain
used between Lemma 14.3 and (14.6).  The latter two production interfaces are
then connected by `claim14_5Bound_of_smallD_caseA_scalarComparison` above.
The statement deliberately retains the threshold relation instead of replacing
it by compactness or a maximum over finitely many quotients. -/
theorem claim145_caseA_highS_log_gain_eventually
    {K d C1 Θ : ℝ} (hK : 1 < K) (hC1 : 0 < C1)
    (hΘ : 0 ≤ Θ) (hgap : 0 < d - 2 * Θ) :
    ∀ᶠ s : ℝ in atTop, ∀ D : ℝ, 1 < D →
      Real.sqrt K / Real.log K ≤ s →
      Real.log K ≤ 4 * Real.log s →
      Real.log D ≤ C1 * K ^ Θ →
      s * (Real.log (Real.log (3 * K)) +
          2 * Real.log (Real.log (3 * s))) ≤
        s * Real.log (1 + s ^ d / Real.log D) := by
  filter_upwards [claim145_caseA_highS_growth_eventually hK hC1 hgap,
      eventually_gt_atTop (1 : ℝ)] with s hgrowth hs
  intro D hD hhigh hlogrel hsmall
  have hchain := claim145_caseA_highS_power_chain hK hhigh hlogrel hC1.le hΘ hsmall
  exact claim145_caseA_highS_log_gain_of_growth hD hK hs hC1 hchain hgrowth

/-- Scalar normalization from the Claim-14.5 `V(q)` scale to the predecessor
`V(p)` error envelope.  The only numerical input is the exposed coefficient
inequality `C145 ≤ C log(q) σ(q)`; Euler monotonicity and positivity are proved
here. -/
theorem claim14_5Scale_le_vProduct_errorEnvelope_of_coefficient
    (S : BoundingSieve) (H : Section13HatLayers)
    {n q p : ℕ} {x d Δ C C145 K : ℝ}
    (hH : Section13HatContract H 2)
    (hq : 2 ≤ q) (hx : 2 ≤ x)
    (hpower : (q : ℝ) ^ (1 / x) = (p : ℝ))
    (hσ : 0 < sourceSigma (q : ℝ) d)
    (hC145 : 0 ≤ C145)
    (hcoef : C145 ≤ C * (Real.log (q : ℝ) * sourceSigma (q : ℝ) d)) :
    C145 * claim14_5Scale S H n (q : ℝ) d Δ
        (sourceSigma (q : ℝ) d) K x ≤
      suzukiVProduct S (p : ℝ) *
        (C * Real.exp (Real.sqrt K) * errorEnvelope H n (q : ℝ) d x *
          (Real.log (q : ℝ)) ^ (-Δ)) := by
  have hq1 : (1 : ℝ) < (q : ℝ) := by exact_mod_cast (show 1 < q by omega)
  have hlog : 0 < Real.log (q : ℝ) := Real.log_pos hq1
  have hx0 : 0 < x := by linarith
  have hexp : 1 / x ≤ (1 : ℝ) := (div_le_one hx0).2 (by linarith)
  have hpq : (p : ℝ) ≤ (q : ℝ) := by
    rw [← hpower]
    exact Real.rpow_le_self_of_one_le (by exact_mod_cast (show 1 ≤ q by omega)) hexp
  have hV : claim14_5VProduct S (q : ℝ) ≤ suzukiVProduct S (p : ℝ) := by
    simpa [claim14_5VProduct, suzukiVProduct] using
      suzukiVProduct_mono_antitone S hpq
  have hE : 0 ≤ errorEnvelope H n (q : ℝ) d x :=
    errorEnvelope_nonneg H n hq1 hx0.le
      (hH.positive (ErrorSign.ofDepth n) x hx0).le
  have hL : 0 ≤ (Real.log (q : ℝ)) ^ (-Δ) :=
    Real.rpow_nonneg hlog.le _
  have hden : 0 < Real.log (q : ℝ) * sourceSigma (q : ℝ) d :=
    mul_pos hlog hσ
  have hcoef' : C145 / (Real.log (q : ℝ) * sourceSigma (q : ℝ) d) ≤ C :=
    (div_le_iff₀ hden).2 (by simpa [mul_comm] using hcoef)
  have hcoef0 : 0 ≤ C145 / (Real.log (q : ℝ) * sourceSigma (q : ℝ) d) :=
    div_nonneg hC145 hden.le
  have hcommon : 0 ≤ Real.exp (Real.sqrt K) *
      errorEnvelope H n (q : ℝ) d x * (Real.log (q : ℝ)) ^ (-Δ) := by
    positivity
  unfold claim14_5Scale
  calc
    C145 * (claim14_5VProduct S (q : ℝ) *
        (Real.exp (Real.sqrt K) /
          (Real.log (q : ℝ) * sourceSigma (q : ℝ) d)) *
        errorEnvelope H n (q : ℝ) d x *
        (Real.log (q : ℝ)) ^ (-Δ)) =
      claim14_5VProduct S (q : ℝ) *
        (C145 / (Real.log (q : ℝ) * sourceSigma (q : ℝ) d)) *
        (Real.exp (Real.sqrt K) * errorEnvelope H n (q : ℝ) d x *
          (Real.log (q : ℝ)) ^ (-Δ)) := by ring
    _ ≤ suzukiVProduct S (p : ℝ) * C *
        (Real.exp (Real.sqrt K) * errorEnvelope H n (q : ℝ) d x *
          (Real.log (q : ℝ)) ^ (-Δ)) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul hV hcoef' hcoef0 (suzukiVProduct_pos S (p : ℝ)).le)
        hcommon
    _ = suzukiVProduct S (p : ℝ) *
        (C * Real.exp (Real.sqrt K) * errorEnvelope H n (q : ℝ) d x *
          (Real.log (q : ℝ)) ^ (-Δ)) := by ring


end MathlibNt.SieveTheory
