import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144CaseIIFinalBoundary
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiCaseIISourceSigmaGeometryEventually
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiSection13HatLayersKappaOne

open scoped Classical BigOperators Interval
open Filter Finset MeasureTheory Set Topology

namespace MathlibNt.SieveTheory

open LinearSieve SwitchingPrinciple SuzukiFiniteContinuousLayers
open SwitchingPrinciple.SuzukiLemma144Equation1410
open SwitchingPrinciple.SuzukiLemma144KappaOne

set_option maxHeartbeats 1200000

/-- At depth one the finite continuous source layer is the literal initial
function `(3-s)/s` throughout the low strip. -/
theorem finiteSourceLayer_one_eq_lowStrip {s : ℝ} (hs3 : s ≤ 3) :
    finiteSourceLayer 1 2 1 s = (3 - s) / s := by
  simp [finiteSourceLayer, suzukiLayer, baseLower, dPowDensity,
    intervalIntegral.integral_const]
  norm_num at hs3 ⊢
  rw [min_eq_left hs3]
  rw [div_eq_mul_inv, mul_comm]

/-- The Section 13 plus-hat initial condition at `β=2`, written in the
normalization occurring in the depth-one error envelope. -/
theorem section13Hat_plus_initial_lowStrip
    {H : Section13HatLayers} (hH : Section13HatContract H 2)
    {s : ℝ} (hs : 0 < s) (hs3 : s ≤ 3) :
    H.Tplus s = 1 / s ^ 2 := by
  have hi := hH.initial_plus s hs (by norm_num at hs3 ⊢; exact hs3)
  simp only [weightedHat, Section13HatLayers.T] at hi
  norm_num at hi
  apply (mul_left_cancel₀ (sq_pos_of_pos hs).ne')
  calc
    s ^ 2 * H.Tplus s = 1 := hi
    _ = s ^ 2 * (1 / s ^ 2) := by field_simp

/-- On the low strip the exact hat initial value gives the uniform lower bound
`1/s` for the depth-one production error envelope. -/
theorem one_div_le_errorEnvelope_one_lowStrip
    {H : Section13HatLayers} (hH : Section13HatContract H 2)
    {D d s : ℝ} (hD : 1 < D) (hs : 0 < s) (hs3 : s ≤ 3) :
    1 / s ≤ errorEnvelope H 1 D d s := by
  have hlog : 0 < Real.log D := Real.log_pos hD
  have hbase : 1 ≤ 1 + s ^ d / Real.log D := by
    have hp : 0 ≤ s ^ d / Real.log D :=
      div_nonneg (Real.rpow_nonneg hs.le _) hlog.le
    linarith
  have hrpow : 1 ≤ (1 + s ^ d / Real.log D) ^ s := by
    simpa only [Real.one_rpow] using
      Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hbase hs.le
  rw [errorEnvelope_odd (by decide : Odd 1),
    section13Hat_plus_initial_lowStrip hH hs hs3]
  calc
    1 / s = 1 * (1 / s) := by ring
    _ ≤ (1 + s ^ d / Real.log D) ^ s * (1 / s) :=
      mul_le_mul_of_nonneg_right hrpow (by positivity)
    _ = (1 + s ^ d / Real.log D) ^ s * s * (1 / s ^ 2) := by
      field_simp [hs.ne']

/-- A completely explicit eventual comparison of the local depth-one remainder
with the same fixed `C` error budget.  The threshold is chosen before `s`, so
this is uniform on `1 < s ≤ 3`. -/
theorem exists_baseOne_localError_sameC_threshold
    {H : Section13HatLayers} (hH : Section13HatContract H 2)
    {d Δ C K : ℝ} (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1)
    (hC : 0 < C) (hK : 2 ≤ K) :
    ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ D : ℝ, D₀ ≤ D →
      ∀ s : ℝ, 1 < s → s ≤ 3 →
        9 * K / (s * Real.log D) ≤
          C * Real.exp (Real.sqrt K) * errorEnvelope H 1 D d s *
            (Real.log D) ^ (-Δ) := by
  let gap : ℝ := 1 - Δ
  have hgap : 0 < gap := by dsimp [gap]; linarith
  let A : ℝ := 9 * K / (C * Real.exp (Real.sqrt K))
  have hK0 : 0 < K := lt_of_lt_of_le (by norm_num) hK
  have hA : 0 < A := by dsimp [A]; positivity
  let X : ℝ := max 3 (A ^ (1 / gap))
  have hX3 : 3 ≤ X := le_max_left _ _
  have hX0 : 0 < X := by linarith
  refine ⟨Real.exp X, Real.one_lt_exp_iff.mpr hX0, ?_⟩
  intro D hDX s hs hs3
  have hDpos : 0 < D := (Real.exp_pos X).trans_le hDX
  have hlogX : X ≤ Real.log D := (Real.le_log_iff_exp_le hDpos).2 hDX
  have hlog3 : 3 ≤ Real.log D := hX3.trans hlogX
  have hlog : 0 < Real.log D := by linarith
  have hroot : A ^ (1 / gap) ≤ Real.log D :=
    (le_max_right (3 : ℝ) (A ^ (1 / gap))).trans hlogX
  have hApow : A ≤ (Real.log D) ^ gap := by
    have hh := Real.rpow_le_rpow (Real.rpow_nonneg hA.le _) hroot hgap.le
    have heq : (A ^ (1 / gap)) ^ gap = A := by
      rw [← Real.rpow_mul hA.le]
      have : (1 / gap) * gap = 1 := by field_simp
      rw [this, Real.rpow_one]
    simpa only [heq] using hh
  have hD1 : 1 < D := (Real.one_lt_exp_iff.mpr hX0).trans_le hDX
  have hE : 1 / s ≤ errorEnvelope H 1 D d s :=
    one_div_le_errorEnvelope_one_lowStrip hH hD1 (zero_lt_one.trans hs) hs3
  have hcoef : 9 * K ≤ C * Real.exp (Real.sqrt K) * (Real.log D) ^ gap := by
    have hm := mul_le_mul_of_nonneg_left hApow
      (show 0 ≤ C * Real.exp (Real.sqrt K) by positivity)
    dsimp [A] at hm
    field_simp at hm
    exact hm
  have hsmall :
      9 * K / (s * Real.log D) ≤
        C * Real.exp (Real.sqrt K) * (1 / s) * (Real.log D) ^ (-Δ) := by
    have hlogpow : (Real.log D) ^ gap =
        (Real.log D) ^ (-Δ) * Real.log D := by
      calc
        (Real.log D) ^ gap = (Real.log D) ^ (-Δ + 1) := by
          congr 1
          dsimp [gap]
          ring
        _ = (Real.log D) ^ (-Δ) * (Real.log D) ^ (1 : ℝ) :=
          Real.rpow_add hlog (-Δ) 1
        _ = (Real.log D) ^ (-Δ) * Real.log D := by
          rw [Real.rpow_one]
    rw [div_le_iff₀ (mul_pos (zero_lt_one.trans hs) hlog)]
    calc
      9 * K ≤ C * Real.exp (Real.sqrt K) * (Real.log D) ^ gap := hcoef
      _ = (C * Real.exp (Real.sqrt K) * (1 / s) *
          (Real.log D) ^ (-Δ)) * (s * Real.log D) := by
        rw [hlogpow]
        field_simp [ne_of_gt (zero_lt_one.trans hs)]
  refine hsmall.trans ?_
  have hfac : 0 ≤ C * Real.exp (Real.sqrt K) :=
    mul_nonneg hC.le (Real.exp_pos _).le
  have hp : 0 ≤ (Real.log D) ^ (-Δ) := Real.rpow_nonneg hlog.le _
  calc
    C * Real.exp (Real.sqrt K) * (1 / s) * (Real.log D) ^ (-Δ) ≤
        C * Real.exp (Real.sqrt K) * errorEnvelope H 1 D d s *
          (Real.log D) ^ (-Δ) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hE hfac) hp

/-- The Euler product multiplying both base-one brackets is nonnegative. -/
theorem suzukiVProduct_nonneg (S : BoundingSieve) (x : ℝ) :
    0 ≤ suzukiVProduct S x := by
  exact (suzukiVProduct_pos S x).le

/-- `log D ≥ 3` is a uniform root threshold for every `1 < s ≤ 3`. -/
theorem two_le_rpow_inv_lowStrip
    {D s : ℝ} (hD : 0 < D) (hlog3 : 3 ≤ Real.log D)
    (hs : 1 < s) (hs3 : s ≤ 3) :
    2 ≤ D ^ (1 / s) := by
  have hs0 : 0 < s := zero_lt_one.trans hs
  have hsexp : 1 ≤ Real.log D * (1 / s) := by
    rw [one_div, ← div_eq_mul_inv, le_div_iff₀ hs0]
    simpa only [one_mul] using hs3.trans hlog3
  rw [Real.rpow_def_of_pos hD]
  have h2exp : (2 : ℝ) ≤ Real.exp 1 := by
    nlinarith [Real.add_one_lt_exp (by norm_num : (1 : ℝ) ≠ 0)]
  exact h2exp.trans (Real.exp_le_exp.mpr hsexp)

/-- Actual Case-II `N=1` closure with one fixed `C`.  A single threshold is
chosen before the low-strip parameter `s`; it simultaneously enforces the
source value `3 ≤ sourceSigma D d`, the natural-ceiling base geometry, and the
uniform absorption of `9K/(s log D)`. -/
theorem lemma14_4_caseII_base_one_sameC_uniform
    {S : BoundingSieve} {H : Section13HatLayers}
    (hH : Section13HatContract H 2)
    {d Δ C K : ℝ} (hd : 0 < d) (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1)
    (hC : 0 < C) (hK : 2 ≤ K)
    (hlocal : HasDimensionOneLocalProductBound S K) :
    ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ D : ℕ, D₀ ≤ (D : ℝ) →
      3 ≤ sourceSigma (D : ℝ) d ∧
      ∀ s : ℝ, 1 < s → s ≤ 3 →
        Lemma144CaseIISameCAt S H 1 D d Δ C K s := by
  obtain ⟨DE, hDE1, hDE⟩ :=
    exists_baseOne_localError_sameC_threshold (d := d) hH hΔ0 hΔ1 hC hK
  obtain ⟨Dσ, hDσ1, hDσ⟩ :=
    exists_sourceSigma_three_threshold d hd
  let D₀ : ℝ := max DE (max Dσ (Real.exp 3))
  have hD₀1 : 1 < D₀ :=
    hDE1.trans_le (le_max_left DE (max Dσ (Real.exp 3)))
  refine ⟨D₀, hD₀1, ?_⟩
  intro D hD
  have hDE' : DE ≤ (D : ℝ) :=
    (le_max_left DE (max Dσ (Real.exp 3))).trans hD
  have htail : max Dσ (Real.exp 3) ≤ (D : ℝ) :=
    (le_max_right DE (max Dσ (Real.exp 3))).trans hD
  have hDσ' : Dσ ≤ (D : ℝ) := (le_max_left Dσ (Real.exp 3)).trans htail
  have hexp3 : Real.exp 3 ≤ (D : ℝ) :=
    (le_max_right Dσ (Real.exp 3)).trans htail
  have hDpos : 0 < (D : ℝ) := (Real.exp_pos 3).trans_le hexp3
  have hlog3 : 3 ≤ Real.log (D : ℝ) :=
    (Real.le_log_iff_exp_le hDpos).2 hexp3
  have hD1 : 1 < (D : ℝ) := by
    have : 1 < Real.exp (3 : ℝ) := Real.one_lt_exp_iff.mpr (by norm_num)
    exact this.trans_le hexp3
  have hsigmaC2 : 3 ≤ sourceSigma (D : ℝ) d :=
    hDσ (D : ℝ) hDσ'
  have hsigma : 3 ≤ sourceSigma (D : ℝ) d := by
    simpa [sourceSigma, sourceSigma] using hsigmaC2
  refine ⟨hsigma, ?_⟩
  intro s hs hs3
  let z : ℕ := ⌈(D : ℝ) ^ (1 / s)⌉₊
  have hs0 : 0 < s := zero_lt_one.trans hs
  have hdom : s ∈ suzukiParityDomainOne 2 1 := by
    simp [suzukiParityDomainOne, KappaOneModel.parityDomain]
    norm_num
    exact hs
  have hroot : 2 ≤ (D : ℝ) ^ (1 / s) :=
    two_le_rpow_inv_lowStrip hDpos hlog3 hs hs3
  have hbase := lemma14_4_base_one_natCeil
    (S := S) (D := D) (z := z) (s := s) (K := K)
    rfl hD1 hdom hs3 hroot (le_trans (by norm_num) hK) hlocal
  have habs := hDE (D : ℝ) hDE' s hs hs3
  have hV : 0 ≤ suzukiVProduct S (z : ℝ) := suzukiVProduct_nonneg S z
  have hcarrier :
      (Finset.Icc 1 1).filter (fun n => n % 2 = 1 % 2) = {1} := by
    ext n
    simp
    omega
  dsimp [Lemma144CaseIISameCAt]
  calc
    ∑ n ∈ (Finset.Icc 1 1).filter (fun n => n % 2 = 1 % 2),
        suzukiSourceV S n D z = suzukiSourceV S 1 D z := by
      rw [hcarrier, Finset.sum_singleton]
    _ ≤ suzukiVProduct S (z : ℝ) *
        (finiteSourceLayer 1 2 1 s + 9 * K / (s * Real.log (D : ℝ))) := hbase
    _ ≤ suzukiVProduct S (z : ℝ) *
        (finiteSourceLayer 1 2 1 s +
          C * Real.exp (Real.sqrt K) * errorEnvelope H 1 (D : ℝ) d s *
            (Real.log (D : ℝ)) ^ (-Δ)) :=
      mul_le_mul_of_nonneg_left (add_le_add (le_refl _) habs) hV

/-- The exact producer requested by the Case-II dispatcher, now discharged
from source data.  It is a specialization of the stronger threshold-before-`s`
uniform theorem above and therefore uses the identical constant `C`. -/
theorem lemma14_4_caseII_base_one_sameC_producer
    {S : BoundingSieve} {H : Section13HatLayers}
    (hH : Section13HatContract H 2)
    {d Δ C K s : ℝ} (hd : 0 < d) (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1)
    (hC : 0 < C) (hK : 2 ≤ K)
    (hlocal : HasDimensionOneLocalProductBound S K)
    (hs : 1 < s) (hs3 : s ≤ 3) :
    Lemma144CaseIIBaseOneSameCProducer S H d Δ C K s := by
  obtain ⟨D₀, hD₀, hmain⟩ :=
    lemma14_4_caseII_base_one_sameC_uniform hH hd hΔ0 hΔ1 hC hK hlocal
  refine ⟨D₀, hD₀, ?_⟩
  intro D hD
  have h := hmain D hD
  refine ⟨h.1, ?_⟩
  intro _hbase
  exact h.2 s hs hs3


end MathlibNt.SieveTheory
