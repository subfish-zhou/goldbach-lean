import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144CaseIIBaseOneSameC
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144ActualRecurrenceStrictCeil
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144FiniteInductionFinal

open scoped Classical BigOperators Interval
open Filter Finset MeasureTheory Set Topology

namespace MathlibNt.SieveTheory

open LinearSieve SwitchingPrinciple SuzukiFiniteContinuousLayers
open SwitchingPrinciple.SuzukiLemma144Equation1410
open SwitchingPrinciple.SuzukiLemma144KappaOne

set_option maxHeartbeats 1200000

/-- Above the initial strip, the depth-one continuous source layer vanishes. -/
theorem finiteSourceLayer_one_eq_zero_of_three_le
    {s : ℝ} (hs3 : 3 ≤ s) :
    finiteSourceLayer 1 2 1 s = 0 := by
  simp [finiteSourceLayer, suzukiLayer, baseLower, dPowDensity,
    intervalIntegral.integral_const]
  norm_num at hs3 ⊢
  rw [min_eq_right hs3]
  ring
  exact Or.inr trivial

/-- At a power cutoff with exponent strictly above three, the actual depth-one
source is empty: every natural below the cutoff has cube strictly below `D`. -/
theorem suzukiActualT_one_natCeil_eq_zero_of_three_lt
    (S : BoundingSieve) {D : ℕ} {s : ℝ}
    (hD : 1 ≤ D) (hs3 : 3 < s) :
    suzukiActualT S 1 D ⌈(D : ℝ) ^ (1 / s)⌉₊ = 0 := by
  rw [suzukiActualT_one]
  apply suzukiSourceV_one_eq_zero_of_cube_lt_below
  intro p hp
  have hDreal : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD
  have hs0 : 0 < (3 : ℝ) := by norm_num
  have hcut : (D : ℝ) ^ (1 / s) ≤ (D : ℝ) ^ (1 / 3 : ℝ) :=
    rpow_one_div_mono_of_le hDreal hs0 hs3.le
  have hroot0 : 0 < (D : ℝ) ^ (1 / s) := by positivity
  have hpRoot : (p : ℝ) < (D : ℝ) ^ (1 / s) := by
    rw [← Nat.lt_ceil]
    exact hp
  have hpCubeRoot : (p : ℝ) < (D : ℝ) ^ (1 / 3 : ℝ) :=
    hpRoot.trans_le hcut
  by_cases hp0 : p = 0
  · subst p
    simp
    omega
  have hpReal0 : 0 < (p : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hp0)
  have hDpos : 0 < (D : ℝ) := lt_of_lt_of_le zero_lt_one hDreal
  have hr := Real.lt_rpow_inv_iff_of_pos
    (x := (p : ℝ)) (y := (D : ℝ)) (z := (3 : ℝ))
    hpReal0.le hDpos.le (by norm_num)
  norm_num [one_div] at hr
  have hpCubeReal : (p : ℝ) ^ (3 : ℕ) < (D : ℝ) := hr.mp hpCubeRoot
  exact_mod_cast hpCubeReal

/-- The complete depth-one Lemma 14.4 base with one cutoff before every
coordinate.  The low strip uses the source-native rounded base estimate and a
uniform absorption threshold; above `3`, both the actual source and the finite
continuous source layer vanish identically. -/
theorem lemma14_4_base_one_full_uniform
    {S : BoundingSieve} {H : Section13HatLayers}
    (hH : Section13HatContract H 2)
    {d Δ C K : ℝ} (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1)
    (hC : 0 < C) (hK : 2 ≤ K)
    (hlocal : HasDimensionOneLocalProductBound S K) :
    ∃ Dmin : ℕ, 2 ≤ Dmin ∧
      Lemma144UniformNatCeilAt S H C K d Δ 1 Dmin := by
  obtain ⟨DE, hDE1, hDE⟩ :=
    exists_baseOne_localError_sameC_threshold (d := d) hH hΔ0 hΔ1 hC hK
  obtain ⟨n, hn⟩ := exists_nat_ge (max DE (Real.exp 3))
  let Dmin : ℕ := max 2 n
  refine ⟨Dmin, le_max_left _ _, ?_⟩
  intro D hDmin hD2 x hx hz2
  have hnD : n ≤ D := (le_max_right 2 n).trans hDmin
  have htail : max DE (Real.exp 3) ≤ (D : ℝ) := hn.trans (by exact_mod_cast hnD)
  have hDE' : DE ≤ (D : ℝ) := (le_max_left _ _).trans htail
  have hexp3 : Real.exp 3 ≤ (D : ℝ) := (le_max_right _ _).trans htail
  have hDpos : 0 < (D : ℝ) := (Real.exp_pos 3).trans_le hexp3
  have hD1 : 1 < (D : ℝ) :=
    (Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 3)).trans_le hexp3
  have hlog3 : 3 ≤ Real.log (D : ℝ) :=
    (Real.le_log_iff_exp_le hDpos).2 hexp3
  have hx1 : 1 < x := by
    have hx' : (2 : ℝ) - 1 < x := by
      simpa [KappaOneModel.parityDomain] using hx
    norm_num at hx' ⊢
    exact hx'
  have hx0 : 0 < x := zero_lt_one.trans hx1
  by_cases hx3 : x ≤ 3
  · have hroot : 2 ≤ (D : ℝ) ^ (1 / x) :=
      two_le_rpow_inv_lowStrip hDpos hlog3 hx1 hx3
    have hdom : x ∈ suzukiParityDomainOne 2 1 := by
      simpa [suzukiParityDomainOne] using hx
    have hbase := lemma14_4_base_one_natCeil
      (S := S) (D := D) (z := ⌈(D : ℝ) ^ (1 / x)⌉₊)
      (s := x) (K := K) rfl hD1 hdom hx3 hroot
      (le_trans (by norm_num) hK) hlocal
    have habs := hDE (D : ℝ) hDE' x hx1 hx3
    have hV := suzukiVProduct_nonneg S
      (⌈(D : ℝ) ^ (1 / x)⌉₊ : ℝ)
    rw [suzukiActualT_one]
    exact hbase.trans (mul_le_mul_of_nonneg_left
      (add_le_add le_rfl habs) hV)
  · have hx3' : 3 < x := lt_of_not_ge hx3
    rw [suzukiActualT_one_natCeil_eq_zero_of_three_lt S (by omega) hx3']
    rw [finiteSourceLayer_one_eq_zero_of_three_le hx3'.le, zero_add]
    have hT : 0 ≤ H.T (ErrorSign.ofDepth 1) x :=
      (hH.positive _ x hx0).le
    have hE : 0 ≤ errorEnvelope H 1 (D : ℝ) d x :=
      errorEnvelope_nonneg H 1 hD1 hx0.le hT
    have hlog : 0 < Real.log (D : ℝ) := Real.log_pos hD1
    have hErr : 0 ≤ C * Real.exp (Real.sqrt K) *
        errorEnvelope H 1 (D : ℝ) d x * (Real.log (D : ℝ)) ^ (-Δ) := by
      positivity
    exact mul_nonneg (suzukiVProduct_nonneg S _) hErr


end MathlibNt.SieveTheory
