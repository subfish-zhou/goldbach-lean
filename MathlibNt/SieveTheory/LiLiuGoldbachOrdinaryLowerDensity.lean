import MathlibNt.SieveTheory.LiLiuGoldbachOrdinaryLowerDensityFactors
import MathlibNt.SieveTheory.SuzukiLemma147JurkatRichertInterval
import MathlibNt.SieveTheory.SuzukiDensityBoundingSieveBridge

set_option autoImplicit false
set_option warningAsError true

namespace MathlibNt.SieveTheory

open LinearSieve SwitchingPrinciple SuzukiFiniteContinuousLayers
open SwitchingPrinciple.SuzukiLemma144KappaOne
open JurkatRichert1965ChenGammaOneQOne LiLiuPrereqWF.SmallRosser

/-- A single positive constant works for every sieve, local-product constant,
integer level and real cutoff. The coefficient is the original lower Rosser
weight; neither a source contract nor a density estimate is a premise. -/
theorem exists_actual_lowerRosser_jr_powerBudget :
    ∃ A : ℝ, 0 < A ∧ ∀ (S : BoundingSieve) (K : ℝ),
      2 ≤ K → HasDimensionOneLocalProductBound S K →
      ∀ (D : ℕ) (z : ℝ), 2 ≤ D → 1 < z →
      (∀ p ∈ S.prodPrimes.primeFactors, (p : ℝ) < z) →
      let t := Real.log (D : ℝ) / Real.log z
      2 ≤ t → t ^ 13 ≤ Real.log (D : ℝ) →
      Real.exp 1 ≤ Real.log (D : ℝ) →
      AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S *
        (jr1965f t - A * Real.exp (Real.sqrt K) *
          (Real.log (D : ℝ)) ^ (-(1 / 3 : ℝ))) ≤
      S.mainSum (lowerRosserWeight S.prodPrimes D) := by
  obtain ⟨Cmin, _hmin, hsource⟩ :=
    exists_lowerRosserDensity_continuousLowerFactor_of_suzuki_literal_allDepth_uniform_in_S_of_source
      jr1965Section13HatLayers jr1965Section13HatSourceContract
      sourceParameters_twelve_third_five
  obtain ⟨_C145, _Clow, C, _h145, _hlow, hC, hsource⟩ := hsource Cmin le_rfl
  refine ⟨C * Real.exp 1 * jrHatDecayConstant,
    mul_pos (mul_pos (by linarith) (Real.exp_pos 1)) jrHatDecayConstant_pos, ?_⟩
  intro S K hK hlocal D z hD hz hprimes t ht hbudget hlog
  have hD1 : (1 : ℝ) < D := by exact_mod_cast (by omega : 1 < D)
  have hD0 : (0 : ℝ) < D := by linarith
  have hz0 : 0 < z := by linarith
  have hlogD : 0 < Real.log (D : ℝ) := Real.log_pos hD1
  have hlogz : 0 < Real.log z := Real.log_pos hz
  have ht0 : 0 < t := by linarith
  have hroot : (D : ℝ) ^ (1 / t) = z := by
    rw [Real.rpow_def_of_pos hD0]
    have he : Real.log (D : ℝ) * (1 / t) = Real.log z := by
      dsimp [t]
      field_simp
    rw [he, Real.exp_log hz0]
  have hzD : z ≤ (D : ℝ) := by
    apply (Real.log_le_log_iff hz0 hD0).mp
    have hmul : 2 * Real.log z ≤ Real.log (D : ℝ) :=
      (le_div_iff₀ hlogz).mp ht
    linarith
  have hceil : 2 ≤ ⌈(D : ℝ) ^ (1 / t)⌉₊ := by
    rw [hroot]
    have hc : 1 < ⌈z⌉₊ := Nat.lt_ceil.mpr (by exact_mod_cast hz)
    omega
  have hcut : ∀ p ∈ S.prodPrimes.primeFactors,
      p < ⌈(D : ℝ) ^ (1 / t)⌉₊ := by
    intro p hp
    rw [hroot]
    exact Nat.lt_ceil.mpr (hprimes p hp)
  have hlevel : ∀ p ∈ S.prodPrimes.primeFactors, p < D := by
    intro p hp
    exact_mod_cast (hprimes p hp).trans_le hzD
  have hsigma : t ≤ sourceSigma (D : ℝ) 12 :=
    moving_range_of_power_budget hD0 (by linarith) hbudget hlog
  have hraw := hsource S K hK hlocal D hD t ht hsigma hceil
  dsimp only at hraw
  rw [continuousLowerFactor_eq_jr1965f ht] at hraw
  let n := 2 * ((suzukiSupportedBelow S ⌈(D : ℝ) ^ (1 / t)⌉₊).card + 1)
  have henv : errorEnvelope jr1965Section13HatLayers n (D : ℝ) 12 t ≤
      Real.exp 1 * jrHatDecayConstant := by
    apply (jr_errorEnvelope_le_exp n ht hbudget).trans
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos 1).le
    calc
      jrHatDecayConstant * Real.exp (-t) ≤ jrHatDecayConstant * 1 :=
        mul_le_mul_of_nonneg_left
          (Real.exp_le_one_iff.mpr (by linarith)) jrHatDecayConstant_pos.le
      _ = jrHatDecayConstant := mul_one _
  have herr : C * Real.exp (Real.sqrt K) *
      errorEnvelope jr1965Section13HatLayers n (D : ℝ) 12 t *
      (Real.log (D : ℝ)) ^ (-(1 / 3 : ℝ)) ≤
      (C * Real.exp 1 * jrHatDecayConstant) * Real.exp (Real.sqrt K) *
      (Real.log (D : ℝ)) ^ (-(1 / 3 : ℝ)) := by
    calc
      _ ≤ C * Real.exp (Real.sqrt K) * (Real.exp 1 * jrHatDecayConstant) *
          (Real.log (D : ℝ)) ^ (-(1 / 3 : ℝ)) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left henv
            (mul_nonneg (by linarith) (Real.exp_pos _).le))
          (Real.rpow_nonneg hlogD.le _)
      _ = _ := by ring
  obtain ⟨hmain, hEuler, _hcert⟩ :=
    suzukiDensityProduct_lowerRosserWeight_exact_bridge S D
      ⌈(D : ℝ) ^ (1 / t)⌉₊ hcut hlevel
  rw [hmain, ← hEuler]
  exact (mul_le_mul_of_nonneg_left (sub_le_sub_left herr (jr1965f t))
    (suzukiVProduct_nonneg S _)).trans hraw

end MathlibNt.SieveTheory
