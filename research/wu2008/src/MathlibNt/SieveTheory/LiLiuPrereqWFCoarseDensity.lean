import MathlibNt.SieveTheory.LiLiuPrereqWFCoarseDensitySource
import MathlibNt.SieveTheory.LiLiuPrereqWFProducerBridge
import MathlibNt.SieveTheory.LiLiuPrereqWFRoughComparison

/-!
# The same ordinary rough density, with the genuine global F/f factors

The real level is transported exactly to its natural ceiling; the coordinate
is correspondingly `log (ceil D) / log z`. Monotonicity of the genuine JR
functions then returns to `log D / log z` in the favorable directions.
The moving-range power budget is retained explicitly in this module.
-/

namespace MathlibNt.SieveTheory.LiLiuPrereqWF.CoarseDensity

open ArithmeticFunction Finset SmallRosser SwitchingPrinciple
open SuzukiFiniteContinuousLayers SwitchingPrinciple.SuzukiLemma144KappaOne
open JurkatRichert1965ChenGammaOneQOne
open scoped Classical

theorem roughOrdinaryDensity_lower (D : ℝ) (B : Finset ℕ) (g : ℕ → ℝ) :
    roughOrdinaryDensity false D B g = lowerSetDensity D g B := by
  simp only [roughOrdinaryDensity, ordinaryRoughSet, Bool.false_eq_true,
    if_false, lowerSetDensity]

theorem roughOrdinaryDensity_upper (D : ℝ) (B : Finset ℕ) (g : ℕ → ℝ) :
    roughOrdinaryDensity true D B g = upperSetDensity D g B := by
  simp only [roughOrdinaryDensity, ordinaryRoughSet, if_true, upperSetDensity]

theorem exp_sqrt_max_two_le_target {K : ℝ} (hK : 0 ≤ K) :
    Real.exp (Real.sqrt (max K 2)) ≤ Real.exp (6 * K + 2) := by
  apply Real.exp_le_exp.mpr
  apply (Real.sqrt_le_iff).mpr
  refine ⟨by positivity, ?_⟩
  apply max_le <;> nlinarith [sq_nonneg K]

/-- The local product hypothesis descends to a subcarrier with the SAME `K`.
Zero deletion is handled separately by the existing actual density sieve. -/
theorem dimensionOneProductBound_subset {P B : Finset ℕ} {g : ℕ → ℝ} {K : ℝ}
    (hBP : B ⊆ P) (hg : ∀ p ∈ P, 0 ≤ g p ∧ g p < 1)
    (hdim : DimensionOneProductBound P g K) :
    DimensionOneProductBound B g K := by
  intro w z hw hwz
  apply le_trans _ (hdim w z hw hwz)
  apply prod_le_prod_of_subset_of_one_le (Finset.filter_subset_filter _ hBP)
  · intro p hp
    exact inv_nonneg.mpr (sub_nonneg.mpr (hg p (hBP (mem_filter.mp hp).1)).2.le)
  · intro p hp _
    have hgp := hg p (mem_filter.mp hp).1
    apply (one_le_inv₀ (sub_pos.mpr hgp.2)).mpr
    linarith [hgp.1]

/-- Uniform in the entire finite carrier, including its adaptive exhaustive
depth. Only the error envelope is exponentially bounded, never the main
continuous source mass. -/
theorem exists_roughOrdinaryDensity_ff_of_powerBudget :
    ∃ C : ℝ, 0 < C ∧
      ∀ (B : Finset ℕ) (_hB : ∀ p ∈ B, p.Prime)
        (g : ArithmeticFunction ℝ) (_hgm : g.IsMultiplicative),
        (∀ p ∈ B, 0 ≤ g p ∧ g p < 1) →
        ∀ D z K : ℝ, 1 < D → 1 < z → z ≤ D →
          (∀ p ∈ B, (p : ℝ) < z) →
          0 ≤ K → DimensionOneProductBound B g K →
          2 ≤ Real.log D / Real.log z →
          (roundedSieveCoordinate D z) ^ 13 ≤ Real.log (⌈D⌉₊ : ℝ) →
          Real.exp 1 ≤ Real.log (⌈D⌉₊ : ℝ) →
          let V := ∏ p ∈ B, (1 - g p)
          let E := C * Real.exp (6 * K + 2) * (Real.log D) ^ (-(1 / 3 : ℝ))
          V * (jr1965f (Real.log D / Real.log z) - E) ≤
              roughOrdinaryDensity false D B g ∧
          roughOrdinaryDensity true D B g ≤
              V * (jr1965F (Real.log D / Real.log z) + E) := by
  obtain ⟨Cmin, _hmin, hsource⟩ :=
    exists_lemma14_4_movingRange_rounded_allDepth_uniform_in_S_of_source
      jr1965Section13HatLayers jr1965Section13HatSourceContract
      sourceParameters_twelve_third_five
  obtain ⟨_C145, _Clow, C, _h145, _hlow, hC, hsource⟩ := hsource Cmin le_rfl
  let A := C * Real.exp 1 * jrHatDecayConstant
  have hC0 : 0 ≤ C := by linarith
  have hdecay0 : 0 ≤ jrHatDecayConstant := jrHatDecayConstant_pos.le
  have hA0 : 0 ≤ A := mul_nonneg (mul_nonneg hC0 (Real.exp_pos 1).le) hdecay0
  refine ⟨A, mul_pos (mul_pos (by linarith) (Real.exp_pos 1))
    jrHatDecayConstant_pos, ?_⟩
  intro B hB g hgm hg D z K hD hz hzD hcut hK hdim hs hbudget hlog
  let S := densityBoundingSieve B hB g hgm hg
  let T := nonzeroDensityPrimes B g
  let s := roundedSieveCoordinate D z
  let r := ⌈D⌉₊
  let V := ∏ p ∈ B, (1 - g p)
  let E := A * Real.exp (6 * K + 2) * (Real.log D) ^ (-(1 / 3 : ℝ))
  have hr : 2 ≤ r := by
    have : 1 < r := Nat.lt_ceil.mpr (by simpa using hD)
    omega
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have hlogD : 0 < Real.log D := Real.log_pos hD
  have hlogz : 0 < Real.log z := Real.log_pos hz
  have hlogs : Real.log D ≤ Real.log (r : ℝ) :=
    Real.log_le_log (by linarith) (Nat.le_ceil D)
  have hss : Real.log D / Real.log z ≤ s :=
    div_le_div_of_nonneg_right hlogs hlogz.le
  have hs2 : 2 ≤ s := hs.trans hss
  have hroot : (r : ℝ) ^ (1 / s) = z := roundedSieveCoordinate_cutoff hD hz
  have hzceil : 2 ≤ ⌈(r : ℝ) ^ (1 / s)⌉₊ := by
    rw [hroot]
    have : 1 < ⌈z⌉₊ := Nat.lt_ceil.mpr (by simpa using hz)
    omega
  have hlocal : HasDimensionOneLocalProductBound S (max K 2) :=
    densityBoundingSieve_hasDimensionOneLocalProductBound B hB g hgm hg
      (hK.trans (le_max_left _ _))
      (dimensionOneProductBound_mono hdim (le_max_left _ _))
  have hV : suzukiVProduct S (⌈z⌉₊ : ℝ) = V :=
    densityBoundingSieve_suzukiVProduct B hB g hgm hg hcut
  have hV0 : 0 ≤ V := prod_nonneg (fun p hp => sub_nonneg.mpr (hg p hp).2.le)
  have hsSigma : s ≤ sourceSigma (r : ℝ) 12 :=
    moving_range_of_power_budget hr0 (by linarith) hbudget hlog
  have herror (N : ℕ) :
      C * Real.exp (Real.sqrt (max K 2)) *
          errorEnvelope jr1965Section13HatLayers N (r : ℝ) 12 s *
          (Real.log (r : ℝ)) ^ (-(1 / 3 : ℝ)) ≤ E := by
    have henv := jr_errorEnvelope_le_exp N hs2 hbudget
    have hdec : Real.exp (-s) ≤ 1 := by
      simpa using Real.exp_le_exp.mpr (show -s ≤ 0 by linarith)
    have hhat : errorEnvelope jr1965Section13HatLayers N (r : ℝ) 12 s ≤
        Real.exp 1 * jrHatDecayConstant := by
      apply henv.trans
      exact mul_le_mul_of_nonneg_left
        (by nlinarith [jrHatDecayConstant_pos]) (Real.exp_pos 1).le
    have hpow : (Real.log (r : ℝ)) ^ (-(1 / 3 : ℝ)) ≤
        (Real.log D) ^ (-(1 / 3 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hlogD hlogs (by norm_num)
    calc
      _ ≤ C * Real.exp (Real.sqrt (max K 2)) *
          (Real.exp 1 * jrHatDecayConstant) *
          (Real.log D) ^ (-(1 / 3 : ℝ)) := by
        apply mul_le_mul
          (mul_le_mul_of_nonneg_left hhat (mul_nonneg hC0 (Real.exp_pos _).le))
          hpow (Real.rpow_nonneg (hlogD.le.trans hlogs) _) (by positivity)
      _ = A * Real.exp (Real.sqrt (max K 2)) *
          (Real.log D) ^ (-(1 / 3 : ℝ)) := by dsimp [A]; ring
      _ ≤ E := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (exp_sqrt_max_two_le_target hK) hA0)
        (Real.rpow_nonneg hlogD.le _)
  have hbound (N : ℕ) (hN : 1 ≤ N) :
      suzukiActualT S N r ⌈z⌉₊ ≤ V * (finiteSourceLayer 1 2 N s + E) := by
    have hdom : s ∈ KappaOneModel.parityDomain 2 N := by
      unfold KappaOneModel.parityDomain
      split_ifs <;> simp only [Set.mem_Ioi, Set.mem_Ici] <;> linarith
    have h := hsource S (max K 2) (le_max_right _ _) hlocal N hN r hr hr
      s hdom hsSigma hzceil
    rw [hroot, hV] at h
    exact h.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl (herror N)) hV0)
  have hlow := hbound (2 * (T.card + 1)) (by omega)
  have hupp := hbound (2 * T.card + 1) (by omega)
  have hlowMass := finiteSourceLayer_even_le_one_sub_jr1965f (T.card + 1) hs2
  have huppMass := finiteSourceLayer_odd_le_jr1965F_sub_one T.card hs2
  have hlow' := hlow.trans
    (mul_le_mul_of_nonneg_left (add_le_add hlowMass (le_refl E)) hV0)
  have hupp' := hupp.trans
    (mul_le_mul_of_nonneg_left (add_le_add huppMass (le_refl E)) hV0)
  have hmonoF := antitoneOn_jr1965F
    (show 0 < Real.log D / Real.log z by linarith)
    (show 0 < s by linarith) hss
  have hmonof := monotoneOn_jr1965f
    (show 0 < Real.log D / Real.log z by linarith)
    (show 0 < s by linarith) hss
  have hmonoFV := mul_le_mul_of_nonneg_left hmonoF hV0
  have hmonofV := mul_le_mul_of_nonneg_left hmonof hV0
  have hid := densityBoundingSieve_actual_densities B hB g hgm hg hD hzD hcut
  dsimp only at hid ⊢
  rw [roughOrdinaryDensity_lower, roughOrdinaryDensity_upper, hid.1, hid.2]
  change V * (jr1965f (Real.log D / Real.log z) - E) ≤
      V - suzukiActualT S (2 * (T.card + 1)) r ⌈z⌉₊ ∧
    V + suzukiActualT S (2 * T.card + 1) r ⌈z⌉₊ ≤
      V * (jr1965F (Real.log D / Real.log z) + E)
  constructor <;> nlinarith

#check exists_roughOrdinaryDensity_ff_of_powerBudget
#print axioms dimensionOneProductBound_subset
#print axioms exists_roughOrdinaryDensity_ff_of_powerBudget

end MathlibNt.SieveTheory.LiLiuPrereqWF.CoarseDensity
