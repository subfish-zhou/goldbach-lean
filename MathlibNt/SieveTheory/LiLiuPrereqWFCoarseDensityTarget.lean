import MathlibNt.SieveTheory.LiLiuPrereqWFCoarseDensity

/-!
# Large-D genuine F/f density for the actual geometric rough carrier

The threshold is chosen before the cutoff, prime set, density, and product
constant. The moving range follows from `z ≥ D^(ε²)` and an explicit power
budget. When `z < D^(ε²)`, the actual rough carrier is empty instead.
-/

namespace MathlibNt.SieveTheory.LiLiuPrereqWF.CoarseDensity

open ArithmeticFunction Finset SmallRosser
open JurkatRichert1965ChenGammaOneQOne
open scoped Classical

theorem coarseCoordinate_sqrt_bounds {D z : ℝ} (hD : 2 ≤ D)
    (hz : 2 ≤ z) (hzD : z ≤ Real.sqrt D) :
    z ≤ D ∧ 2 ≤ Real.log D / Real.log z := by
  have hsqrt : (Real.sqrt D) ^ 2 = D := Real.sq_sqrt (by linarith)
  have hsqrt0 : 0 ≤ Real.sqrt D := Real.sqrt_nonneg D
  have hsq : z ^ 2 ≤ D := by nlinarith
  have hlog : Real.log (z ^ 2) ≤ Real.log D :=
    Real.log_le_log (by positivity) hsq
  rw [Real.log_pow] at hlog
  norm_num at hlog
  refine ⟨by nlinarith, ?_⟩
  exact (le_div_iff₀ (Real.log_pos (by linarith : 1 < z))).mpr hlog

/-- No dependence on the carrier or `K` occurs in this rounded moving-range
budget. The power `13` is the actual source/envelope budget, not a fixed-s
substitute. -/
theorem coarse_rounded_power_budget {D ε z : ℝ} (hD : 2 ≤ D)
    (hε : 0 < ε) (hz : 1 < z) (huz : D ^ (ε ^ 2) ≤ z)
    (hlarge : (2 / ε ^ 2) ^ 13 ≤ Real.log D) :
    (roundedSieveCoordinate D z) ^ 13 ≤ Real.log (⌈D⌉₊ : ℝ) := by
  have hD0 : 0 < D := by linarith
  have hlogD : 0 < Real.log D := Real.log_pos (by linarith)
  have hlogz : 0 < Real.log z := Real.log_pos hz
  have hlog2 : Real.log 2 ≤ Real.log D := Real.log_le_log (by norm_num) hD
  have hceil :
      Real.log D ≤ Real.log (⌈D⌉₊ : ℝ) ∧
        Real.log (⌈D⌉₊ : ℝ) ≤ 2 * Real.log D := by
    simpa only [Real.rpow_one, one_mul] using
      log_ceil_rpow_bounds (ε := 1) hD (by simpa only [one_mul] using hlog2)
  have hlogu : ε ^ 2 * Real.log D ≤ Real.log z := by
    have h := Real.log_le_log (Real.rpow_pos_of_pos hD0 _) huz
    simpa only [Real.log_rpow hD0] using h
  have hs0 : 0 ≤ roundedSieveCoordinate D z :=
    (roundedSieveCoordinate_pos (by linarith) hz).le
  have hs : roundedSieveCoordinate D z ≤ 2 / ε ^ 2 := by
    apply (div_le_iff₀ hlogz).mpr
    have hm := mul_le_mul_of_nonneg_left hlogu (show 0 ≤ 2 / ε ^ 2 by positivity)
    have hid : 2 / ε ^ 2 * (ε ^ 2 * Real.log D) = 2 * Real.log D := by
      field_simp
    rw [hid] at hm
    exact hceil.2.trans hm
  exact (pow_le_pow_left₀ hs0 hs 13).trans (hlarge.trans hceil.1)

theorem roughOrdinaryDensity_empty (upper : Bool) {D : ℝ} (hD : 1 < D)
    (g : ℕ → ℝ) :
    roughOrdinaryDensity upper D ∅ g = 1 := by
  cases upper <;>
    simp [roughOrdinaryDensity, ordinaryRoughSet, setWeight, upperSetWeight,
      LowerAdmissibleSet, UpperAdmissibleSet, hD]

/-- Genuine F/f density of the SAME ordinary coefficient appearing in the
finite signed-family comparison. The absolute constant precedes `ε`; the
large-D threshold precedes all prime sets, densities, cutoffs, and `K`.
The original product constant and unrounded `log D / log z` are retained. -/
theorem exists_roughOrdinaryDensity_ff_target :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ε < 1 / 8 →
      ∃ D₀ : ℝ, 2 ≤ D₀ ∧ ∀ D : ℝ, D₀ ≤ D →
        ∀ (P : Finset ℕ), (∀ p ∈ P, p.Prime) →
          ∀ (g : ArithmeticFunction ℝ), g.IsMultiplicative →
            (∀ p ∈ P, 0 ≤ g p ∧ g p < 1) →
            ∀ z : ℝ, 2 ≤ z → z ≤ Real.sqrt D →
              (∀ p ∈ P \ geometricSmallPrimes P D ε, (p : ℝ) < z) →
              ∀ K : ℝ, 0 ≤ K → DimensionOneProductBound P g K →
                let R := P \ geometricSmallPrimes P D ε
                let V := ∏ p ∈ R, (1 - g p)
                let E := C * (ε ^ 8)⁻¹ * Real.exp (6 * K + 2) *
                  (Real.log D) ^ (-(1 / 3 : ℝ))
                V * (jr1965f (Real.log D / Real.log z) - E) ≤
                    roughOrdinaryDensity false D R g ∧
                roughOrdinaryDensity true D R g ≤
                    V * (jr1965F (Real.log D / Real.log z) + E) := by
  obtain ⟨C, hC, hbound⟩ := exists_roughOrdinaryDensity_ff_of_powerBudget
  refine ⟨C, hC, ?_⟩
  intro ε hε hεsmall
  let M := max ((2 / ε ^ 2) ^ 13) (Real.exp 1)
  refine ⟨max 2 (Real.exp M), le_max_left _ _, ?_⟩
  intro D hD P hP g hgm hg z hz hzD hcut K hK hdim
  have hD2 : 2 ≤ D := (le_max_left _ _).trans hD
  have hD1 : 1 < D := by linarith
  have hz1 : 1 < z := by linarith
  have hlogD : 0 < Real.log D := Real.log_pos hD1
  have hlarge : M ≤ Real.log D := by
    have h := Real.log_le_log (Real.exp_pos M) ((le_max_right _ _).trans hD)
    simpa only [Real.log_exp] using h
  have hceil : Real.log D ≤ Real.log (⌈D⌉₊ : ℝ) :=
    Real.log_le_log (by linarith) (Nat.le_ceil D)
  obtain ⟨hzD', hs2⟩ := coarseCoordinate_sqrt_bounds hD2 hz hzD
  let R := P \ geometricSmallPrimes P D ε
  let V := ∏ p ∈ R, (1 - g p)
  let E := C * (ε ^ 8)⁻¹ * Real.exp (6 * K + 2) *
    (Real.log D) ^ (-(1 / 3 : ℝ))
  have hR : R ⊆ P := sdiff_subset
  have hgR : ∀ p ∈ R, 0 ≤ g p ∧ g p < 1 := fun p hp => hg p (hR hp)
  have hV0 : 0 ≤ V := prod_nonneg (fun p hp => sub_nonneg.mpr (hgR p hp).2.le)
  have hE0 : 0 ≤ E := by
    dsimp [E]
    exact mul_nonneg (by positivity) (Real.rpow_nonneg hlogD.le _)
  change V * (jr1965f (Real.log D / Real.log z) - E) ≤
      roughOrdinaryDensity false D R g ∧
    roughOrdinaryDensity true D R g ≤ V * (jr1965F (Real.log D / Real.log z) + E)
  by_cases huz : D ^ (ε ^ 2) ≤ z
  · have hbudget := coarse_rounded_power_budget hD2 hε hz1 huz
      ((le_max_left _ _).trans hlarge)
    have hlog : Real.exp 1 ≤ Real.log (⌈D⌉₊ : ℝ) :=
      ((le_max_right _ _).trans hlarge).trans hceil
    have h := hbound R (fun p hp => hP p (hR hp)) g hgm hgR D z K
      hD1 hz1 hzD' hcut hK (dimensionOneProductBound_subset hR hg hdim)
      hs2 hbudget hlog
    have heps : 1 ≤ (ε ^ 8)⁻¹ :=
      (one_le_inv₀ (pow_pos hε 8)).mpr (pow_le_one₀ hε.le (by linarith))
    have hE :
        C * Real.exp (6 * K + 2) * (Real.log D) ^ (-(1 / 3 : ℝ)) ≤ E := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hlogD.le _)
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      simpa only [mul_one] using mul_le_mul_of_nonneg_left heps hC.le
    have hVE := mul_le_mul_of_nonneg_left hE hV0
    dsimp only at h
    change V * (jr1965f (Real.log D / Real.log z) -
        C * Real.exp (6 * K + 2) * (Real.log D) ^ (-(1 / 3 : ℝ))) ≤
          roughOrdinaryDensity false D R g ∧
      roughOrdinaryDensity true D R g ≤ V * (jr1965F (Real.log D / Real.log z) +
        C * Real.exp (6 * K + 2) * (Real.log D) ^ (-(1 / 3 : ℝ))) at h
    constructor <;> nlinarith [h.1, h.2]
  · have hRempty : R = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro p hp
      have hpP := hR hp
      have hpsmall : p ∈ geometricSmallPrimes P D ε :=
        mem_filter.mpr ⟨hpP, hP p hpP, (hcut p hp).trans (lt_of_not_ge huz)⟩
      exact (mem_sdiff.mp hp).2 hpsmall
    have hV : V = 1 := by simp only [V, hRempty, prod_empty]
    rw [hRempty, hV, roughOrdinaryDensity_empty false hD1,
      roughOrdinaryDensity_empty true hD1, one_mul, one_mul]
    constructor
    · linarith [jr1965f_le_one (show 1 ≤ Real.log D / Real.log z by linarith)]
    · linarith [one_le_jr1965F (show 1 ≤ Real.log D / Real.log z by linarith)]

#check coarse_rounded_power_budget
#check exists_roughOrdinaryDensity_ff_target
#print axioms coarse_rounded_power_budget
#print axioms exists_roughOrdinaryDensity_ff_target

end MathlibNt.SieveTheory.LiLiuPrereqWF.CoarseDensity
