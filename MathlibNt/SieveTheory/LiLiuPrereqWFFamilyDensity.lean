import MathlibNt.SieveTheory.LiLiuPrereqWFRoughDensityTarget
import MathlibNt.SieveTheory.LiLiuPrereqWFCoarseDensityTarget

/-!
# Genuine F/f density of the fixed normalized signed family

All three terms in the comparison use the same coefficients. In particular,
the lower small-weight density is never assumed positive: its error is paid
against the absolute rough Euler majorant before the coarse F/f inequalities
are used. The original dimension-one constant and uniform threshold order
are retained.
-/

namespace MathlibNt.SieveTheory.LiLiuPrereqWF

open Finset ArithmeticFunction SmallRosser
open JurkatRichert1965ChenGammaOneQOne
open scoped Classical

theorem roughSignedDensity_abs_le_euler (upper : Bool) (b c : ℕ → ℝ)
    (D : ℝ) (R : Finset ℕ) (g : ℕ → ℝ) (hg : ∀ p ∈ R, 0 ≤ g p) :
    |roughSignedDensity upper b c D R g| ≤ ∏ p ∈ R, (1 + g p) := by
  rw [roughSignedDensity, prod_one_add]
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro s hs
  have hp : 0 ≤ ∏ p ∈ s, g p := prod_nonneg (fun p hp => hg p (mem_powerset.mp hs hp))
  have hc : |normalizedSignedSet upper b c D s| ≤ 1 := by
    cases upper <;> simp only [normalizedSignedSet, normalizedUpperSet, normalizedLowerSet,
      Bool.false_eq_true, if_true, if_false] <;> split_ifs <;> norm_num
  rw [abs_mul, abs_of_nonneg hp]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hc hp

private theorem euler_partition (P : Finset ℕ) (D ε : ℝ) (g : ℕ → ℝ) :
    (∏ p ∈ geometricSmallPrimes P D ε, (1 - g p)) *
      (∏ p ∈ P \ geometricSmallPrimes P D ε, (1 - g p)) =
        ∏ p ∈ P, (1 - g p) := by
  have hB : geometricSmallPrimes P D ε ⊆ P := filter_subset _ _
  rw [mul_comm, ← prod_union sdiff_disjoint,
    sdiff_union_of_subset hB]

/-- A full-`V(P)` comparison with the same ordinary coarse density. The
small weight, rough signed weight, and replacement remainder are not changed. -/
theorem exists_signedFamilyDensity_coarse_comparison_target :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ε < 1 / 8 →
      ∃ D₀ : ℝ, 2 ≤ D₀ ∧ ∀ D : ℝ, D₀ ≤ D →
        ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) →
          (∀ p ∈ P \ geometricSmallPrimes P D ε, (p : ℝ) < Real.sqrt D) →
          ∀ ω : ArithmeticFunction ℝ, ω.IsMultiplicative →
            (∀ p ∈ P, 0 ≤ ω p / (p : ℝ) ∧ ω p / (p : ℝ) < 1) →
            ∀ K : ℝ, 0 ≤ K → DimensionOneProductBound P (primeDensity ω) K →
              ∀ upper : Bool,
                let B := geometricSmallPrimes P D ε
                let g := primeDensity ω
                |signedFamilyDensity upper P D ε (geometricSieveLabel D ε) g -
                    (∏ p ∈ B, (1 - g p)) * roughOrdinaryDensity upper D (P \ B) g| ≤
                  (∏ p ∈ P, (1 - g p)) * C *
                    (ε + (ε ^ 8)⁻¹ * Real.exp (6 * K + 2) *
                      Real.log D ^ (-(1 / 3 : ℝ))) := by
  obtain ⟨Cr, hCr, hr⟩ := exists_signedFamilyDensity_replacement_target
  obtain ⟨Cs, hCs, hs⟩ := exists_smallWeight_source_fundamental_density
  refine ⟨Cr + 120 * Cs + 20, by positivity, ?_⟩
  intro ε hε hεsmall
  obtain ⟨Dr, hDr, hr⟩ := hr ε hε hεsmall
  obtain ⟨Ds, hDs, hs⟩ := hs ε hε hεsmall
  refine ⟨max (max Dr Ds) (Real.exp (1 / ε ^ 2)),
    hDr.trans ((le_max_left _ _).trans (le_max_left _ _)), ?_⟩
  intro D hD P hP hcut ω hω hg K hK hdim upper
  have hDbase : max Dr Ds ≤ D := (le_max_left _ _).trans hD
  have hDrD : Dr ≤ D := (le_max_left _ _).trans hDbase
  have hDsD : Ds ≤ D := (le_max_right _ _).trans hDbase
  have hD2 : 2 ≤ D := hDr.trans hDrD
  have hlog : 0 < Real.log D := Real.log_pos (by linarith)
  have hlarge : 1 ≤ ε ^ 2 * Real.log D := by
    have hh := Real.log_le_log (Real.exp_pos (1 / ε ^ 2))
      ((le_max_right _ _).trans hD)
    rw [Real.log_exp] at hh
    exact (div_le_iff₀ (sq_pos_of_pos hε)).mp hh |>.trans_eq (mul_comm _ _)
  let B := geometricSmallPrimes P D ε
  let R := P \ B
  let g := primeDensity ω
  let b := fun p => geometricLower D ε (ε ^ 9) (geometricSieveLabel D ε p)
  let c := fun p => b p ^ (1 + ε ^ 9)
  let VB := ∏ p ∈ B, (1 - g p)
  let VR := ∏ p ∈ R, (1 - g p)
  let V := ∏ p ∈ P, (1 - g p)
  let E := Real.exp (-(1 / ε)) + Real.exp (Real.sqrt K - 1 / ε) *
    (ε * Real.log D) ^ (-(1 / 3 : ℝ))
  let T := ε + (ε ^ 8)⁻¹ * Real.exp (6 * K + 2) * Real.log D ^ (-(1 / 3 : ℝ))
  let A := (1 + K / (ε ^ 2 * Real.log D)) / ε ^ 2
  let rho := roughSignedDensity upper b c D R g
  let ordinary := roughOrdinaryDensity upper D R g
  let small := smallWeightDensity upper P D ε g
  let density := signedFamilyDensity upper P D ε (geometricSieveLabel D ε) g
  have hg' : ∀ p ∈ P, 0 ≤ g p ∧ g p < 1 := hg
  have hVB : 0 ≤ VB := prod_nonneg (fun p hp =>
    sub_nonneg.mpr (hg' p (mem_filter.mp hp).1).2.le)
  have hVR : 0 ≤ VR := prod_nonneg (fun p hp =>
    sub_nonneg.mpr (hg' p (mem_sdiff.mp hp).1).2.le)
  have hV : 0 ≤ V := prod_nonneg (fun p hp => sub_nonneg.mpr (hg' p hp).2.le)
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hpartition : VB * VR = V := euler_partition P D ε g
  have hrepl : |density - small * rho| ≤ V * Cr * T := by
    exact (hr D hDrD P hP hcut ω hω hg K hK hdim upper).2
  have hsmall : |small - VB| ≤ VB * (Cs * E) := by
    have hh := hs D hDsD P ω hω
      (fun p hp => hg p (mem_filter.mp hp).1) K hK hdim
    cases upper
    · simpa only [small, smallWeightDensity, Bool.false_eq_true, if_false,
        VB, B, g, primeDensity_apply, E] using hh.1
    · simpa only [small, smallWeightDensity, if_true,
        VB, B, g, primeDensity_apply, E] using hh.2
  have hrho : |rho| ≤ ∏ p ∈ R, (1 + g p) :=
    roughSignedDensity_abs_le_euler upper b c D R g
      (fun p hp => (hg' p (mem_sdiff.mp hp).1).1)
  have heuler : (∏ p ∈ R, (1 + g p)) ≤ VR * A ^ 2 :=
    roughEulerProduct_le_normalized P hP hD2 hε hεsmall hlarge hcut hg' hdim
  have hscalar : E / ε ^ 4 * (1 + K / (ε ^ 2 * Real.log D)) ^ 2 ≤ 120 * T :=
    roughEuler_replacement_scalar hε (by linarith) hlog hK hlarge
  have hsmallrho : |(small - VB) * rho| ≤ V * (120 * Cs) * T := by
    rw [abs_mul]
    calc
      _ ≤ (VB * (Cs * E)) * (∏ p ∈ R, (1 + g p)) :=
        mul_le_mul hsmall hrho (abs_nonneg _) (by positivity)
      _ ≤ (VB * (Cs * E)) * (VR * A ^ 2) :=
        mul_le_mul_of_nonneg_left heuler (by positivity)
      _ = V * Cs * (E / ε ^ 4 * (1 + K / (ε ^ 2 * Real.log D)) ^ 2) := by
        rw [← hpartition]
        dsimp [A]
        ring
      _ ≤ V * Cs * (120 * T) :=
        mul_le_mul_of_nonneg_left hscalar (mul_nonneg hV hCs.le)
      _ = _ := by ring
  have hrough : |rho - ordinary| ≤ 20 * VR * T :=
    roughSignedDensity_abs_sub_le_target upper P hP hD2 hε hεsmall hlarge hK hcut hg' hdim
  have hroughV : |VB * (rho - ordinary)| ≤ V * 20 * T := by
    rw [abs_mul, abs_of_nonneg hVB]
    calc
      _ ≤ VB * (20 * VR * T) := mul_le_mul_of_nonneg_left hrough hVB
      _ = _ := by rw [← hpartition]; ring
  change |density - VB * ordinary| ≤ V * (Cr + 120 * Cs + 20) * T
  have hid : density - VB * ordinary =
      (density - small * rho) + (small - VB) * rho + VB * (rho - ordinary) := by ring
  rw [hid]
  calc
    _ ≤ |density - small * rho| + |(small - VB) * rho| +
        |VB * (rho - ordinary)| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ V * Cr * T + V * (120 * Cs) * T + V * 20 * T :=
      add_le_add (add_le_add hrepl hsmallrho) hroughV
    _ = _ := by ring

/-- The actual common signed family has the genuine linear-sieve densities
on the internal domain `2 ≤ z ≤ sqrt D`. The lower error is subtracted. -/
theorem exists_signedFamilyDensity_ff :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ε < 1 / 8 →
      ∃ D₀ : ℝ, 2 ≤ D₀ ∧ ∀ D : ℝ, D₀ ≤ D →
        ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) →
          ∀ ω : ArithmeticFunction ℝ, ω.IsMultiplicative →
            (∀ p ∈ P, 0 ≤ ω p / (p : ℝ) ∧ ω p / (p : ℝ) < 1) →
            ∀ z : ℝ, 2 ≤ z → z ≤ Real.sqrt D →
              (∀ p ∈ P \ geometricSmallPrimes P D ε, (p : ℝ) < z) →
              ∀ K : ℝ, 0 ≤ K → DimensionOneProductBound P (primeDensity ω) K →
                let V := ∏ p ∈ P, (1 - ω p / (p : ℝ))
                let E := C * (ε + (ε ^ 8)⁻¹ * Real.exp (6 * K + 2) *
                  Real.log D ^ (-(1 / 3 : ℝ)))
                V * (jr1965f (Real.log D / Real.log z) - E) ≤
                    signedFamilyDensity false P D ε (geometricSieveLabel D ε) (primeDensity ω) ∧
                  signedFamilyDensity true P D ε (geometricSieveLabel D ε) (primeDensity ω) ≤
                    V * (jr1965F (Real.log D / Real.log z) + E) := by
  obtain ⟨Ca, hCa, ha⟩ := exists_signedFamilyDensity_coarse_comparison_target
  obtain ⟨Cf, hCf, hf⟩ := CoarseDensity.exists_roughOrdinaryDensity_ff_target
  refine ⟨Ca + Cf, by positivity, ?_⟩
  intro ε hε hεsmall
  obtain ⟨Da, hDa, ha⟩ := ha ε hε hεsmall
  obtain ⟨Df, hDf, hf⟩ := hf ε hε hεsmall
  refine ⟨max Da Df, hDa.trans (le_max_left _ _), ?_⟩
  intro D hD P hP ω hω hg z hz hzD hcut K hK hdim
  have hDaD := (le_max_left _ _).trans hD
  have hDfD := (le_max_right _ _).trans hD
  have hrough : ∀ p ∈ P \ geometricSmallPrimes P D ε, (p : ℝ) < Real.sqrt D :=
    fun p hp => (hcut p hp).trans_le hzD
  let g := primeDensity ω
  let B := geometricSmallPrimes P D ε
  let VB := ∏ p ∈ B, (1 - g p)
  let VR := ∏ p ∈ P \ B, (1 - g p)
  let V := ∏ p ∈ P, (1 - g p)
  let T := ε + (ε ^ 8)⁻¹ * Real.exp (6 * K + 2) * Real.log D ^ (-(1 / 3 : ℝ))
  let tail := (ε ^ 8)⁻¹ * Real.exp (6 * K + 2) * Real.log D ^ (-(1 / 3 : ℝ))
  have hVB : 0 ≤ VB := prod_nonneg (fun p hp =>
    sub_nonneg.mpr (hg p (mem_filter.mp hp).1).2.le)
  have hV : 0 ≤ V := prod_nonneg (fun p hp => sub_nonneg.mpr (hg p hp).2.le)
  have hpart : VB * VR = V := euler_partition P D ε g
  have hlow := (abs_le.mp (ha D hDaD P hP hrough ω hω hg K hK hdim false)).1
  have hupp := (abs_le.mp (ha D hDaD P hP hrough ω hω hg K hK hdim true)).2
  have hff := hf D hDfD P hP g (primeDensity_isMultiplicative hω) hg z hz hzD hcut K hK hdim
  have hl := mul_le_mul_of_nonneg_left hff.1 hVB
  have hu := mul_le_mul_of_nonneg_left hff.2 hVB
  dsimp only at hl hu hlow hupp ⊢
  change -(V * Ca * T) ≤
    signedFamilyDensity false P D ε (geometricSieveLabel D ε) g -
      VB * roughOrdinaryDensity false D (P \ B) g at hlow
  change signedFamilyDensity true P D ε (geometricSieveLabel D ε) g -
      VB * roughOrdinaryDensity true D (P \ B) g ≤ V * Ca * T at hupp
  have hidl : VB * (VR * (jr1965f (Real.log D / Real.log z) - Cf * tail)) =
      V * (jr1965f (Real.log D / Real.log z) - Cf * tail) := by rw [← mul_assoc, hpart]
  have hidu : VB * (VR * (jr1965F (Real.log D / Real.log z) + Cf * tail)) =
      V * (jr1965F (Real.log D / Real.log z) + Cf * tail) := by rw [← mul_assoc, hpart]
  change VB * (VR * (jr1965f (Real.log D / Real.log z) - _)) ≤
      VB * roughOrdinaryDensity false D (P \ B) g at hl
  change VB * roughOrdinaryDensity true D (P \ B) g ≤
      VB * (VR * (jr1965F (Real.log D / Real.log z) + _)) at hu
  have htailEq : Cf * (ε ^ 8)⁻¹ * Real.exp (6 * K + 2) *
      Real.log D ^ (-(1 / 3 : ℝ)) = Cf * tail := by dsimp [tail]; ring
  rw [htailEq, hidl] at hl
  rw [htailEq, hidu] at hu
  have htail : tail ≤ T := by dsimp [tail, T]; linarith
  have hpay := mul_le_mul_of_nonneg_left htail (mul_nonneg hV hCf.le)
  change V * (jr1965f (Real.log D / Real.log z) - (Ca + Cf) * T) ≤ _ ∧
    _ ≤ V * (jr1965F (Real.log D / Real.log z) + (Ca + Cf) * T)
  constructor <;> nlinarith

#check exists_signedFamilyDensity_coarse_comparison_target
#print axioms exists_signedFamilyDensity_coarse_comparison_target
#check exists_signedFamilyDensity_ff
#print axioms exists_signedFamilyDensity_ff

end MathlibNt.SieveTheory.LiLiuPrereqWF
