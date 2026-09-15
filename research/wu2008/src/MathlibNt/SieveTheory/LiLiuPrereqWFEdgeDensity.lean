import MathlibNt.SieveTheory.LiLiuPrereqWFEdgeDensityScalar
import MathlibNt.SieveTheory.LiLiuPrereqWFCoordinateShift

/-!
# Genuine upper density at the external near-two edge

The family is the accepted upper family on primes strictly below `sqrt D`.
For large dimension constants its bounded aggregate replaces, rather than
inflates, the internal analytic estimate.
-/

namespace MathlibNt.SieveTheory.LiLiuPrereqWF.EdgeDensity

open Finset ArithmeticFunction SmallRosser
open JurkatRichert1965ChenGammaOneQOne
open scoped Classical

private theorem small_dimension_edge_scalar {ε L K C r s : ℝ}
    (hε : 0 < ε) (hε8 : ε < 1 / 8) (hL : 1 ≤ L)
    (hK : 0 ≤ K) (hKL : K ≤ L) (hC : 0 ≤ C)
    (hr : 0 ≤ r) (hr2 : r ≤ 2)
    (hs : 2 ≤ s) (hsc : s ≤ 2 * (1 + ε + ε ^ 9))
    (hid : jr1965F 2 * r = jr1965F s * (1 + ε + ε ^ 9)) :
    (jr1965F 2 + C * (ε + (ε ^ 8)⁻¹ * Real.exp (6 * K + 2) *
        L ^ (-(1 / 3 : ℝ)))) * r * (1 + 2 * K / L) ≤
      jr1965F s + (6 * C + 6 * jr1965DelayConstant) *
        (ε + (ε ^ 8)⁻¹ * Real.exp (6 * K + 2) * L ^ (-(1 / 3 : ℝ))) := by
  let A := (ε ^ 8)⁻¹ * Real.exp (6 * K + 2) * L ^ (-(1 / 3 : ℝ))
  let T := ε + A
  let M := jr1965DelayConstant
  have hM : 0 ≤ M := CoordinateShift.delayConstant_pos.le
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hL0 : 0 < L := by linarith
  have ht0 : 0 ≤ K / L := div_nonneg hK hL0.le
  have ht1 : K / L ≤ 1 := (div_le_one hL0).mpr hKL
  have htA : K / L ≤ A := dimension_quotient_le_target hε (by linarith) hL hK
  have hc := CoordinateShift.scale_bounds hε hε8
  have hF : 0 ≤ jr1965F s := by
    rw [jr1965F_eq_of_le_three (by linarith [hc.2.2])]
    positivity
  have hFM : jr1965F s ≤ M := jr1965F_le_delayConstant (by linarith)
  have hmain : jr1965F 2 * r ≤ jr1965F s + 2 * M * ε := by
    rw [hid]
    have h := mul_le_mul_of_nonneg_left hc.2.1 hF
    have h' := mul_le_mul_of_nonneg_right hFM hε.le
    nlinarith
  have hmain2 : jr1965F 2 * r ≤ 2 * M := by
    rw [hid]
    have h := mul_le_mul_of_nonneg_left
      (show 1 + ε + ε ^ 9 ≤ 2 by linarith [hc.2.2]) hF
    nlinarith
  have hratio : r * (1 + 2 * K / L) ≤ 6 := by
    rw [mul_div_assoc]
    nlinarith
  have hpaid := mul_le_mul_of_nonneg_left htA (show 0 ≤ 4 * M by positivity)
  have hcross := mul_le_mul_of_nonneg_right hmain2 (show 0 ≤ 2 * (K / L) by positivity)
  have herr := mul_le_mul_of_nonneg_left hratio (mul_nonneg hC hT)
  change (jr1965F 2 + C * T) * r * (1 + 2 * K / L) ≤
    jr1965F s + (6 * C + 6 * M) * T
  rw [mul_div_assoc] at herr ⊢
  dsimp [T] at herr ⊢
  nlinarith [mul_nonneg hM hA, mul_nonneg hM hε.le]

/-- The absolute constant is chosen before epsilon; the threshold precedes
the prime carrier, multiplicative density, original dimension constant and
external cutoff. The weights are exactly the already accepted family. -/
theorem exists_signedFamilyDensity_upper_edge :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ε < 1 / 8 →
      ∃ D₀ : ℝ, 4 ≤ D₀ ∧ ∀ D : ℝ, D₀ ≤ D →
        ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) →
          ∀ ω : ArithmeticFunction ℝ, ω.IsMultiplicative →
            (∀ p ∈ P, 0 ≤ ω p / (p : ℝ) ∧ ω p / (p : ℝ) < 1) →
            ∀ K : ℝ, 0 ≤ K → DimensionOneProductBound P (primeDensity ω) K →
              ∀ z : ℝ, Real.sqrt D < z →
                z ≤ Real.sqrt (D ^ (1 + ε + ε ^ 9)) →
                (∀ p ∈ P, (p : ℝ) < z) →
                signedFamilyDensity true (P.filter (fun p : ℕ => (p : ℝ) < Real.sqrt D))
                    D ε (geometricSieveLabel D ε) (primeDensity ω) ≤
                  (∏ p ∈ P, (1 - ω p / (p : ℝ))) *
                    (jr1965F (Real.log (D ^ (1 + ε + ε ^ 9)) / Real.log z) +
                      C * (ε + (ε ^ 8)⁻¹ * Real.exp (6 * K + 2) *
                        Real.log D ^ (-(1 / 3 : ℝ)))) := by
  obtain ⟨Ci, hCi, hi⟩ := exists_signedFamilyDensity_ff
  let B := ((1 / Real.log 2) * (1 + 1 / Real.log 2)) ^ 2
  let C := 6 * Ci + 6 * jr1965DelayConstant + B + 1
  have hB : 0 ≤ B := sq_nonneg _
  have hM := CoordinateShift.delayConstant_pos
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro ε hε hε8
  obtain ⟨Di, hDi, hi⟩ := hi ε hε hε8
  refine ⟨max (max Di 4) (Real.exp 1),
    (le_max_right Di 4).trans (le_max_left _ _), ?_⟩
  intro D hD P hP ω hω hg K hK hdim z hz hzQ hcut
  have hD4 : 4 ≤ D := ((le_max_right Di 4).trans (le_max_left _ _)).trans hD
  have hDiD : Di ≤ D := ((le_max_left Di 4).trans (le_max_left _ _)).trans hD
  have hD0 : 0 < D := by linarith
  have hL : 1 ≤ Real.log D := by
    have h := Real.log_le_log (Real.exp_pos 1) ((le_max_right _ _).trans hD)
    simpa only [Real.log_exp] using h
  have hL0 : 0 < Real.log D := by linarith
  have hsqrt : 2 ≤ Real.sqrt D := by
    nlinarith [Real.sq_sqrt hD0.le, Real.sqrt_nonneg D]
  have hz2 : 2 < z := hsqrt.trans_lt hz
  have hy0 : 0 < Real.log z := Real.log_pos (by linarith)
  let c := 1 + ε + ε ^ 9
  let s := Real.log (D ^ c) / Real.log z
  let r := Real.log z / Real.log (Real.sqrt D)
  let P₀ := P.filter (fun p : ℕ => (p : ℝ) < Real.sqrt D)
  let g := primeDensity ω
  let V := ∏ p ∈ P, (1 - g p)
  let V₀ := ∏ p ∈ P₀, (1 - g p)
  let T := ε + (ε ^ 8)⁻¹ * Real.exp (6 * K + 2) *
    Real.log D ^ (-(1 / 3 : ℝ))
  have hc := CoordinateShift.scale_bounds hε hε8
  have hlogQ : Real.log (D ^ c) = c * Real.log D := Real.log_rpow hD0 c
  have hlogroot : Real.log (Real.sqrt D) = Real.log D / 2 := Real.log_sqrt hD0.le
  have hylow : Real.log D / 2 < Real.log z := by
    simpa only [hlogroot] using Real.log_lt_log (by linarith : 0 < Real.sqrt D) hz
  have hyhigh : Real.log z ≤ c * Real.log D / 2 := by
    have h := Real.log_le_log (by linarith : 0 < z) hzQ
    rw [Real.log_sqrt (Real.rpow_nonneg hD0.le c), hlogQ] at h
    exact h
  have hc2 : c ≤ 2 := by dsimp [c]; linarith [hc.2.2]
  have hyL : Real.log z ≤ Real.log D := by nlinarith
  have hs : 2 ≤ s := by
    dsimp [s]
    rw [hlogQ]
    exact (le_div_iff₀ hy0).mpr (by linarith)
  have hsc : s ≤ 2 * c := by
    dsimp [s]
    rw [hlogQ]
    apply (div_le_iff₀ hy0).mpr
    have hc0 : 0 ≤ c := by dsimp [c]; positivity
    nlinarith
  have hr : 0 ≤ r := by dsimp [r]; rw [hlogroot]; positivity
  have hr2 : r ≤ 2 := by
    dsimp [r]
    rw [hlogroot]
    exact (div_le_iff₀ (by positivity)).mpr (by linarith)
  have hid : jr1965F 2 * r = jr1965F s * c := by
    have hre : r = 2 * c / s := by
      dsimp [r, s]
      rw [hlogroot, hlogQ]
      have hc0 : c ≠ 0 := by dsimp [c]; positivity
      field_simp
    rw [hre]
    exact CoordinateShift.upper_edge_exact hs hsc hc.2.2
  have hP₀ : P₀ ⊆ P := filter_subset _ _
  have hprime₀ : ∀ p ∈ P₀, p.Prime := fun p hp => hP p (hP₀ hp)
  have hg₀ : ∀ p ∈ P₀, 0 ≤ ω p / (p : ℝ) ∧ ω p / (p : ℝ) < 1 :=
    fun p hp => hg p (hP₀ hp)
  have hcut₀ : ∀ p ∈ P₀ \ geometricSmallPrimes P₀ D ε, (p : ℝ) < Real.sqrt D :=
    fun p hp => (mem_filter.mp (mem_sdiff.mp hp).1).2
  have hV : 0 < V := prod_pos (fun p hp => sub_pos.mpr (hg p hp).2)
  have hV₀ : 0 ≤ V₀ := prod_nonneg (fun p hp => sub_nonneg.mpr (hg₀ p hp).2.le)
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hF : 0 ≤ jr1965F s := by
    rw [jr1965F_eq_of_le_three (by dsimp [c] at hsc; linarith [hc.2.2])]
    positivity
  change signedFamilyDensity true P₀ D ε (geometricSieveLabel D ε) g ≤
    V * (jr1965F s + C * T)
  by_cases hKL : K ≤ Real.log D
  · have hdim₀ := CoarseDensity.dimensionOneProductBound_subset hP₀ hg hdim
    have hinternal := (hi D hDiD P₀ hprime₀ ω hω hg₀ (Real.sqrt D)
      hsqrt le_rfl hcut₀ K hK hdim₀).2
    have hcoord : Real.log D / Real.log (Real.sqrt D) = 2 := by
      rw [hlogroot]
      field_simp
    change signedFamilyDensity true P₀ D ε (geometricSieveLabel D ε) g ≤
      V₀ * (jr1965F (Real.log D / Real.log (Real.sqrt D)) + Ci * T) at hinternal
    rw [hcoord] at hinternal
    have hratio := euler_truncation_ratio P hP hg hsqrt hz hcut hdim
    change V₀ / V ≤ r * (1 + K / Real.log (Real.sqrt D)) at hratio
    rw [hlogroot] at hratio
    have hquot : K / (Real.log D / 2) = 2 * K / Real.log D := by ring
    rw [hquot] at hratio
    have hratio' : V₀ ≤ V * (r * (1 + 2 * K / Real.log D)) := by
      have h := (div_le_iff₀ hV).mp hratio
      simpa only [mul_comm] using h
    have hF2 : 0 ≤ jr1965F 2 := by
      rw [jr1965F_eq_of_le_three (by norm_num)]
      positivity
    have hscalar := small_dimension_edge_scalar hε hε8 hL hK hKL hCi.le
      hr hr2 hs hsc hid
    have hconst : 6 * Ci + 6 * jr1965DelayConstant ≤ C := by dsimp [C]; linarith
    calc
      _ ≤ V₀ * (jr1965F 2 + Ci * T) := hinternal
      _ ≤ (V * (r * (1 + 2 * K / Real.log D))) *
          (jr1965F 2 + Ci * T) :=
        mul_le_mul_of_nonneg_right hratio' (by positivity)
      _ = V * ((jr1965F 2 + Ci * T) * r * (1 + 2 * K / Real.log D)) := by ring
      _ ≤ V * (jr1965F s + (6 * Ci + 6 * jr1965DelayConstant) * T) :=
        mul_le_mul_of_nonneg_left hscalar hV.le
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (add_le_add le_rfl (mul_le_mul_of_nonneg_right hconst hT)) hV.le
  · have habs := signedFamilyDensity_abs_le_plusProduct true P₀ hprime₀
      (show 2 ≤ D by linarith) hε hcut₀ (primeDensity_isMultiplicative hω)
      (fun p hp => (hg₀ p hp).1)
    have hplus := plusProduct_le_full_euler P P₀ hP₀ hP hg hz2 hcut hdim
    have hscalar := large_dimension_square_le_target
      (show 0 < Real.log 2 from Real.log_pos (by norm_num)) hε (by linarith)
      hL hy0.le hyL (le_of_not_ge hKL)
    have hscalar' : (Real.log z / Real.log 2 * (1 + K / Real.log 2)) ^ 2 ≤ B * T := by
      apply hscalar.trans
      apply mul_le_mul_of_nonneg_left _ hB
      dsimp [T]
      linarith
    have hconst : B ≤ C := by dsimp [C]; linarith
    calc
      _ ≤ |signedFamilyDensity true P₀ D ε (geometricSieveLabel D ε) g| := le_abs_self _
      _ ≤ ∏ p ∈ P₀, (1 + g p) := habs
      _ ≤ V * (Real.log z / Real.log 2 * (1 + K / Real.log 2)) ^ 2 := hplus
      _ ≤ V * (B * T) := mul_le_mul_of_nonneg_left hscalar' hV.le
      _ ≤ V * (jr1965F s + C * T) := by
        apply mul_le_mul_of_nonneg_left _ hV.le
        linarith [mul_le_mul_of_nonneg_right hconst hT]

#check exists_signedFamilyDensity_upper_edge
#print axioms exists_signedFamilyDensity_upper_edge

end MathlibNt.SieveTheory.LiLiuPrereqWF.EdgeDensity
