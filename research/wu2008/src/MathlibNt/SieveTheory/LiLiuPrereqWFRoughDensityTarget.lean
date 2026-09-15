import MathlibNt.SieveTheory.LiLiuPrereqWFBoundaryAnalyticTarget

/-!
# The same rough signed density at the normalized analytic scale

Both actual error classes are now paid. The comparison is to the very same
ordinary rough Rosser coefficient, with its original level and parity.
-/

namespace MathlibNt.SieveTheory.LiLiuPrereqWF

open Finset SmallRosser
open scoped Classical

theorem roughCollisionPairContribution_le_target (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) {D ε K : ℝ}
    (hD : 2 ≤ D) (hε : 0 < ε) (hεsmall : ε < 1 / 8)
    (hlarge : 1 ≤ ε ^ 2 * Real.log D) (hK : 0 ≤ K)
    (hcut : ∀ p ∈ P \ geometricSmallPrimes P D ε, (p : ℝ) < Real.sqrt D)
    {g : ℕ → ℝ} (hg : ∀ p ∈ P, 0 ≤ g p ∧ g p < 1)
    (hdim : DimensionOneProductBound P g K) :
    let R := P \ geometricSmallPrimes P D ε
    let b := fun p => geometricLower D ε (ε ^ 9) (geometricSieveLabel D ε p)
    (∏ p ∈ R, (1 + g p)) * roughCollisionPairMass b R g ≤
      10 * (∏ p ∈ R, (1 - g p)) *
        (ε + (ε ^ 8)⁻¹ * Real.exp (6 * K + 2) * Real.log D ^ (-(1 / 3 : ℝ))) := by
  dsimp only
  have hlog : 0 < Real.log D := Real.log_pos (by linarith)
  let A := (1 + K / (ε ^ 2 * Real.log D)) / ε ^ 2
  let d := ε ^ 9 + 2 * K / (ε ^ 2 * Real.log D)
  let V := ∏ p ∈ P \ geometricSmallPrimes P D ε, (1 - g p)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hV : 0 ≤ V :=
    prod_nonneg (fun p hp => sub_nonneg.mpr (hg p (mem_sdiff.mp hp).1).2.le)
  have hpair := CollisionAnalytic.roughCollisionPairMass_le_dimensionOne
    P hP hD hε hεsmall hlarge hK hcut hg hdim
  have hE := roughEulerProduct_le_normalized P hP hD hε hεsmall hlarge hcut hg hdim
  have hprod0 : 0 ≤ ∏ p ∈ P \ geometricSmallPrimes P D ε, (1 + g p) :=
    prod_nonneg (fun p hp => by linarith [(hg p (mem_sdiff.mp hp).1).1])
  have hp := mul_le_mul hpair hE hprod0 (mul_nonneg hd hA)
  have heps : ε ^ 9 ≤ ε ^ 7 :=
    pow_le_pow_of_le_one hε.le (by linarith) (by omega)
  have hdle : d ≤ 2 * (3 * ε ^ 7 + 2 * K / (ε ^ 2 * Real.log D)) := by
    dsimp [d]
    have hk0 : 0 ≤ 2 * K / (ε ^ 2 * Real.log D) := by positivity
    nlinarith [pow_nonneg hε.le 7]
  have hm := mul_le_mul_of_nonneg_left hdle (mul_nonneg hV (pow_nonneg hA 3))
  have hs := mul_le_mul_of_nonneg_left
    (BoundaryAnalytic.boundary_scalar hε (by linarith) hlog hK hlarge) hV
  dsimp only at hpair
  change _ ≤ 10 * V * _
  change _ ≤ V * _ at hs
  change _ ≤ V * A ^ 2 at hE
  change _ ≤ (d * A) * (V * A ^ 2) at hp
  change V * A ^ 3 * d ≤ _ at hm
  dsimp [A] at hm
  dsimp [A, d, V] at hp ⊢
  dsimp [V] at hs hm
  nlinarith

/-- Both signs of the actual rough family differ from the ordinary family
by at most the same Euler-normalized error. -/
theorem roughSignedDensity_abs_sub_le_target (upper : Bool) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) {D ε K : ℝ}
    (hD : 2 ≤ D) (hε : 0 < ε) (hεsmall : ε < 1 / 8)
    (hlarge : 1 ≤ ε ^ 2 * Real.log D) (hK : 0 ≤ K)
    (hcut : ∀ p ∈ P \ geometricSmallPrimes P D ε, (p : ℝ) < Real.sqrt D)
    {g : ℕ → ℝ} (hg : ∀ p ∈ P, 0 ≤ g p ∧ g p < 1)
    (hdim : DimensionOneProductBound P g K) :
    let R := P \ geometricSmallPrimes P D ε
    let b := fun p => geometricLower D ε (ε ^ 9) (geometricSieveLabel D ε p)
    let c := fun p => b p ^ (1 + ε ^ 9)
    |roughSignedDensity upper b c D R g - roughOrdinaryDensity upper D R g| ≤
      20 * (∏ p ∈ R, (1 - g p)) *
        (ε + (ε ^ 8)⁻¹ * Real.exp (6 * K + 2) * Real.log D ^ (-(1 / 3 : ℝ))) := by
  have hp := roughCollisionPairContribution_le_target P hP hD hε hεsmall
    hlarge hK hcut hg hdim
  have hb := BoundaryAnalytic.roughBoundaryMass_le_target upper P hP hD hε hεsmall
    hlarge hK hcut hg hdim
  obtain ⟨h0, h1⟩ := roughSignedDensity_canonical_pair_bound upper P hP (D := D)
    (by linarith) hε g (fun p hp => (hg p (mem_sdiff.mp hp).1).1)
  dsimp only at hp hb h0 h1 ⊢
  cases upper <;> simp only [Bool.false_eq_true, if_false, if_true,
    one_mul, neg_one_mul] at *
  · rw [abs_of_nonpos (by linarith)]
    nlinarith
  · rw [abs_of_nonneg h0]
    nlinarith

#check roughCollisionPairContribution_le_target
#print axioms roughCollisionPairContribution_le_target
#check roughSignedDensity_abs_sub_le_target
#print axioms roughSignedDensity_abs_sub_le_target

end MathlibNt.SieveTheory.LiLiuPrereqWF
