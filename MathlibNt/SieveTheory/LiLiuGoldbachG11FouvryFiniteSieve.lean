import MathlibNt.SieveTheory.LiLiuGoldbachG11RectangleCount
import MathlibNt.SieveTheory.LiLiuFouvryG9MainNormalization

open Finset Filter
open scoped BigOperators Classical
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
open MathlibNt.SieveTheory.LiLiuPrereqWF

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- The original weighted divisibility sum is literally the product-indexed
integer AP count. In particular, zero and negative overhang are not truncated. -/
theorem goldbachG11RectangleDivCount_eq (N d : ℕ) (U V : Finset ℕ) :
    weightedDivCount (U ×ˢ V)
      (fun v : ℕ × ℕ => ((N : ℤ)-(v.1 : ℤ)*v.2).natAbs)
      (goldbachG11RectangleWeight N) d =
    g9IntegerFibreDivisibility U V
      (fun m => (goldbachG11ProductCoefficient N ((N : ℝ)^(4/53 : ℝ))
        ((N : ℝ)^(4/33 : ℝ)) m : ℝ))
      (fun p => if p.Coprime N then primeSWBeta p else 0) N d := rfl

/-- The real G11 rectangular sifted count with the unchanged external family.
The main term retains its exact coprime density; the remainder is still on
primorial divisors, not yet the full-modulus distribution estimate. -/
theorem goldbachG11RectangleSiftedMass_external_upper
    (N : ℕ) (U V P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    {D θ z : ℝ} (hD : 2 ≤ D) (hθ : 0 < θ) (hθu : θ < 1/8)
    (hcut : ∀ p ∈ P, (p : ℝ) < z) :
    let α := fun m => (goldbachG11ProductCoefficient N ((N : ℝ)^(4/53 : ℝ))
      ((N : ℝ)^(4/33 : ℝ)) m : ℝ)
    let β := fun p => if p.Coprime N then primeSWBeta p else 0
    goldbachG11RectangleSiftedMass N U V P ≤
      (∑ m ∈ U, ∑ p ∈ V, α m*β p*externalDensity true P D θ z (progressionDensity (m*p))) +
      (∑ t ∈ externalTags true P D θ z, ∑ d ∈ (P.prod id).divisors,
        externalTerm true P D θ z t d * bilinearDiscrepancy U V α β N d) := by
  dsimp only
  have h := externalFamily_weighted_sequence_sieve_centered P hP hD hθ hθu hcut
    (U ×ˢ V) (fun v : ℕ × ℕ => ((N : ℤ)-(v.1 : ℤ)*v.2).natAbs)
    (goldbachG11RectangleWeight N) (fun v _ => goldbachG11RectangleWeight_nonneg N v)
    (g9IntegerFibreCenter U V
      (fun m => (goldbachG11ProductCoefficient N ((N : ℝ)^(4/53 : ℝ))
        ((N : ℝ)^(4/33 : ℝ)) m : ℝ))
      (fun p => if p.Coprime N then primeSWBeta p else 0))
  simp only [goldbachG11RectangleDivCount_eq, g9IntegerFibre_centered_eq,
    g9IntegerFibreCenter_externalDensity] at h
  exact h

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig