import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144Equation1410
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma87DimensionOne
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiVOneNaturalBridge

open scoped Classical BigOperators
open Finset

namespace MathlibNt.SieveTheory.SwitchingPrinciple
namespace SuzukiLemma144Equation1410

open SuzukiFiniteContinuousLayers

set_option maxHeartbeats 800000

/-- Exact identification of the main term `Σ₁₁` from equation (14.10) with
Suzuki's genuine Lemma-8.7 middle-range prime sum.

The finite carrier is the supported set below the natural cutoff `znat`.
The hypothesis `v ≤ znat` makes this support restriction redundant on the
middle range `w ≤ p < v`.  Termwise, positivity of `V(znat)` allows the
normalization `V(p) / V(znat)` to be identified with the exact Euler suffix
over `p ≤ q < znat`; no abstract ratio hypothesis is used. -/
theorem sigmaEleven_eq_suzukiLemmaEightSevenPrimeSum
    (S : BoundingSieve) (β σ τ w v : ℝ) (N D znat : ℕ)
    (hw : w = (D : ℝ) ^ (1 / σ))
    (hv : v = (D : ℝ) ^ (1 / τ))
    (hvz : v ≤ (znat : ℝ)) :
    sigmaEleven (suzukiSupportedBelow S znat) S.nu
        (fun p => suzukiVProduct S p) (suzukiVProduct S znat)
        β N D σ τ =
      suzukiVProduct S znat *
        suzukiLemmaEightSevenPrimeSum S (D : ℝ) w v (znat : ℝ)
          (fun t => finiteSourceLayer 1 β (N - 1) (t - 1)) := by
  classical
  have hcarrier :
      sigmaOneCarrier (suzukiSupportedBelow S znat) D σ τ =
        S.prodPrimes.primeFactors.filter
          (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < v) := by
    ext p
    simp only [sigmaOneCarrier, suzukiSupportedBelow, Finset.mem_filter]
    rw [← hw, ← hv]
    constructor
    · rintro ⟨⟨hpS, _hpz⟩, hpw, hpv⟩
      exact ⟨hpS, hpw, hpv⟩
    · rintro ⟨hpS, hpw, hpv⟩
      have hpzR : (p : ℝ) < (znat : ℝ) := hpv.trans_le hvz
      have hpz : p < znat := by exact_mod_cast hpzR
      exact ⟨⟨hpS, hpz⟩, hpw, hpv⟩
  unfold sigmaEleven suzukiLemmaEightSevenPrimeSum
  rw [hcarrier]
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  have hp' := Finset.mem_filter.mp hp
  have hpz : (p : ℝ) < (znat : ℝ) := hp'.2.2.trans_le hvz
  have hprod :
      suzukiVProduct S znat * suzukiLocalRatio S (p : ℝ) (znat : ℝ) =
        suzukiVProduct S p := by
    rw [suzukiVProduct_mul_localRatio_eq_sourceDiscreteEuler S hpz]
    unfold sourceDiscreteEuler suzukiVProduct suzukiSupportedBelow
    congr 1
    ext q
    simp
  have hratio :
      suzukiVProduct S p / suzukiVProduct S znat =
        suzukiLocalRatio S (p : ℝ) (znat : ℝ) := by
    apply (div_eq_iff (ne_of_gt (suzukiVProduct_pos S znat))).2
    simpa [mul_comm] using hprod.symm
  have hsuffix :
      (∏ q ∈ S.prodPrimes.primeFactors.filter
          (fun q : ℕ => p ≤ q ∧ (q : ℝ) < (znat : ℝ)),
        (1 - S.nu q)⁻¹) =
        suzukiLocalRatio S (p : ℝ) (znat : ℝ) := by
    unfold suzukiLocalRatio
    congr 2
    ext q
    simp
  simp only
  rw [mul_div_assoc, hratio, hsuffix]
  rfl

end SuzukiLemma144Equation1410
end MathlibNt.SieveTheory.SwitchingPrinciple
