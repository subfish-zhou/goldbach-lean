import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiSigma11Sigma12MiddleRange

open scoped Classical BigOperators
open Finset MeasureTheory Set

namespace MathlibNt.SieveTheory.SwitchingPrinciple
namespace SuzukiLemma144KappaOne

open SuzukiLemma144Equation1410

set_option maxHeartbeats 800000

/-- The concrete Euler-product quotient occurring in `sigmaTwelve` is exactly
its Lemma-8.7 suffix product. -/
theorem suzukiVProduct_div_eq_suffix
    (S : BoundingSieve) {p : ℕ} {z : ℝ} (hpz : (p : ℝ) < z) :
    suzukiVProduct S (p : ℝ) / suzukiVProduct S z =
      ∏ q ∈ S.prodPrimes.primeFactors.filter
        (fun q : ℕ => p ≤ q ∧ (q : ℝ) < z), (1 - S.nu q)⁻¹ := by
  classical
  let B := S.prodPrimes.primeFactors.filter (fun q : ℕ => (q : ℝ) < z)
  let A := S.prodPrimes.primeFactors.filter (fun q : ℕ => (q : ℝ) < (p : ℝ))
  let C := S.prodPrimes.primeFactors.filter
    (fun q : ℕ => p ≤ q ∧ (q : ℝ) < z)
  have hA : B.filter (fun q : ℕ => (q : ℝ) < (p : ℝ)) = A := by
    ext q
    simp only [B, A, Finset.mem_filter]
    constructor
    · exact fun h => ⟨h.1.1, h.2⟩
    · rintro ⟨hq, hqp⟩
      exact ⟨⟨hq, hqp.trans hpz⟩, hqp⟩
  have hC : B.filter (fun q : ℕ => ¬ (q : ℝ) < (p : ℝ)) = C := by
    ext q
    simp only [B, C, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hq, hqz⟩, hnqp⟩
      exact ⟨hq, (by exact_mod_cast (le_of_not_gt hnqp) : p ≤ q), hqz⟩
    · rintro ⟨hq, hpq, hqz⟩
      exact ⟨⟨hq, hqz⟩, not_lt_of_ge (by exact_mod_cast hpq : (p : ℝ) ≤ (q : ℝ))⟩
  have hpartition :
      (∏ q ∈ B, (1 - S.nu q)) =
        (∏ q ∈ A, (1 - S.nu q)) * (∏ q ∈ C, (1 - S.nu q)) := by
    rw [← hA, ← hC]
    exact (Finset.prod_filter_mul_prod_filter_not B (fun q : ℕ => (q : ℝ) < (p : ℝ))
      (fun q => 1 - S.nu q)).symm
  have hAne : (∏ q ∈ A, (1 - S.nu q)) ≠ 0 :=
    (suzukiVProduct_pos S (p : ℝ)).ne'
  unfold suzukiVProduct
  change (∏ q ∈ A, (1 - S.nu q)) / (∏ q ∈ B, (1 - S.nu q)) =
    ∏ q ∈ C, (1 - S.nu q)⁻¹
  rw [Finset.prod_inv_distrib, hpartition, div_mul_eq_div_div, div_self hAne, one_div]

/-- Source-coordinate version of the natural-ceiling error estimate.  Unlike
`naturalCeil_error_le_claim14_13`, this is the form needed by the literal
`equation14_10.sigmaTwelve`, whose envelope is evaluated at the inherited
coordinate. -/
theorem naturalCeil_inherited_error_le_claim14_13
    (H : Section13HatLayers) {N D p : ℕ} {d Δ : ℝ}
    (hp : 2 ≤ p) (hDp : 2 * p ≤ D) (hΔ : 0 ≤ Δ)
    (hT : 0 ≤ H.T (ErrorSign.ofDepth (N - 1)) (inheritedCoordinate D p))
    (h1413 : Claim14_13PointwisePremise H N (D : ℝ) d Δ
      (Real.log (D : ℝ) / Real.log (p : ℝ)) ((D : ℝ) / (p : ℝ))) :
    errorEnvelope H (N - 1) ((D ⌈/⌉ p : ℕ) : ℝ) d
          (inheritedCoordinate D p) *
        (Real.log ((D ⌈/⌉ p : ℕ) : ℝ)) ^ (-Δ) ≤
      (Real.log (D : ℝ)) ^ (-Δ) *
        qD H (ErrorSign.ofDepth N).opposite (D : ℝ) d Δ
          (Real.log (D : ℝ) / Real.log (p : ℝ)) := by
  have hpR : (0 : ℝ) < (p : ℝ) := by positivity
  have hdiv2 : (2 : ℝ) ≤ (D : ℝ) / (p : ℝ) := by
    rw [le_div_iff₀ hpR]
    exact_mod_cast hDp
  have hceilLower : (D : ℝ) / (p : ℝ) ≤ ((D ⌈/⌉ p : ℕ) : ℝ) := by
    rw [div_le_iff₀ hpR]
    exact_mod_cast (ceilDiv_mul_bounds (D := D) (p := p) (by omega : 0 < p)).1
  have hlogdiv : 0 ≤ Real.log ((D : ℝ) / (p : ℝ)) :=
    (Real.log_pos (lt_of_lt_of_le (by norm_num) hdiv2)).le
  have hlogp : 0 < Real.log (p : ℝ) := Real.log_pos (by
    exact_mod_cast (show 1 < p by omega))
  have hinherited_nonneg : 0 ≤ inheritedCoordinate D p := by
    rw [inheritedCoordinate_eq_log_div D p (by omega) hp]
    exact div_nonneg hlogdiv hlogp.le
  have hcutoff := errorEnvelope_antitone_cutoff H (N - 1) (d := d)
    (lt_of_lt_of_le (by norm_num) hdiv2) hceilLower hinherited_nonneg hT
  have hceil2 : (2 : ℝ) ≤ ((D ⌈/⌉ p : ℕ) : ℝ) := hdiv2.trans hceilLower
  have herror_nonneg := errorEnvelope_nonneg H (N - 1) (d := d)
    (lt_of_lt_of_le (by norm_num) hceil2) hinherited_nonneg hT
  have hdivFactor : 0 ≤ (Real.log ((D : ℝ) / (p : ℝ))) ^ (-Δ) :=
    Real.rpow_nonneg hlogdiv _
  have hfactor := ceilDiv_log_rpow_neg_le_div_log_rpow_neg hp hDp hΔ
  have hsourceCoord :
      Real.log (D : ℝ) / Real.log (p : ℝ) - 1 = inheritedCoordinate D p := rfl
  calc
    errorEnvelope H (N - 1) ((D ⌈/⌉ p : ℕ) : ℝ) d
          (inheritedCoordinate D p) *
        (Real.log ((D ⌈/⌉ p : ℕ) : ℝ)) ^ (-Δ) ≤
      errorEnvelope H (N - 1) ((D ⌈/⌉ p : ℕ) : ℝ) d
          (inheritedCoordinate D p) *
        (Real.log ((D : ℝ) / (p : ℝ))) ^ (-Δ) :=
      mul_le_mul_of_nonneg_left hfactor herror_nonneg
    _ ≤ errorEnvelope H (N - 1) ((D : ℝ) / (p : ℝ)) d
          (inheritedCoordinate D p) *
        (Real.log ((D : ℝ) / (p : ℝ))) ^ (-Δ) :=
      mul_le_mul_of_nonneg_right hcutoff hdivFactor
    _ ≤ (Real.log (D : ℝ)) ^ (-Δ) *
        qD H (ErrorSign.ofDepth N).opposite (D : ℝ) d Δ
          (Real.log (D : ℝ) / Real.log (p : ℝ)) := by
      rw [← hsourceCoord]
      exact h1413


end SuzukiLemma144KappaOne
end MathlibNt.SieveTheory.SwitchingPrinciple
