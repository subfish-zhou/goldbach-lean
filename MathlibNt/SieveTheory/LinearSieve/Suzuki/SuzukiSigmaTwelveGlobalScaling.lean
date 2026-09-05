import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144Equation1410
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiSigma11Sigma12MiddleRange
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144BaseOne

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
  have hAne : (∏ q ∈ A, (1 - S.nu q)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro q hq
    have hqS : q ∈ S.prodPrimes.primeFactors := (Finset.mem_filter.mp hq).1
    have hqprime : q.Prime := Nat.prime_of_mem_primeFactors hqS
    have hqdiv : q ∣ S.prodPrimes := (Nat.mem_primeFactors.mp hqS).2.1
    exact ne_of_gt (sub_pos.mpr (S.nu_lt_one_of_prime q hqprime hqdiv))
  have hCne : (∏ q ∈ C, (1 - S.nu q)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro q hq
    have hqS : q ∈ S.prodPrimes.primeFactors := (Finset.mem_filter.mp hq).1
    have hqprime : q.Prime := Nat.prime_of_mem_primeFactors hqS
    have hqdiv : q ∣ S.prodPrimes := (Nat.mem_primeFactors.mp hqS).2.1
    exact ne_of_gt (sub_pos.mpr (S.nu_lt_one_of_prime q hqprime hqdiv))
  unfold suzukiVProduct
  change (∏ q ∈ A, (1 - S.nu q)) / (∏ q ∈ B, (1 - S.nu q)) =
    ∏ q ∈ C, (1 - S.nu q)⁻¹
  rw [Finset.prod_inv_distrib, hpartition]
  field_simp [hAne, hCne]

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

/-- Global scaling closure of the concrete `sigmaTwelve` from (14.10), followed
by the exact integral-plus-endpoint conclusion of qD Lemma 8.7. -/
theorem sigmaTwelve_suzukiVProduct_le_qD_lemma8_7
    {S : BoundingSieve} {H : Section13HatLayers}
    {β C K d Δ w v s τ σ : ℝ} {N D znat : ℕ}
    (hH : Section13HatContract H β)
    (hD : 1 < (D : ℝ)) (hz2 : 2 ≤ (znat : ℝ))
    (hv2 : 2 ≤ v) (hw2 : 2 ≤ w)
    (hwv : w ≤ v) (hvz : v ≤ (znat : ℝ))
    (hz : (znat : ℝ) = (D : ℝ) ^ (1 / s))
    (hv : v = (D : ℝ) ^ (1 / τ))
    (hw : w = (D : ℝ) ^ (1 / σ))
    (hτ : H.betaHat + (ErrorSign.ofDepth N).epsilon < τ)
    (hτσ : τ ≤ σ) (hK : 2 ≤ K)
    (hlocal : HasDimensionOneLocalProductBound S K)
    (hii : Claim14_6_MonotoneQPremise H (D : ℝ) d Δ σ)
    (hC : 0 ≤ C) (hΔ : 0 ≤ Δ)
    (hCeil : ∀ p ∈ S.prodPrimes.primeFactors,
      w ≤ (p : ℝ) → (p : ℝ) < v → 2 ≤ p ∧ 2 * p ≤ D)
    (hT : ∀ p ∈ S.prodPrimes.primeFactors,
      w ≤ (p : ℝ) → (p : ℝ) < v →
      0 ≤ H.T (ErrorSign.ofDepth (N - 1)) (inheritedCoordinate D p))
    (h1413 : ∀ p ∈ S.prodPrimes.primeFactors,
      w ≤ (p : ℝ) → (p : ℝ) < v →
      Claim14_13PointwisePremise H N (D : ℝ) d Δ
        (Real.log (D : ℝ) / Real.log (p : ℝ)) ((D : ℝ) / (p : ℝ))) :
    sigmaTwelve S.prodPrimes.primeFactors S.nu
        (fun p => suzukiVProduct S (p : ℝ))
        (fun n D' x => errorEnvelope H n (D' : ℝ) d x)
        (suzukiVProduct S (znat : ℝ)) C K Δ N D σ τ ≤
      C * Real.exp (Real.sqrt K) * suzukiVProduct S (znat : ℝ) *
        ((Real.log (D : ℝ)) ^ (-Δ) *
          ((1 / s) * (∫ t in τ..σ,
              qD H (ErrorSign.ofDepth N).opposite (D : ℝ) d Δ t) +
            (6 * K ^ 2 *
                qD H (ErrorSign.ofDepth N).opposite (D : ℝ) d Δ τ /
              Real.log w) * (τ / s))) := by
  classical
  let Q : ℝ → ℝ := qD H (ErrorSign.ofDepth N).opposite (D : ℝ) d Δ
  have hcarrier : sigmaOneCarrier S.prodPrimes.primeFactors D σ τ =
      S.prodPrimes.primeFactors.filter
        (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < v) := by
    ext p
    simp only [sigmaOneCarrier, Finset.mem_filter]
    rw [hw, hv]
  have hsum :
      (∑ p ∈ sigmaOneCarrier S.prodPrimes.primeFactors D σ τ,
        S.nu p * suzukiVProduct S (p : ℝ) / suzukiVProduct S (znat : ℝ) *
          errorEnvelope H (N - 1) ((D ⌈/⌉ p : ℕ) : ℝ) d
            (inheritedCoordinate D p) *
          Real.log ((D ⌈/⌉ p : ℕ) : ℝ) ^ (-Δ)) ≤
        (Real.log (D : ℝ)) ^ (-Δ) *
          suzukiLemmaEightSevenPrimeSum S (D : ℝ) w v (znat : ℝ) Q := by
    rw [hcarrier]
    unfold suzukiLemmaEightSevenPrimeSum
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p hp
    have hp' := Finset.mem_filter.mp hp
    have hpz : (p : ℝ) < (znat : ℝ) := hp'.2.2.trans_le hvz
    have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hp'.1
    have hpdiv : p ∣ S.prodPrimes := (Nat.mem_primeFactors.mp hp'.1).2.1
    have hnu : 0 ≤ S.nu p := (S.nu_pos_of_prime p hpprime hpdiv).le
    have hsuffix : 0 ≤ ∏ q ∈ S.prodPrimes.primeFactors.filter
        (fun q : ℕ => p ≤ q ∧ (q : ℝ) < (znat : ℝ)), (1 - S.nu q)⁻¹ := by
      apply Finset.prod_nonneg
      intro q hq
      have hq' := Finset.mem_filter.mp hq
      have hqprime : q.Prime := Nat.prime_of_mem_primeFactors hq'.1
      have hqdiv : q ∣ S.prodPrimes := (Nat.mem_primeFactors.mp hq'.1).2.1
      exact inv_nonneg.mpr
        (sub_nonneg.mpr (S.nu_lt_one_of_prime q hqprime hqdiv).le)
    have herr := naturalCeil_inherited_error_le_claim14_13 H
      (hCeil p hp'.1 hp'.2.1 hp'.2.2).1
      (hCeil p hp'.1 hp'.2.1 hp'.2.2).2 hΔ
      (hT p hp'.1 hp'.2.1 hp'.2.2)
      (h1413 p hp'.1 hp'.2.1 hp'.2.2)
    rw [show S.nu p * suzukiVProduct S (p : ℝ) /
        suzukiVProduct S (znat : ℝ) =
        S.nu p * (suzukiVProduct S (p : ℝ) /
          suzukiVProduct S (znat : ℝ)) by ring]
    rw [suzukiVProduct_div_eq_suffix S hpz]
    dsimp [Q]
    have hmul := mul_le_mul_of_nonneg_left herr (mul_nonneg hnu hsuffix)
    nlinarith
  have houter : 0 ≤ C * Real.exp (Real.sqrt K) * suzukiVProduct S (znat : ℝ) :=
    mul_nonneg (mul_nonneg hC (Real.exp_nonneg _)) (suzukiVProduct_pos S _).le
  unfold sigmaTwelve
  apply (mul_le_mul_of_nonneg_left hsum houter).trans
  apply mul_le_mul_of_nonneg_left _ houter
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (Real.log_nonneg hD.le) _)
  exact sigma12_middle_le_qD_lemma8_7 (S := S) (H := H)
    (ErrorSign.ofDepth N) Q (fun p hp hpw hpv => le_rfl)
    hH hD hz2 hv2 hw2 hwv hvz hz hv hw hτ hτσ hK hlocal hii


end SuzukiLemma144KappaOne
end MathlibNt.SieveTheory.SwitchingPrinciple
