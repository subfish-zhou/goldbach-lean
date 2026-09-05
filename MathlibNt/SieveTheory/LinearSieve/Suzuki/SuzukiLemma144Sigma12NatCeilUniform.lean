import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144Sigma12NatCeil
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144Sigma12NatCeilClosed
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiClaim146FullInternal
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiClaim1413Internal

open scoped Classical BigOperators Interval
open Finset MeasureTheory Set

namespace MathlibNt.SieveTheory

open LinearSieve SwitchingPrinciple
open SuzukiFiniteContinuousLayers
open SwitchingPrinciple.SuzukiLemma144Equation1410
open SwitchingPrinciple.SuzukiLemma144KappaOne
open SwitchingPrinciple.SuzukiLemma144KappaOne.Section13QhatMajorantClosure

set_option maxHeartbeats 1600000

/-! A quantifier-order strengthening of the internal `Σ₁₂` contraction.  The
large-`D` threshold comes only from the full moving Claim 14.6 source assembly,
so it is chosen before, and is uniform in, the depth `N` and coordinate `s`. -/

/-- The natural-ceiling `Σ₁₂` same-constant contraction with one threshold
uniform in both the induction depth `N` and the coordinate `s`. -/
theorem eventually_sigmaTwelve_internal_contraction_sameC_uniform
    {S : BoundingSieve} {H : Section13HatLayers}
    {C K d Δ : ℝ}
    (hH : Section13HatSourceContract H)
    (hd1 : 1 < d) (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1)
    (hK : 2 ≤ K) (hlocal : HasDimensionOneLocalProductBound S K)
    (hC : 0 ≤ C) :
    ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ D : ℕ, D₀ ≤ (D : ℝ) →
      ∀ (N : ℕ) (s : ℝ) (z : ℕ),
      2 ≤ N →
      0 < s →
      2 + (ErrorSign.ofDepth N).epsilon ≤ s →
      1 < sourceSigma (D : ℝ) d →
      s ≤ sourceSigma (D : ℝ) d →
      1 < (D : ℝ) →
      2 ≤ (D : ℝ) ^ (1 / s) →
      2 ≤ (D : ℝ) ^ (1 / sourceSigma (D : ℝ) d) →
      (D : ℝ) ^ (1 / sourceSigma (D : ℝ) d) ≤ (D : ℝ) ^ (1 / s) →
      z = ⌈(D : ℝ) ^ (1 / s)⌉₊ →
      H.betaHat + (ErrorSign.ofDepth N).epsilon ≤ s →
      (∀ p ∈ S.prodPrimes.primeFactors,
        (D : ℝ) ^ (1 / sourceSigma (D : ℝ) d) ≤ (p : ℝ) →
        (p : ℝ) < (D : ℝ) ^ (1 / s) → 2 ≤ p ∧ 2 * p ≤ D) →
      (∀ p ∈ S.prodPrimes.primeFactors,
        (D : ℝ) ^ (1 / sourceSigma (D : ℝ) d) ≤ (p : ℝ) →
        (p : ℝ) < (D : ℝ) ^ (1 / s) →
        0 ≤ H.T (ErrorSign.ofDepth (N - 1)) (inheritedCoordinate D p)) →
      ∃ q : Lemma144StrictFactor,
        q.ρ = (1 + sigma12ContractionMultiplier (sourceSigma (D : ℝ) d) Δ) / 2 ∧
        sigmaTwelve S.prodPrimes.primeFactors S.nu
            (fun p => suzukiVProduct S (p : ℝ))
            (fun n D' x => errorEnvelope H n (D' : ℝ) d x)
            (suzukiVProduct S (z : ℝ)) C K Δ N D
            (sourceSigma (D : ℝ) d) s ≤
          sigma12ContractionMultiplier (sourceSigma (D : ℝ) d) Δ *
              sigma12InheritedBudget S H N D z C K d Δ s +
            sigma12EndpointRemainder S H N D z C K d Δ s
              (sourceSigma (D : ℝ) d) ∧
        sigmaTwelve S.prodPrimes.primeFactors S.nu
            (fun p => suzukiVProduct S (p : ℝ))
            (fun n D' x => errorEnvelope H n (D' : ℝ) d x)
            (suzukiVProduct S (z : ℝ)) C K Δ N D
            (sourceSigma (D : ℝ) d) s ≤
          q.ρ * sigma12InheritedBudget S H N D z C K d Δ s +
            sigma12EndpointRemainder S H N D z C K d Δ s
              (sourceSigma (D : ℝ) d) := by
  obtain ⟨D₀, hD₀, h146⟩ :=
    eventually_claim14_6_full_internal_at_sourceSigma hH hd1 hΔ0 hΔ1
  refine ⟨D₀, hD₀, ?_⟩
  intro D hDlarge N s z hN2 hs0 hsLower hσ1 hsσ hD hv2 hw2 hwv hz hthreshold
    hCeil hT
  obtain ⟨_hi, hii, hiii⟩ := h146 (D : ℝ) hDlarge
  let σ : ℝ := sourceSigma (D : ℝ) d
  let a : ℝ := sigma12ContractionMultiplier σ Δ
  let A : ℝ := C * Real.exp (Real.sqrt K) * suzukiVProduct S (z : ℝ) *
    (Real.log (D : ℝ)) ^ (-Δ)
  let B : ℝ := errorEnvelope H N (D : ℝ) d s
  let R : ℝ := (6 * K ^ 2 * qD H (ErrorSign.ofDepth N).opposite
      (D : ℝ) d Δ s / Real.log ((D : ℝ) ^ (1 / σ))) * (s / s)
  have h12 := sigmaTwelve_suzukiVProduct_le_qD_lemma8_7_natCeil_closed
    (S := S) (H := H) (β := (2 : ℝ)) (C := C) (K := K) (d := d) (Δ := Δ)
    (w := (D : ℝ) ^ (1 / σ)) (v := (D : ℝ) ^ (1 / s))
    (s := s) (τ := s) (σ := σ) (N := N) (D := D) (znat := z)
    hH.toSection13HatContract hD hv2 hw2 hwv le_rfl hz rfl rfl
    hthreshold hsσ hK hlocal (by simpa [σ] using hii) hC hΔ0.le
    (by simpa [σ] using hCeil) (by simpa [σ] using hT)
    (by
      intro p hp hpw hpv
      have hcp := hCeil p hp hpw hpv
      exact claim14_13_pointwise_carrier H (by omega) hcp.1 hcp.2 hd1 hΔ0
        (hT p hp hpw hpv))
  have hint := hiii (ErrorSign.ofDepth N) s hsLower hsσ
  have hintScaled :
      (1 / s) * (∫ t in s..σ,
        qD H (ErrorSign.ofDepth N).opposite (D : ℝ) d Δ t) ≤ a * B := by
    have hmul := mul_le_mul_of_nonneg_left hint.le (one_div_nonneg.mpr hs0.le)
    calc
      (1 / s) * (∫ t in s..σ,
          qD H (ErrorSign.ofDepth N).opposite (D : ℝ) d Δ t) ≤
          (1 / s) * (a * lambda H (ErrorSign.ofDepth N) (D : ℝ) d 0 s) := by
            simpa [σ, a, sigma12ContractionMultiplier] using hmul
      _ = a * ((1 / s) * lambda H (ErrorSign.ofDepth N) (D : ℝ) d 0 s) := by ring
      _ = a * B := by rw [one_div_mul_lambda_eq_errorEnvelope H hs0]
  have hA : 0 ≤ A := by
    dsimp [A]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg hC (Real.exp_nonneg _)) (suzukiVProduct_pos S (z : ℝ)).le)
      (Real.rpow_nonneg (Real.log_nonneg hD.le) _)
  have hraw :
      sigmaTwelve S.prodPrimes.primeFactors S.nu
          (fun p => suzukiVProduct S (p : ℝ))
          (fun n D' x => errorEnvelope H n (D' : ℝ) d x)
          (suzukiVProduct S (z : ℝ)) C K Δ N D σ s ≤
        a * (A * B) + A * R := by
    apply h12.trans
    rw [show C * Real.exp (Real.sqrt K) * suzukiVProduct S (z : ℝ) *
        ((Real.log (D : ℝ)) ^ (-Δ) *
          ((1 / s) * (∫ t in s..σ,
            qD H (ErrorSign.ofDepth N).opposite (D : ℝ) d Δ t) +
            (6 * K ^ 2 * qD H (ErrorSign.ofDepth N).opposite
              (D : ℝ) d Δ s / Real.log ((D : ℝ) ^ (1 / σ))) * (s / s))) =
        A * ((1 / s) * (∫ t in s..σ,
          qD H (ErrorSign.ofDepth N).opposite (D : ℝ) d Δ t) + R) by
            dsimp [A, R]; ring]
    have hinside :
        (1 / s) * (∫ t in s..σ,
          qD H (ErrorSign.ofDepth N).opposite (D : ℝ) d Δ t) + R ≤
          a * B + R := add_le_add hintScaled (le_refl R)
    calc
      A * ((1 / s) * (∫ t in s..σ,
          qD H (ErrorSign.ofDepth N).opposite (D : ℝ) d Δ t) + R) ≤
          A * (a * B + R) := mul_le_mul_of_nonneg_left hinside hA
      _ = a * (A * B) + A * R := by ring
  obtain ⟨q, hq, haq⟩ := exists_sigma12_sameC_strictFactor hσ1 hΔ1
  have hB : 0 ≤ B := by
    apply errorEnvelope_nonneg H N hD hs0.le
    exact (hH.positive (ErrorSign.ofDepth N) s hs0).le
  have hbudget : 0 ≤ A * B := mul_nonneg hA hB
  refine ⟨q, by simpa [σ] using hq, ?_, ?_⟩
  · simpa [σ, a, A, B, R, sigma12InheritedBudget,
      sigma12EndpointRemainder, mul_assoc] using hraw
  · have hρ : a ≤ q.ρ := haq.le
    have hslack : a * (A * B) + A * R ≤ q.ρ * (A * B) + A * R := by
      exact add_le_add (mul_le_mul_of_nonneg_right hρ hbudget) le_rfl
    have hfinal := hraw.trans hslack
    simpa [σ, a, A, B, R, sigma12InheritedBudget,
      sigma12EndpointRemainder, mul_assoc] using hfinal


end MathlibNt.SieveTheory
