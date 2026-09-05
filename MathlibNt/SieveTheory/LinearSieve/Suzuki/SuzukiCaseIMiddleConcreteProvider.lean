import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiSigmaElevenPrimeSumIdentification
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiSigmaTwelveGlobalScaling

open scoped Classical BigOperators
open MeasureTheory Set

namespace MathlibNt.SieveTheory.SwitchingPrinciple
namespace SuzukiLemma144KappaOne

open SuzukiLemma144Equation1410
open SuzukiFiniteContinuousLayers

set_option maxHeartbeats 800000

/-- Concrete middle-range provider for the literal `Σ₁₁ + Σ₁₂` terms from
(14.10).  Both terms use Suzuki's Euler product, and the error term is the
Section-13 envelope; there is no abstract middle-range or reverse-error
premise. -/
theorem sigmaEleven_add_sigmaTwelve_suzukiVProduct_le_finiteSourceLayer_add_qD
    {S : BoundingSieve} {H : Section13HatLayers}
    {β C K d Δ s τ σ : ℝ} {N D znat : ℕ}
    (hH : Section13HatContract H β)
    (hsdom : s ∈ KappaOneModel.parityDomain β N)
    (hτdom : τ - 1 ∈ KappaOneModel.parityDomain β (N - 1))
    (hsτ : s ≤ τ) (hτσ : τ ≤ σ)
    (hD : 1 < (D : ℝ)) (hz2 : 2 ≤ (znat : ℝ))
    (hv2 : 2 ≤ (D : ℝ) ^ (1 / τ))
    (hw2 : 2 ≤ (D : ℝ) ^ (1 / σ))
    (hwv : (D : ℝ) ^ (1 / σ) ≤ (D : ℝ) ^ (1 / τ))
    (hvz : (D : ℝ) ^ (1 / τ) ≤ (znat : ℝ))
    (hz : (znat : ℝ) = (D : ℝ) ^ (1 / s))
    (hτ : H.betaHat + (ErrorSign.ofDepth N).epsilon < τ)
    (hK : 2 ≤ K)
    (hlocal : HasDimensionOneLocalProductBound S K)
    (hii : Claim14_6_MonotoneQPremise H (D : ℝ) d Δ σ)
    (hC : 0 ≤ C) (hΔ : 0 ≤ Δ)
    (hCeil : ∀ p ∈ S.prodPrimes.primeFactors,
      (D : ℝ) ^ (1 / σ) ≤ (p : ℝ) →
      (p : ℝ) < (D : ℝ) ^ (1 / τ) → 2 ≤ p ∧ 2 * p ≤ D)
    (hT : ∀ p ∈ S.prodPrimes.primeFactors,
      (D : ℝ) ^ (1 / σ) ≤ (p : ℝ) →
      (p : ℝ) < (D : ℝ) ^ (1 / τ) →
      0 ≤ H.T (ErrorSign.ofDepth (N - 1)) (inheritedCoordinate D p))
    (h1413 : ∀ p ∈ S.prodPrimes.primeFactors,
      (D : ℝ) ^ (1 / σ) ≤ (p : ℝ) →
      (p : ℝ) < (D : ℝ) ^ (1 / τ) →
      Claim14_13PointwisePremise H N (D : ℝ) d Δ
        (Real.log (D : ℝ) / Real.log (p : ℝ)) ((D : ℝ) / (p : ℝ))) :
    sigmaEleven (suzukiSupportedBelow S znat) S.nu
        (fun p => suzukiVProduct S p) (suzukiVProduct S znat)
        β N D σ τ +
      sigmaTwelve S.prodPrimes.primeFactors S.nu
        (fun p => suzukiVProduct S p)
        (fun n D' x => errorEnvelope H n (D' : ℝ) d x)
        (suzukiVProduct S znat) C K Δ N D σ τ ≤
      suzukiVProduct S znat *
        (finiteSourceLayer 1 β N s +
          (6 * K ^ 2 * finiteSourceLayer 1 β (N - 1) (τ - 1) /
            Real.log ((D : ℝ) ^ (1 / σ))) * (τ / s)) +
      C * Real.exp (Real.sqrt K) * suzukiVProduct S znat *
        (Real.log (D : ℝ)) ^ (-Δ) *
        ((1 / s) * (∫ t in τ..σ,
            qD H (ErrorSign.ofDepth N).opposite (D : ℝ) d Δ t) +
          (6 * K ^ 2 *
              qD H (ErrorSign.ofDepth N).opposite (D : ℝ) d Δ τ /
            Real.log ((D : ℝ) ^ (1 / σ))) * (τ / s)) := by
  let w : ℝ := (D : ℝ) ^ (1 / σ)
  let v : ℝ := (D : ℝ) ^ (1 / τ)
  have h11 := sigma11_middle_le_finiteSourceLayer_add_endpoint
    (S := S) (D := (D : ℝ)) (z := (znat : ℝ)) (v := v) (w := w)
    (s := s) (τ := τ) (σ := σ) (K := K) (β := β) (N := N)
    hH.beta_gt_one hsdom hτdom hsτ hτσ hD hz2 hv2 hw2 hwv hvz
    hz rfl rfl hK hlocal
  have h11scaled := mul_le_mul_of_nonneg_left h11
    (suzukiVProduct_pos S (znat : ℝ)).le
  have h12 := sigmaTwelve_suzukiVProduct_le_qD_lemma8_7
    (S := S) (H := H) (β := β) (C := C) (K := K) (d := d) (Δ := Δ)
    (w := w) (v := v) (s := s) (τ := τ) (σ := σ)
    (N := N) (D := D) (znat := znat)
    hH hD hz2 hv2 hw2 hwv hvz hz rfl rfl hτ hτσ hK hlocal hii
    hC hΔ hCeil hT h1413
  have h12' :
      sigmaTwelve S.prodPrimes.primeFactors S.nu
          (fun p => suzukiVProduct S p)
          (fun n D' x => errorEnvelope H n (D' : ℝ) d x)
          (suzukiVProduct S znat) C K Δ N D σ τ ≤
        C * Real.exp (Real.sqrt K) * suzukiVProduct S znat *
          (Real.log (D : ℝ)) ^ (-Δ) *
          ((1 / s) * (∫ t in τ..σ,
              qD H (ErrorSign.ofDepth N).opposite (D : ℝ) d Δ t) +
            (6 * K ^ 2 *
                qD H (ErrorSign.ofDepth N).opposite (D : ℝ) d Δ τ /
              Real.log ((D : ℝ) ^ (1 / σ))) * (τ / s)) := by
    simpa only [w, mul_assoc] using h12
  rw [sigmaEleven_eq_suzukiLemmaEightSevenPrimeSum
    S β σ τ w v N D znat rfl rfl hvz]
  exact add_le_add h11scaled h12'

end SuzukiLemma144KappaOne
end MathlibNt.SieveTheory.SwitchingPrinciple
