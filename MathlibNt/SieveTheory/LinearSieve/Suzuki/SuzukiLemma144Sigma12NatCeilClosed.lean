import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144CaseIICubicClosedEndpoint

open scoped Classical BigOperators Interval
open Finset MeasureTheory Set

namespace MathlibNt.SieveTheory

open LinearSieve SwitchingPrinciple
open SuzukiFiniteContinuousLayers
open SwitchingPrinciple.SuzukiLemma144Equation1410
open SwitchingPrinciple.SuzukiLemma144KappaOne

set_option maxHeartbeats 1200000

/-- Closed-endpoint rounded version of the concrete middle provider.  The
natural ceiling transports the strict carrier exactly, while the `Σ₁₂` input
allows equality at its lower endpoint. -/
theorem sigmaEleven_add_sigmaTwelve_suzukiVProduct_le_finiteSourceLayer_add_qD_natCeil_closed
    {S : BoundingSieve} {H : Section13HatLayers}
    {β C K d Δ s τ σ : ℝ} {N D z : ℕ}
    (hH : Section13HatContract H β)
    (hsdom : s ∈ KappaOneModel.parityDomain β N)
    (hτdom : τ - 1 ∈ KappaOneModel.parityDomain β (N - 1))
    (hsτ : s ≤ τ) (hτσ : τ ≤ σ)
    (hD : 1 < (D : ℝ)) (hz2 : 2 ≤ (z : ℝ))
    (hroot2 : 2 ≤ (D : ℝ) ^ (1 / s))
    (hv2 : 2 ≤ (D : ℝ) ^ (1 / τ))
    (hw2 : 2 ≤ (D : ℝ) ^ (1 / σ))
    (hwv : (D : ℝ) ^ (1 / σ) ≤ (D : ℝ) ^ (1 / τ))
    (hvroot : (D : ℝ) ^ (1 / τ) ≤ (D : ℝ) ^ (1 / s))
    (hzceil : z = ⌈(D : ℝ) ^ (1 / s)⌉₊)
    (hτerr : H.betaHat + (ErrorSign.ofDepth N).epsilon ≤ τ)
    (hK : 2 ≤ K) (hlocal : HasDimensionOneLocalProductBound S K)
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
    sigmaEleven (suzukiSupportedBelow S z) S.nu
        (fun p => suzukiVProduct S p) (suzukiVProduct S z)
        β N D σ τ +
      sigmaTwelve S.prodPrimes.primeFactors S.nu
        (fun p => suzukiVProduct S p)
        (fun n D' x => errorEnvelope H n (D' : ℝ) d x)
        (suzukiVProduct S z) C K Δ N D σ τ ≤
      suzukiVProduct S z *
        (finiteSourceLayer 1 β N s +
          (6 * K ^ 2 * finiteSourceLayer 1 β (N - 1) (τ - 1) /
            Real.log ((D : ℝ) ^ (1 / σ))) * (τ / s)) +
      C * Real.exp (Real.sqrt K) * suzukiVProduct S z *
        (Real.log (D : ℝ)) ^ (-Δ) *
        ((1 / s) * (∫ t in τ..σ,
            qD H (ErrorSign.ofDepth N).opposite (D : ℝ) d Δ t) +
          (6 * K ^ 2 *
              qD H (ErrorSign.ofDepth N).opposite (D : ℝ) d Δ τ /
            Real.log ((D : ℝ) ^ (1 / σ))) * (τ / s)) := by
  classical
  let w : ℝ := (D : ℝ) ^ (1 / σ)
  let v : ℝ := (D : ℝ) ^ (1 / τ)
  let r : ℝ := (D : ℝ) ^ (1 / s)
  have hDnat : 0 < D := by
    exact_mod_cast (show (0 : ℝ) < D by linarith)
  have hr : 0 < r := by
    exact natCast_rpow_one_div_pos hDnat s
  have hVz : suzukiVProduct S (z : ℝ) = suzukiVProduct S r :=
    suzukiVProduct_natCeil_eq_power S hr (by simpa [r] using hzceil)
  have hPrime : ∀ F : ℝ → ℝ,
      suzukiLemmaEightSevenPrimeSum S (D : ℝ) w v (z : ℝ) F =
        suzukiLemmaEightSevenPrimeSum S (D : ℝ) w v r F := by
    intro F
    unfold suzukiLemmaEightSevenPrimeSum
    apply Finset.sum_congr rfl
    intro p hp
    rw [suzukiSuffixCarrier_natCeil_eq_power S p hr
      (by simpa [r] using hzceil)]
  have h11 := sigma11_middle_le_finiteSourceLayer_add_endpoint
    (S := S) (D := (D : ℝ)) (z := r) (v := v) (w := w)
    (s := s) (τ := τ) (σ := σ) (K := K) (β := β) (N := N)
    hH.beta_gt_one hsdom hτdom hsτ hτσ hD hroot2 hv2 hw2 hwv hvroot
    rfl rfl rfl hK hlocal
  have h11scaled := mul_le_mul_of_nonneg_left h11
    (suzukiVProduct_pos S r).le
  have h11final :
      sigmaEleven (suzukiSupportedBelow S z) S.nu
          (fun p => suzukiVProduct S p) (suzukiVProduct S z)
          β N D σ τ ≤
        suzukiVProduct S z *
          (finiteSourceLayer 1 β N s +
            (6 * K ^ 2 * finiteSourceLayer 1 β (N - 1) (τ - 1) /
              Real.log w) * (τ / s)) := by
    have hrz : r ≤ (z : ℝ) :=
      (Nat.le_ceil r).trans_eq (congrArg Nat.cast hzceil).symm
    rw [sigmaEleven_eq_suzukiLemmaEightSevenPrimeSum S β σ τ w v N D z rfl rfl
      (hvroot.trans hrz)]
    rw [hPrime, hVz]
    exact h11scaled
  have h12final :=
    sigmaTwelve_suzukiVProduct_le_qD_lemma8_7_natCeil_closed
      (S := S) (H := H) (β := β) (C := C) (K := K) (d := d) (Δ := Δ)
      (w := w) (v := v) (s := s) (τ := τ) (σ := σ)
      (N := N) (D := D) (znat := z)
      hH hD hv2 hw2 hwv hvroot hzceil rfl rfl hτerr hτσ hK hlocal hii
      hC hΔ (by simpa [w, v] using hCeil) (by simpa [w, v] using hT)
      (by simpa [w, v] using h1413)
  simpa only [w, mul_assoc] using add_le_add h11final h12final

end MathlibNt.SieveTheory
