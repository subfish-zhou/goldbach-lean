import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144Equation1410
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiSigma11Sigma12MiddleRange
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma87FiniteSourceRecursion
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiSigmaTwelveGlobalScaling
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144BaseOne
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiDiscreteParityRecurrence

open scoped Classical BigOperators Interval
open Finset MeasureTheory Set

namespace MathlibNt.SieveTheory
namespace SwitchingPrinciple
namespace SuzukiLemma144KappaOne

open SuzukiFiniteContinuousLayers
open SuzukiLemma144Equation1410

set_option maxHeartbeats 1200000

/-- Equation (14.11), with the finite Euler quotient expanded into the exact
Lemma-8.7 suffix.  The upper prime carrier is `v`; `z` remains the independent
Euler-product cutoff. -/
theorem sigmaEleven_eq_lemmaEightSevenPrimeSum
    (S : BoundingSieve) (β σ τ w v : ℝ) (N D z : ℕ)
    (hw : w = (D : ℝ) ^ (1 / σ))
    (hv : v = (D : ℝ) ^ (1 / τ))
    (hvz : v ≤ (z : ℝ)) :
    sigmaEleven (suzukiSupportedBelow S z) S.nu
        (fun p => suzukiVProduct S p) (suzukiVProduct S z)
        β N D σ τ =
      suzukiVProduct S z *
        suzukiLemmaEightSevenPrimeSum S (D : ℝ) w v (z : ℝ)
          (fun t => finiteSourceLayer 1 β (N - 1) (t - 1)) := by
  classical
  unfold sigmaEleven
  apply congrArg (fun x : ℝ => suzukiVProduct S z * x)
  unfold suzukiLemmaEightSevenPrimeSum sigmaOneCarrier
  apply Finset.sum_congr
  · ext p
    simp only [suzukiSupportedBelow, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hpS, hpz⟩, hpw, hpv⟩
      exact ⟨hpS, by simpa [one_div, hw] using hpw,
        by simpa [one_div, hv] using hpv⟩
    · rintro ⟨hpS, hpw, hpv⟩
      refine ⟨⟨hpS, ?_⟩, by simpa [one_div, hw] using hpw,
        by simpa [one_div, hv] using hpv⟩
      exact_mod_cast hpv.trans_le hvz
  · intro p hp
    have hp' := Finset.mem_filter.mp hp
    have hpz : (p : ℝ) < (z : ℝ) := hp'.2.2.trans_le hvz
    rw [show S.nu p * suzukiVProduct S (p : ℝ) / suzukiVProduct S (z : ℝ) =
      S.nu p * (suzukiVProduct S (p : ℝ) / suzukiVProduct S (z : ℝ)) by ring]
    rw [suzukiVProduct_div_eq_suffix S hpz]
    congr 1

/-- Strict finite carriers, Euler products, and Lemma-8.7 suffixes are unchanged
when the real cutoff is replaced by its natural ceiling. -/
theorem sigmaEleven_eq_lemmaEightSevenPrimeSum_natCeil
    (S : BoundingSieve) (β σ τ w v r : ℝ) (N D z : ℕ)
    (hw : w = (D : ℝ) ^ (1 / σ))
    (hv : v = (D : ℝ) ^ (1 / τ))
    (hvr : v ≤ r) (hz : z = ⌈r⌉₊) :
    sigmaEleven (suzukiSupportedBelow S z) S.nu
        (fun p => suzukiVProduct S p) (suzukiVProduct S z)
        β N D σ τ =
      suzukiVProduct S z *
        suzukiLemmaEightSevenPrimeSum S (D : ℝ) w v r
          (fun t => finiteSourceLayer 1 β (N - 1) (t - 1)) := by
  have hrz : r ≤ (z : ℝ) :=
    (Nat.le_ceil r).trans_eq (congrArg Nat.cast hz).symm
  rw [sigmaEleven_eq_lemmaEightSevenPrimeSum S β σ τ w v N D z hw hv
    (hvr.trans hrz)]
  apply congrArg (fun x : ℝ => suzukiVProduct S z * x)
  classical
  unfold suzukiLemmaEightSevenPrimeSum
  apply Finset.sum_congr rfl
  intro p hp
  have hcarrier :
      S.prodPrimes.primeFactors.filter
          (fun q : ℕ => p ≤ q ∧ (q : ℝ) < (z : ℝ)) =
        S.prodPrimes.primeFactors.filter
          (fun q : ℕ => p ≤ q ∧ (q : ℝ) < r) := by
    ext q
    simp only [Finset.mem_filter]
    rw [Nat.cast_lt, hz, Nat.lt_ceil]
  rw [hcarrier]

/-- Internalized Case-I `hSigma11`.  Lemma 8.7 gives the main integral plus its
(14.12) endpoint remainder; the finite (9.2) recurrence bounds that integral by
`T_N(s)`.  Thus neither a `mainSum`/finite-layer identification nor a packaged
middle-endpoint estimate is a premise. -/
theorem caseI_sigmaEleven_le_finiteSourceLayer_add_endpoint
    {S : BoundingSieve} {β s τ σ K : ℝ} {N D z : ℕ}
    (hβ : 1 < β)
    (hsdom : s ∈ KappaOneModel.parityDomain β N)
    (hτdom : τ - 1 ∈ KappaOneModel.parityDomain β (N - 1))
    (hsτ : s ≤ τ) (hτσ : τ ≤ σ)
    (hD : 1 < (D : ℝ))
    (hroot2 : 2 ≤ (D : ℝ) ^ (1 / s))
    (hv2 : 2 ≤ (D : ℝ) ^ (1 / τ))
    (hw2 : 2 ≤ (D : ℝ) ^ (1 / σ))
    (hwv : (D : ℝ) ^ (1 / σ) ≤ (D : ℝ) ^ (1 / τ))
    (hvroot : (D : ℝ) ^ (1 / τ) ≤ (D : ℝ) ^ (1 / s))
    (hz : z = ⌈(D : ℝ) ^ (1 / s)⌉₊)
    (hK : 2 ≤ K) (hlocal : HasDimensionOneLocalProductBound S K) :
    sigmaEleven (suzukiSupportedBelow S z) S.nu
        (fun p => suzukiVProduct S p) (suzukiVProduct S z)
        β N D σ τ ≤
      suzukiVProduct S z * finiteSourceLayer 1 β N s +
        suzukiVProduct S z *
          ((6 * K ^ 2 * finiteSourceLayer 1 β (N - 1) (τ - 1) /
            Real.log ((D : ℝ) ^ (1 / σ))) * (τ / s)) := by
  let w : ℝ := (D : ℝ) ^ (1 / σ)
  let v : ℝ := (D : ℝ) ^ (1 / τ)
  let r : ℝ := (D : ℝ) ^ (1 / s)
  have h87 := sigma11_finiteSourceLayer_lemma8_7
    (S := S) (D := (D : ℝ)) (z := r) (v := v) (w := w)
    (s := s) (τ := τ) (σ := σ) (K := K) (β := β) (N := N)
    hβ hτdom hτσ hD hroot2 hv2 hw2 hwv hvroot rfl rfl rfl hK hlocal
  have hmain := Sigma11FiniteLayerMajorization hβ hsdom hτdom hsτ hτσ
  have hprime := h87.trans (add_le_add hmain le_rfl)
  have hscale := mul_le_mul_of_nonneg_left hprime (suzukiVProduct_pos S z).le
  rw [sigmaEleven_eq_lemmaEightSevenPrimeSum_natCeil
    S β σ τ w v r N D z rfl rfl hvroot (by simpa [r] using hz)]
  simpa only [w, mul_add, mul_assoc] using hscale


end SuzukiLemma144KappaOne
end SwitchingPrinciple
end MathlibNt.SieveTheory
