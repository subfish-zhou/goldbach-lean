import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144ActualRecurrence
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiClaim145SourceSigmaFinal

open scoped Classical BigOperators
open Finset

namespace MathlibNt.SieveTheory

open SwitchingPrinciple
open SwitchingPrinciple.SuzukiLemma144KappaOne

set_option maxHeartbeats 1200000

/-!
# Lemma 14.4: `Σ₀` at the single source endpoint

The low-prime part is first recombined at its one endpoint, exactly in source
order.  Claim 14.5 is then applied once to the resulting `T_N`; no
prime-dependent threshold or uniformity premise is used.
-/

/-- At a single real endpoint `D^(1/σ)`, the strict low-prime carrier is exactly
the support below its natural ceiling.  The actual Case-I recurrence therefore
recombines `Σ₀` into one value of `suzukiActualT`. -/
theorem suzukiSigmaZero_eq_actualT_single_endpoint
    (S : BoundingSieve) {N D z : ℕ} {σ : ℝ}
    (hN : 2 ≤ N)
    (hz : (D : ℝ) ^ (1 / σ) ≤ (z : ℝ))
    (hOddBoundary : Odd N → ⌈(D : ℝ) ^ (1 / σ)⌉₊ ^ 3 ≤ D) :
    suzukiSigmaZero S N D z ((D : ℝ) ^ (1 / σ)) =
      suzukiActualT S N D ⌈(D : ℝ) ^ (1 / σ)⌉₊ := by
  classical
  let a : ℝ := (D : ℝ) ^ (1 / σ)
  let za : ℕ := ⌈a⌉₊
  have hcarrier :
      (suzukiSupportedBelow S z).filter (fun p : ℕ => (p : ℝ) < a) =
        suzukiSupportedBelow S za := by
    ext p
    simp only [suzukiSupportedBelow, Finset.mem_filter, za, Nat.lt_ceil]
    constructor
    · rintro ⟨⟨hpP, _⟩, hpa⟩
      exact ⟨hpP, hpa⟩
    · rintro ⟨hpP, hpa⟩
      have hpzR : (p : ℝ) < (z : ℝ) := hpa.trans_le (by simpa [a] using hz)
      have hpz : p < z := by exact_mod_cast hpzR
      exact ⟨⟨hpP, hpz⟩, hpa⟩
  have hrec := suzukiActualT_caseI_recurrence
    (S := S) (N := N) (D := D) (z := za) hN (by
      intro hodd
      simpa [za, a] using hOddBoundary hodd)
  unfold suzukiSigmaZero
  change (∑ p ∈ (suzukiSupportedBelow S z).filter
      (fun p : ℕ => (p : ℝ) < a),
      S.nu p * suzukiActualT S (N - 1) (D ⌈/⌉ p) p) = _
  rw [hcarrier]
  exact hrec.symm

/-- Eventual `Σ₀` bound in source order: first use the exact single-endpoint
recombination, then invoke Claim 14.5 once at `sourceSigma D d`. -/
theorem suzukiSigmaZero_sourceSigma_eventually
    (S : BoundingSieve) (H : Section13HatLayers)
    {d Δ K C145 : ℝ}
    (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1)
    (hd : 7 / (1 - Δ) < d) (hK : 0 < K) (hC145 : 0 < C145)
    (hlocal : HasDimensionOneLocalProductBound S K)
    (hH : Section13HatSourceContract H) :
    ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ (D N z : ℕ), D₀ ≤ (D : ℝ) →
      2 ≤ N →
      (D : ℝ) ^ (1 / sourceSigma (D : ℝ) d) ≤ (z : ℝ) →
      (Odd N → ⌈(D : ℝ) ^ (1 / sourceSigma (D : ℝ) d)⌉₊ ^ 3 ≤ D) →
      suzukiSigmaZero S N D z
          ((D : ℝ) ^ (1 / sourceSigma (D : ℝ) d)) ≤
        C145 * claim14_5Scale S H N (D : ℝ) d Δ
          (sourceSigma (D : ℝ) d) K (sourceSigma (D : ℝ) d) := by
  rcases claim145_sourceSigma_endpoint_internal S H hΔ0 hΔ1 hd hK hC145
      hlocal hH with ⟨D₀, hD₀, hendpoint⟩
  refine ⟨D₀, hD₀, ?_⟩
  intro D N z hD hN hz hOddBoundary
  rw [suzukiSigmaZero_eq_actualT_single_endpoint S hN hz hOddBoundary]
  exact hendpoint D N hD


end MathlibNt.SieveTheory
