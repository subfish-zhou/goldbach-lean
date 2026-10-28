import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma87FiniteSourceRecursion
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144Equation1410

open scoped Classical BigOperators
open MeasureTheory Set

namespace MathlibNt.SieveTheory.SwitchingPrinciple
namespace SuzukiLemma144KappaOne

open SuzukiFiniteContinuousLayers

set_option maxHeartbeats 800000


/-- Direct source-layer instance of Lemma 8.7, kept in the same import cone as
Claim 14.5 to avoid the legacy/production finite-layer declaration collision. -/
theorem sigma11_finiteSourceLayer_lemma8_7
    {S : BoundingSieve} {D z v w s τ σ K β : ℝ} {N : ℕ}
    (hβ : 1 < β)
    (hτdom : τ - 1 ∈ KappaOneModel.parityDomain β (N - 1))
    (hτσ : τ ≤ σ)
    (hD : 1 < D) (hz2 : 2 ≤ z) (hv2 : 2 ≤ v) (hw2 : 2 ≤ w)
    (hwv : w ≤ v) (hvz : v ≤ z)
    (hz : z = D ^ (1 / s)) (hv : v = D ^ (1 / τ))
    (hw : w = D ^ (1 / σ))
    (hK : 2 ≤ K) (hlocal : HasDimensionOneLocalProductBound S K) :
    suzukiLemmaEightSevenPrimeSum S D w v z
        (fun t => finiteSourceLayer 1 β (N - 1) (t - 1)) ≤
      (1 / s) * (∫ t in τ..σ, finiteSourceLayer 1 β (N - 1) (t - 1)) +
        (6 * K ^ 2 * finiteSourceLayer 1 β (N - 1) (τ - 1) /
          Real.log w) * (τ / s) := by
  exact suzukiLemmaEightSeven_finiteSourceLayer_shift
    hβ hτdom hτσ hD hz2 hv2 hw2 hwv hvz hz hv hw hK hlocal

/-- Monotonicity of the source-faithful Lemma-8.7 middle-range functional.
Only values at the actual prime coordinates are required.  The Euler suffix
continues to use the third cutoff `z`; the prime carrier stops at `v`. -/
theorem suzukiLemmaEightSevenPrimeSum_mono_on_middle
    (S : BoundingSieve) (D w v z : ℝ) (F G : ℝ → ℝ)
    (hFG : ∀ p ∈ S.prodPrimes.primeFactors,
      w ≤ (p : ℝ) → (p : ℝ) < v →
      F (Real.log D / Real.log p) ≤ G (Real.log D / Real.log p)) :
    suzukiLemmaEightSevenPrimeSum S D w v z F ≤
      suzukiLemmaEightSevenPrimeSum S D w v z G := by
  classical
  unfold suzukiLemmaEightSevenPrimeSum
  apply Finset.sum_le_sum
  intro p hp
  have hp' := Finset.mem_filter.mp hp
  have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hp'.1
  have hpdiv : p ∣ S.prodPrimes := (Nat.mem_primeFactors.mp hp'.1).2.1
  have hnu : 0 ≤ S.nu p := (S.nu_pos_of_prime p hpprime hpdiv).le
  have hsuffix : 0 ≤ ∏ q ∈ S.prodPrimes.primeFactors.filter
      (fun q : ℕ => p ≤ q ∧ (q : ℝ) < z), (1 - S.nu q)⁻¹ := by
    apply Finset.prod_nonneg
    intro q hq
    have hq' := Finset.mem_filter.mp hq
    have hqprime : q.Prime := Nat.prime_of_mem_primeFactors hq'.1
    have hqdiv : q ∣ S.prodPrimes := (Nat.mem_primeFactors.mp hq'.1).2.1
    exact inv_nonneg.mpr
      (sub_nonneg.mpr (S.nu_lt_one_of_prime q hqprime hqdiv).le)
  exact mul_le_mul_of_nonneg_left
    (hFG p hp'.1 hp'.2.1 hp'.2.2) (mul_nonneg hnu hsuffix)

/-- Source-correct `Σ₁₁` middle-range assembly.  Lemma 8.7 is used only on
`w ≤ p < v`, with `H(t)=T_{N-1}(t-1)`.  Proposition 9.3 supplies all analytic
conditions, while the source recursion bounds the truncated main integral by
`T_N(s)`.  No equality is asserted: it generally fails when `τ > s` or when
`σ` truncates the source support. -/
theorem sigma11_middle_le_finiteSourceLayer_add_endpoint
    {S : BoundingSieve} {D z v w s τ σ K β : ℝ} {N : ℕ}
    (hβ : 1 < β)
    (hsdom : s ∈ KappaOneModel.parityDomain β N)
    (hτdom : τ - 1 ∈ KappaOneModel.parityDomain β (N - 1))
    (hsτ : s ≤ τ) (hτσ : τ ≤ σ)
    (hD : 1 < D) (hz2 : 2 ≤ z) (hv2 : 2 ≤ v) (hw2 : 2 ≤ w)
    (hwv : w ≤ v) (hvz : v ≤ z)
    (hz : z = D ^ (1 / s)) (hv : v = D ^ (1 / τ))
    (hw : w = D ^ (1 / σ))
    (hK : 2 ≤ K) (hlocal : HasDimensionOneLocalProductBound S K) :
    suzukiLemmaEightSevenPrimeSum S D w v z
        (fun t => finiteSourceLayer 1 β (N - 1) (t - 1)) ≤
      finiteSourceLayer 1 β N s +
        (6 * K ^ 2 * finiteSourceLayer 1 β (N - 1) (τ - 1) /
          Real.log w) * (τ / s) := by
  have h87 := sigma11_finiteSourceLayer_lemma8_7
    hβ hτdom hτσ hD hz2 hv2 hw2 hwv hvz hz hv hw hK hlocal
  exact h87.trans (add_le_add
    (Sigma11FiniteLayerMajorization hβ hsdom hτdom hsτ hτσ) le_rfl)


end SuzukiLemma144KappaOne
end MathlibNt.SieveTheory.SwitchingPrinciple
