import AnalyticNumberTheory.Sieve.PanMainTerm
import AnalyticNumberTheory.Sieve.WeightedPan
import Mathlib.Tactic

/-! # W1 lemma B: decomposing 3^{ω(q)} for squarefree q

For squarefree `q` with prime factors `{p₁, ..., p_k}`,

  `3^{ω(q)} = 3^k = ∏_{p|q} (1+2)
   = Σ_{S⊆primeFactors q} 2^{|S|}
   = Σ_{d|q, Squarefree d} 2^{ω(d)}`.

Each subset `S` corresponds to the squarefree divisor
`d = ∏_{p∈S} p`.
`WeightedPan.lean` already supplies the natural-number version
`threeOmega_eq_sum_twoOmega_divisors`. This module gives the
real-valued version with a squarefree filter needed for W1,
separating the combinatorial identity
`3^k = Σ_{S⊆[k]} 2^{|S|}` from the subset-divisor bijection.
-/

namespace AnalyticNumberTheory.Sieve

open Finset Real
open scoped BigOperators

/-- **Combinatorial identity**:
`Σ_{u∈t.powerset} 2^{|u|} = 3^{|t|}`.
Expand `(1+2)^{|t|}` over subsets: each element is independently
included with weight 2 or excluded with weight 1. -/
theorem sum_powerset_two_pow_eq_three_pow {α : Type*} [DecidableEq α] (t : Finset α) :
    (∑ u ∈ t.powerset, (2 : ℝ) ^ u.card) = (3 : ℝ) ^ t.card := by
  simpa only [Finset.prod_const, show (1 : ℝ) + 2 = 3 by norm_num] using
    (Finset.prod_one_add (f := fun _ : α => (2 : ℝ)) t).symm

/-- Every divisor of squarefree `q` is squarefree, so
`divisors.filter Squarefree` removes no terms. -/
theorem divisors_squarefree_filter_eq_self {q : ℕ} (hq : Squarefree q) :
    q.divisors.filter Squarefree = q.divisors := by
  classical
  exact Finset.filter_eq_self.mpr fun d hd =>
    hq.squarefree_of_dvd (Nat.dvd_of_mem_divisors hd)

/-- **Subset-divisor bijection**: for squarefree `q`,
`Σ_{S⊆primeFactors q} 2^{|S|}
 = Σ_{d|q, Squarefree d} 2^{ω(d)}`.
The bijection is `S ↦ ∏_{p∈S} p`, with inverse `d ↦ d.primeFactors`. -/
theorem sum_squarefree_divisors_eq_sum_powerset {q : ℕ} (hq : Squarefree q) :
    (∑ S ∈ (q.primeFactors).powerset, (2 : ℝ) ^ S.card) =
      ∑ d ∈ q.divisors.filter Squarefree, (2 : ℝ) ^ d.primeFactors.card := by
  classical
  apply Finset.sum_bij (i := fun S _ => ∏ p ∈ S, p)
  · intro S hS
    have hdvd : (∏ p ∈ S, p) ∣ q := by
      rw [← Nat.prod_primeFactors_of_squarefree hq]
      exact Finset.prod_dvd_prod_of_subset S q.primeFactors (fun p => p) (Finset.mem_powerset.mp hS)
    rw [Finset.mem_filter]
    constructor
    · rw [Nat.mem_divisors]
      exact ⟨hdvd, hq.ne_zero⟩
    · exact hq.squarefree_of_dvd hdvd
  · intro S₁ hS₁ S₂ hS₂ h
    have hprime₁ : ∀ p ∈ S₁, p.Prime := by
      intro p hp
      exact (Nat.mem_primeFactors.mp ((Finset.mem_powerset.mp hS₁) hp)).1
    have hprime₂ : ∀ p ∈ S₂, p.Prime := by
      intro p hp
      exact (Nat.mem_primeFactors.mp ((Finset.mem_powerset.mp hS₂) hp)).1
    rw [← Nat.primeFactors_prod hprime₁, h, Nat.primeFactors_prod hprime₂]
  · intro d hd
    refine ⟨d.primeFactors, ?_, ?_⟩
    · rw [Finset.mem_powerset]
      exact Nat.primeFactors_mono (Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hd).1) hq.ne_zero
    · exact Nat.prod_primeFactors_of_squarefree (Finset.mem_filter.mp hd).2
  · intro S hS
    have hprime : ∀ p ∈ S, p.Prime := by
      intro p hp
      exact (Nat.mem_primeFactors.mp ((Finset.mem_powerset.mp hS) hp)).1
    rw [Nat.primeFactors_prod hprime]

/-- **W1 lemma B**: for squarefree `q`,
`3^{ω(q)} = Σ_{d|q, Squarefree d} 2^{ω(d)}`.
Each prime factor contributes `3 = 1+2`, according to whether
it is excluded from or included in `d`; every squarefree divisor
corresponds to exactly one subset of the prime-factor set. -/
theorem three_pow_omega_eq_sum_two_pow {q : ℕ} (hq : Squarefree q) :
    (3 : ℝ) ^ q.primeFactors.card =
      ∑ d ∈ q.divisors.filter Squarefree, (2 : ℝ) ^ d.primeFactors.card := by
  classical
  rw [← sum_squarefree_divisors_eq_sum_powerset hq]
  exact (sum_powerset_two_pow_eq_three_pow q.primeFactors).symm

end AnalyticNumberTheory.Sieve
