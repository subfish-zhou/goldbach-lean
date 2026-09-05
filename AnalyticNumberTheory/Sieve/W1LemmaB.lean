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
  classical
  induction t using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.powerset_insert (s := s) (a := a)]
      have hdisj : Disjoint s.powerset (s.powerset.image (insert a)) := by
        rw [Finset.disjoint_left]
        intro u hu hiu
        have hnu : a ∉ u := fun hx => ha ((Finset.mem_powerset.mp hu) hx)
        rcases Finset.mem_image.mp hiu with ⟨w, hw, rfl⟩
        have hau : a ∈ insert a w := Finset.mem_insert_self a w
        exact hnu hau
      have hinj : Set.InjOn (insert a) (s.powerset : Set (Finset α)) := by
        intro u hu w hw h
        have hua : a ∉ u := fun hx => ha ((Finset.mem_powerset.mp hu) hx)
        have hwa : a ∉ w := fun hx => ha ((Finset.mem_powerset.mp hw) hx)
        have h' := congrArg (fun v : Finset α => v.erase a) h
        simpa [hua, hwa] using h'
      rw [Finset.sum_union hdisj, Finset.sum_image hinj]
      have hcard : (∑ u ∈ s.powerset, (2 : ℝ) ^ (insert a u).card) =
          ∑ u ∈ s.powerset, (2 : ℝ) ^ u.card * 2 := by
        apply Finset.sum_congr rfl
        intro u hu
        have hua : a ∉ u := fun hx => ha ((Finset.mem_powerset.mp hu) hx)
        rw [Finset.card_insert_of_notMem hua, pow_succ]
      rw [hcard, ← Finset.sum_mul, ih, Finset.card_insert_of_notMem ha, pow_succ]
      ring

/-- Every divisor of squarefree `q` is squarefree, so
`divisors.filter Squarefree` removes no terms. -/
theorem divisors_squarefree_filter_eq_self {q : ℕ} (hq : Squarefree q) :
    q.divisors.filter Squarefree = q.divisors := by
  classical
  apply Finset.ext
  intro d
  rw [Finset.mem_filter]
  constructor
  · intro h
    exact h.1
  · intro hd
    exact ⟨hd, hq.squarefree_of_dvd (Nat.dvd_of_mem_divisors hd)⟩

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
