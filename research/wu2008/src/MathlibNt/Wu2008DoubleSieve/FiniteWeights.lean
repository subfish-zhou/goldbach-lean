import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-!
# The finite three-prime weight in Wu's double sieve

Source: Wu (2008), Proposition 4.4, equation (4.4). The exceptional
small-prime and analytic estimates are not part of this module.

The least two distinct sifting divisors determine a triple with every
remaining divisor. This proves the actual finite weight inequality, without
squarefreeness or assumptions about an asymptotic sieve estimate.
-/

namespace Wu2008DoubleSieve

open Finset

/-- Increasing triples of elements of a finite set. -/
def orderedTriples (s : Finset ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (s ×ˢ (s ×ˢ s)).filter (fun t => t.1 < t.2.1 ∧ t.2.1 < t.2.2)

/-- The first two entries are the two least elements of `s`. -/
def firstTwoTriples (s : Finset ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (orderedTriples s).filter
    (fun t => ∀ q ∈ s, q < t.2.1 → q = t.1)

theorem mem_firstTwoTriples {s : Finset ℕ} {a b c : ℕ} :
    (a, b, c) ∈ firstTwoTriples s ↔
      a ∈ s ∧ b ∈ s ∧ c ∈ s ∧ a < b ∧ b < c ∧
        ∀ q ∈ s, q < b → q = a := by
  simp only [firstTwoTriples, orderedTriples, mem_filter, mem_product]
  tauto

/-- Each divisor other than the two least ones supplies a distinct triple. -/
theorem card_le_two_add_firstTwoTriples (s : Finset ℕ) :
    s.card ≤ 2 + (firstTwoTriples s).card := by
  classical
  by_cases hs : s.Nonempty
  · let a := s.min' hs
    have ha : a ∈ s := s.min'_mem hs
    have ha_le : ∀ q ∈ s, a ≤ q := fun q hq => s.min'_le q hq
    by_cases ht : (s.erase a).Nonempty
    · let b := (s.erase a).min' ht
      have hb : b ∈ s.erase a := (s.erase a).min'_mem ht
      have hb_le : ∀ q ∈ s.erase a, b ≤ q :=
        fun q hq => (s.erase a).min'_le q hq
      have hab : a < b := lt_of_le_of_ne (ha_le b (mem_erase.mp hb).2)
        (Ne.symm (mem_erase.mp hb).1)
      have hcard :
          ((s.erase a).erase b).card ≤ (firstTwoTriples s).card := by
        apply Finset.card_le_card_of_injOn (fun c => (a, b, c))
        · intro c hc
          have hc' := mem_erase.mp hc
          refine mem_firstTwoTriples.mpr
            ⟨ha, (mem_erase.mp hb).2, (mem_erase.mp hc'.2).2, hab, ?_, ?_⟩
          · exact lt_of_le_of_ne (hb_le c hc'.2) (Ne.symm hc'.1)
          · intro q hq hqb
            by_contra hqa
            exact (not_lt_of_ge (hb_le q (mem_erase.mpr ⟨hqa, hq⟩))) hqb
        · intro c _ d _ h
          exact congrArg (fun t : ℕ × ℕ × ℕ => t.2.2) h
      have hca := Finset.card_erase_add_one ha
      have hcb := Finset.card_erase_add_one hb
      omega
    · have he : s.erase a = ∅ := Finset.not_nonempty_iff_eq_empty.mp ht
      have hca := Finset.card_erase_add_one ha
      rw [he, card_empty] at hca
      omega
  · have he : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    simp [he]

/-- Pointwise form of Wu's upper weight; repeated prime factors cause no loss. -/
theorem three_prime_weight (s : Finset ℕ) :
    (if s = ∅ then (2 : ℤ) else 0) ≤
      2 - (s.card : ℤ) + ((firstTwoTriples s).card : ℤ) := by
  classical
  by_cases hs : s = ∅
  · simp [hs, firstTwoTriples, orderedTriples]
  · have h := card_le_two_add_firstTwoTriples s
    have h' : (s.card : ℤ) ≤ 2 + ((firstTwoTriples s).card : ℤ) := by
      exact_mod_cast h
    simp only [if_neg hs]
    omega

/-- Distinct sifting divisors, not prime factors counted with multiplicity. -/
def divisorsIn (P : Finset ℕ) (n : ℕ) : Finset ℕ :=
  P.filter (fun q => q ∣ n)

/-- Indices are retained, so equal values of `v` are counted with multiplicity. -/
def siftedIndices {ι : Type*} (A : Finset ι) (v : ι → ℕ) (P : Finset ℕ) :
    Finset ι :=
  A.filter (fun i => divisorsIn P (v i) = ∅)

/-- The sieve at the second selected divisor omits the first selected divisor. -/
def tripleSurvives (P : Finset ℕ) (n : ℕ) (t : ℕ × ℕ × ℕ) : Prop :=
  t.1 ∣ n ∧ t.2.1 ∣ n ∧ t.2.2 ∣ n ∧
    ∀ q ∈ P, q < t.2.1 → q ≠ t.1 → ¬q ∣ n

instance (P : Finset ℕ) (n : ℕ) (t : ℕ × ℕ × ℕ) :
    Decidable (tripleSurvives P n t) := by
  unfold tripleSurvives
  infer_instance

theorem firstTwoTriples_divisorsIn (P : Finset ℕ) (n : ℕ) :
    firstTwoTriples (divisorsIn P n) =
      (orderedTriples P).filter (tripleSurvives P n) := by
  ext ⟨a, b, c⟩
  simp only [mem_firstTwoTriples, divisorsIn, mem_filter,
    orderedTriples, mem_product, tripleSurvives]
  constructor
  · rintro ⟨⟨ha, han⟩, ⟨hb, hbn⟩, ⟨hc, hcn⟩, hab, hbc, hmin⟩
    refine ⟨⟨⟨ha, hb, hc⟩, hab, hbc⟩, han, hbn, hcn, ?_⟩
    intro q hq hqb hqa hqn
    exact hqa (hmin q ⟨hq, hqn⟩ hqb)
  · rintro ⟨⟨⟨ha, hb, hc⟩, hab, hbc⟩, han, hbn, hcn, hmin⟩
    refine ⟨⟨ha, han⟩, ⟨hb, hbn⟩, ⟨hc, hcn⟩, hab, hbc, ?_⟩
    intro q hq hqb
    by_contra hqa
    exact hmin q hq.1 hqb hqa hq.2

def singleMass {ι : Type*} (A : Finset ι) (v : ι → ℕ) (P : Finset ℕ) : ℤ :=
  ∑ q ∈ P, ((A.filter (fun i => q ∣ v i)).card : ℤ)

def tripleMass {ι : Type*} (A : Finset ι) (v : ι → ℕ) (P : Finset ℕ) : ℤ :=
  ∑ t ∈ orderedTriples P, ((A.filter (fun i => tripleSurvives P (v i) t)).card : ℤ)

theorem singleMass_eq_sum {ι : Type*} (A : Finset ι) (v : ι → ℕ)
    (P : Finset ℕ) :
    singleMass A v P = ∑ i ∈ A, ((divisorsIn P (v i)).card : ℤ) := by
  simp only [singleMass, divisorsIn, ← Finset.sum_boole]
  exact Finset.sum_comm

theorem tripleMass_eq_sum {ι : Type*} (A : Finset ι) (v : ι → ℕ)
    (P : Finset ℕ) :
    tripleMass A v P = ∑ i ∈ A, ((firstTwoTriples (divisorsIn P (v i))).card : ℤ) := by
  simp only [tripleMass, firstTwoTriples_divisorsIn, ← Finset.sum_boole]
  exact Finset.sum_comm

/-- Wu's three-prime upper weight on a genuine finite multiset of integers.
There is no asymptotic or distribution hypothesis. -/
theorem finite_three_prime_upper_weight {ι : Type*} (A : Finset ι) (v : ι → ℕ)
    (P : Finset ℕ) :
    2 * ((siftedIndices A v P).card : ℤ) ≤
      2 * (A.card : ℤ) - singleMass A v P + tripleMass A v P := by
  classical
  have h := Finset.sum_le_sum (fun i (_ : i ∈ A) =>
    three_prime_weight (divisorsIn P (v i)))
  have hleft :
      (∑ i ∈ A, if divisorsIn P (v i) = ∅ then (2 : ℤ) else 0) =
        2 * ((siftedIndices A v P).card : ℤ) := by
    simp only [siftedIndices, ← Finset.sum_boole, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> norm_num
  rw [hleft, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← singleMass_eq_sum, ← tripleMass_eq_sum] at h
  simpa [mul_comm] using h

end Wu2008DoubleSieve
