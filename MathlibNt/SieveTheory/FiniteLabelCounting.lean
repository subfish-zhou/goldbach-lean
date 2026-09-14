import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Data.Finset.Sigma
import Mathlib.Algebra.Order.Sub.Basic

open scoped BigOperators

namespace MathlibNt.SieveTheory

/-- Bound labelled incidences by a relation whose reverse fibres have bounded size.
The labels remain in `S`, even when their associated values coincide. -/
theorem sum_card_le_of_relation {α β : Type*} (S : Finset α) (T : Finset β)
    (F : α → Finset β) (r : α → β → Prop) [DecidableRel r] (C : ℕ)
    (hmap : ∀ a ∈ S, ∀ b ∈ F a, b ∈ T ∧ r a b)
    (hcap : ∀ b ∈ T, (S.filter (fun a => r a b)).card ≤ C) :
    (∑ a ∈ S, (F a).card) ≤ C * T.card := by
  calc
    _ ≤ ∑ a ∈ S, (T.bipartiteAbove r a).card :=
      Finset.sum_le_sum fun a ha => Finset.card_le_card fun b hb =>
        Finset.mem_filter.mpr (hmap a ha b hb)
    _ = ∑ b ∈ T, (S.bipartiteBelow r b).card :=
      Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow r
    _ ≤ ∑ _b ∈ T, C := Finset.sum_le_sum hcap
    _ = C * T.card := by simp [mul_comm]

/-- On a fixed output fibre, a positive retained factor determines its cofactor.
The product bounds are essential because subtraction is in the naturals. -/
theorem sigma_snd_injOn_sub_mul_fiber (A : Finset (Σ _m : ℕ, ℕ)) (N p : ℕ)
    (hpos : ∀ x ∈ A, 0 < x.2) (hle : ∀ x ∈ A, x.2 * x.1 ≤ N) :
    Set.InjOn (fun x : Σ _m : ℕ, ℕ => x.2)
      (A.filter (fun x => N - x.2 * x.1 = p)) := by
  intro x hx y hy he
  obtain ⟨hx, hxp⟩ := Finset.mem_filter.mp hx
  obtain ⟨hy, hyp⟩ := Finset.mem_filter.mp hy
  have hprod := (tsub_right_inj (hle x hx) (hle y hy)).mp (hxp.trans hyp.symm)
  have hm : x.1 = y.1 := Nat.eq_of_mul_eq_mul_left (hpos x hx) (by
    simpa only [← he] using hprod)
  exact Sigma.ext hm (heq_of_eq he)

end MathlibNt.SieveTheory
