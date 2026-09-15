import Wu18938Campaign.M2.RawArithmetic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Range

namespace Wu18938Campaign.M2

open Finset
open scoped Classical

theorem raw_squarefree_carrier_empty (low : ℕ → Prop) {N d L p : ℕ}
    (hp : p.Prime) (hpN : p.Coprime N) (hpL : p ∣ L) (hlow : low p) :
    ((range (N + 1)).filter fun ell =>
      ell.Prime ∧ d * L ∣ N - ell ∧
        (∀ q : ℕ, q.Prime → q.Coprime (d * N) → low q → ¬q ∣ N - ell) ∧
          Squarefree (N - ell)) = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro ell hell
  obtain ⟨_, _, hd, hs, hsf⟩ := mem_filter.mp hell
  exact raw_squarefree_excludes_label low hp hpN hpL hd hsf hs hlow

theorem raw_squarefree_count_zero (low : ℕ → Prop) {N d L p : ℕ}
    (hp : p.Prime) (hpN : p.Coprime N) (hpL : p ∣ L) (hlow : low p) :
    (((range (N + 1)).filter fun ell =>
      ell.Prime ∧ d * L ∣ N - ell ∧
        (∀ q : ℕ, q.Prime → q.Coprime (d * N) → low q → ¬q ∣ N - ell) ∧
          Squarefree (N - ell)).card : ℕ) = 0 := by
  rw [raw_squarefree_carrier_empty low hp hpN hpL hlow, card_empty]

end Wu18938Campaign.M2
