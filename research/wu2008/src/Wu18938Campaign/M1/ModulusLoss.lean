import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Lean.Elab.Tactic.Omega

namespace Wu18938Campaign.M1

open Finset
open scoped Classical

theorem sifted_filter_defect_antitone {ι : Type*}
    (I : Finset ι) (n : ι → ℕ) (M a : ℕ) {b c : ℝ}
    (ha : a.Prime) (haM : a.Coprime M) (hab : (a : ℝ) < b) (hbc : b ≤ c) :
    (((I.filter (fun i => ∀ q : ℕ, q.Prime → q.Coprime (M * a) →
        (q : ℝ) < c → ¬q ∣ n i)).card : ℤ) -
      ((I.filter (fun i => ∀ q : ℕ, q.Prime → q.Coprime M →
        (q : ℝ) < c → ¬q ∣ n i)).card : ℤ)) ≤
    (((I.filter (fun i => ∀ q : ℕ, q.Prime → q.Coprime (M * a) →
        (q : ℝ) < b → ¬q ∣ n i)).card : ℤ) -
      ((I.filter (fun i => ∀ q : ℕ, q.Prime → q.Coprime M →
        (q : ℝ) < b → ¬q ∣ n i)).card : ℤ)) := by
  let F := fun (K : ℕ) (y : ℝ) =>
    I.filter (fun i => ∀ q : ℕ, q.Prime → q.Coprime K →
      (q : ℝ) < y → ¬q ∣ n i)
  have hsub : ∀ y : ℝ, F M y ⊆ F (M * a) y := by
    intro y i hi
    obtain ⟨hi, hs⟩ := mem_filter.mp hi
    exact mem_filter.mpr ⟨hi, fun q hq hqMa hqy =>
      hs q hq (Nat.coprime_mul_iff_right.mp hqMa).1 hqy⟩
  have hdiff : F (M * a) c \ F M c ⊆ F (M * a) b \ F M b := by
    intro i hi
    obtain ⟨hi, hnot⟩ := mem_sdiff.mp hi
    obtain ⟨hiI, hs⟩ := mem_filter.mp hi
    refine mem_sdiff.mpr ⟨mem_filter.mpr ⟨hiI, ?_⟩, ?_⟩
    · intro q hq hqMa hqb
      exact hs q hq hqMa (hqb.trans_le hbc)
    · intro hiM
      have hsM := (mem_filter.mp hiM).2
      apply hnot
      refine mem_filter.mpr ⟨hiI, ?_⟩
      intro q hq hqM hqc
      by_cases hqa : q = a
      · subst q
        exact hsM a ha haM hab
      · exact hs q hq
          (Nat.coprime_mul_iff_right.mpr
            ⟨hqM, (Nat.coprime_primes hq ha).mpr hqa⟩) hqc
  have hb := card_sdiff_add_card_eq_card (hsub b)
  have hc := card_sdiff_add_card_eq_card (hsub c)
  have hd := card_le_card hdiff
  change ((F (M * a) c).card : ℤ) - ((F M c).card : ℤ) ≤
    ((F (M * a) b).card : ℤ) - ((F M b).card : ℤ)
  omega

theorem prime_complement_defect_antitone (N d a : ℕ) {b c : ℝ}
    (ha : a.Prime) (haN : a.Coprime N) (hab : (a : ℝ) < b) (hbc : b ≤ c) :
    let Q := fun (M : ℕ) (y : ℝ) =>
      (((range (N + 1)).filter (fun p =>
        p.Prime ∧ d ∣ N - p ∧
          ∀ q : ℕ, q.Prime → q.Coprime M → (q : ℝ) < y →
            ¬q ∣ (N - p) / d)).card : ℤ)
    Q (N * a) c - Q N c ≤ Q (N * a) b - Q N b := by
  dsimp only
  have h := sifted_filter_defect_antitone
    ((range (N + 1)).filter (fun p => p.Prime ∧ d ∣ N - p))
    (fun p => (N - p) / d) N a ha haN hab hbc
  simpa only [filter_filter, and_assoc] using h

end Wu18938Campaign.M1
