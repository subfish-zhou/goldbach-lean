import R2RawMotherAssembly

namespace WuPaper.R2RawMother

open Finset Wu2008DoubleSieve
open scoped Classical

theorem ordered_prime_prod_squarefree (l : List ℕ)
    (hord : l.Pairwise (· < ·)) (hp : ∀ p ∈ l, p.Prime) :
    Squarefree l.prod := by
  induction l with
  | nil => simp
  | cons p l ih =>
    obtain ⟨hmin, hord⟩ := List.pairwise_cons.mp hord
    have hpp := hp p (by simp)
    rw [List.prod_cons, Nat.squarefree_mul_iff]
    refine ⟨secondFunctionalMother_coprime_prod p l ?_, hpp.prime.squarefree,
      ih hord (fun q hq => hp q (by simp [hq]))⟩
    intro q hq
    exact (Nat.coprime_primes hpp (hp q (by simp [hq]))).mpr (ne_of_lt (hmin q hq))

theorem prime_list_product_add_three_coprime (l : List ℕ) {p : ℕ}
    (hp : p.Prime) (hpl : p ∈ l) (h3 : 3 < p) :
    p.Coprime (l.prod + 3) := by
  apply hp.coprime_iff_not_dvd.mpr
  intro hd
  have hd3 : p ∣ 3 := by
    have h := Nat.dvd_sub hd (List.dvd_prod hpl)
    simpa only [Nat.add_sub_cancel_left] using h
  have := Nat.le_of_dvd (by norm_num : 0 < 3) hd3
  omega

theorem prime_list_product_add_three_even (l : List ℕ)
    (hp : ∀ p ∈ l, p.Prime) (h3 : ∀ p ∈ l, 3 < p) :
    Even (l.prod + 3) := by
  have hodd : Odd l.prod := by
    induction l with
    | nil => simp
    | cons p l ih =>
      have hpp := hp p (by simp)
      have hp3 := h3 p (by simp)
      have hpo : Odd p := Nat.odd_iff.mpr (hpp.eq_two_or_odd.resolve_left (by omega))
      exact hpo.mul (ih (fun q hq => hp q (by simp [hq]))
        (fun q hq => h3 q (by simp [hq])))
  exact hodd.add_odd (by decide : Odd 3)

theorem prefix_suffix_carrier (N : ℕ) (l : List ℕ) (s t : ℕ) :
    secondFunctionalMotherPrefixCarrier N 1 (l ++ [s, t]) =
      sourceSieveCarrier N (l.prod * (s * t)) (l.prod * N) (s : ℝ) := by
  simp [fourthRowMotherPrefixCarrier, List.prod_append]

theorem prefix_suffix_witness (l : List ℕ) {s t : ℕ}
    (hs : s.Prime) (ht : t.Prime) (hst : s ≤ t) :
    3 ∈ secondFunctionalMotherPrefixCarrier ((l ++ [s, t]).prod + 3) 1
      (l ++ [s, t]) := by
  rw [prefix_suffix_carrier]
  apply mem_filter.mpr
  have heq : (l ++ [s, t]).prod = l.prod * (s * t) := by simp [List.prod_append]
  refine ⟨mem_range.mpr (by omega), by norm_num, ?_, ?_⟩
  · simp [heq]
  · rw [Nat.add_sub_cancel, heq, sifted_mul_iff, sifted_mul_iff]
    refine ⟨?_, sifted_prime_of_le hs le_rfl, sifted_prime_of_le ht ?_⟩
    · intro q hq hc hz
      exact siftedLE_of_dvd_modulus (dvd_mul_right l.prod _) _ q hq hc hz.le
    · exact_mod_cast hst

theorem squarefree_exception_witness (l : List ℕ) {p s t : ℕ}
    (hpl : p ∈ l) (hp : p.Prime) (hp3 : 3 < p) (hps : p < s)
    (hs : s.Prime) (ht : t.Prime) (hst : s ≤ t)
    (hord : (l ++ [s, t]).Pairwise (· < ·))
    (hprime : ∀ q ∈ l ++ [s, t], q.Prime)
    (hlarge : ∀ q ∈ l ++ [s, t], 3 < q) :
    Even ((l ++ [s, t]).prod + 3) ∧
      3 ∈ exceptionalCarrier ((l ++ [s, t]).prod + 3) 1 (l ++ [s, t]) ∧
        3 ∉ rawCarrier ((l ++ [s, t]).prod + 3) 1 (l ++ [s, t]) ∧
          Squarefree (((l ++ [s, t]).prod + 3) - 3) := by
  have hpmem : p ∈ l ++ [s, t] := List.mem_append_left _ hpl
  have hpN : p.Coprime (1 * ((l ++ [s, t]).prod + 3)) := by
    simpa only [one_mul] using prime_list_product_add_three_coprime _ hp hpmem hp3
  have hcut : (p : ℝ) < (l ++ [s, t]).getD ((l ++ [s, t]).length - 2) 0 := by
    simpa using (show (p : ℝ) < s by exact_mod_cast hps)
  have hempty := rawCarrier_empty_of_selected hp hpN hpmem hcut
  refine ⟨prime_list_product_add_three_even _ hprime hlarge, ?_, ?_, ?_⟩
  · rw [exceptional_eq_prefix_of_selected hp hpN hpmem hcut]
    exact prefix_suffix_witness l hs ht hst
  · rw [hempty]
    simp
  · simpa only [Nat.add_sub_cancel] using ordered_prime_prod_squarefree _ hord hprime

theorem prefixTerm_one_le_of_witness {N d M : ℕ} {a b c e f : ℝ}
    {cs l : List ℕ} {ell : ℕ}
    (hl : l ∈ secondFunctionalMotherTuples (primeWindow M a f) cs.length)
    (hc : l.map (secondFunctionalMotherColour b c e) = cs)
    (hw : ell ∈ secondFunctionalMotherPrefixCarrier N d l) :
    1 ≤ secondFunctionalMotherPrefixTerm N d M a b c e f cs := by
  have hcard : 1 ≤ (secondFunctionalMotherPrefixCarrier N d l).card :=
    card_pos.mpr ⟨ell, hw⟩
  calc
    (1 : ℝ) ≤ ((secondFunctionalMotherPrefixCarrier N d l).card : ℝ) := by
      exact_mod_cast hcard
    _ = if l.map (secondFunctionalMotherColour b c e) = cs then
        ((secondFunctionalMotherPrefixCarrier N d l).card : ℝ) else 0 := by rw [if_pos hc]
    _ ≤ _ := by
      unfold secondFunctionalMotherPrefixTerm
      exact single_le_sum (f := fun l =>
        if l.map (secondFunctionalMotherColour b c e) = cs then
          ((secondFunctionalMotherPrefixCarrier N d l).card : ℝ) else 0)
        (fun l _ => by split_ifs <;> positivity) hl

end WuPaper.R2RawMother

#check @WuPaper.R2RawMother.ordered_prime_prod_squarefree
#print axioms WuPaper.R2RawMother.ordered_prime_prod_squarefree
#check @WuPaper.R2RawMother.prime_list_product_add_three_coprime
#print axioms WuPaper.R2RawMother.prime_list_product_add_three_coprime
#check @WuPaper.R2RawMother.prime_list_product_add_three_even
#print axioms WuPaper.R2RawMother.prime_list_product_add_three_even
#check @WuPaper.R2RawMother.prefix_suffix_carrier
#print axioms WuPaper.R2RawMother.prefix_suffix_carrier
#check @WuPaper.R2RawMother.prefix_suffix_witness
#print axioms WuPaper.R2RawMother.prefix_suffix_witness
#check @WuPaper.R2RawMother.squarefree_exception_witness
#print axioms WuPaper.R2RawMother.squarefree_exception_witness
#check @WuPaper.R2RawMother.prefixTerm_one_le_of_witness
#print axioms WuPaper.R2RawMother.prefixTerm_one_le_of_witness
