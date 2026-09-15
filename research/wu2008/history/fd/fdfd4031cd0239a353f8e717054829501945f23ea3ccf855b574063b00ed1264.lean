import R2RawMotherCarrier

namespace WuPaper.R2RawMother

open Finset Wu2008DoubleSieve
open scoped Classical

theorem sifted_prime_iff {M p : ℕ} (hp : p.Prime) (z : ℝ) :
    Sifted M p z ↔ z ≤ (p : ℝ) ∨ p ∣ M := by
  constructor
  · intro hs
    by_cases hz : z ≤ (p : ℝ)
    · exact Or.inl hz
    · right
      by_contra hd
      exact hs p hp (hp.coprime_iff_not_dvd.mpr hd) (lt_of_not_ge hz) (dvd_refl p)
  · rintro (hz | hd)
    · exact sifted_prime_of_le hp hz
    · intro q hq hc hz
      exact siftedLE_of_dvd_modulus hd z q hq hc hz.le

theorem labelsSurvive_five_iff {N d p q r s t : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hs : s.Prime) (ht : t.Prime)
    (hpN : p.Coprime N) (hqN : q.Coprime N) (hrN : r.Coprime N)
    (hps : p < s) (hqs : q < s) (hrs : r < s) (hst : s ≤ t) :
    labelsSurvive N d [p, q, r, s, t] ↔ p ∣ d ∧ q ∣ d ∧ r ∣ d := by
  have hbase : Sifted (d * N) d (s : ℝ) :=
    fun v hv hc hz => siftedLE_of_dvd_modulus (dvd_mul_right d N) _ v hv hc hz.le
  have hps' : ¬(s : ℝ) ≤ p := not_le.mpr (by exact_mod_cast hps)
  have hqs' : ¬(s : ℝ) ≤ q := not_le.mpr (by exact_mod_cast hqs)
  have hrs' : ¬(s : ℝ) ≤ r := not_le.mpr (by exact_mod_cast hrs)
  have hst' : (s : ℝ) ≤ t := by exact_mod_cast hst
  simp only [labelsSurvive, List.length_cons, List.length_nil, List.getD,
    List.prod_cons, List.prod_nil, mul_one, Nat.reduceAdd, Nat.reduceSub,
    sifted_mul_iff, hbase, true_and, sifted_prime_iff hp, sifted_prime_iff hq,
    sifted_prime_iff hr, sifted_prime_iff hs, sifted_prime_iff ht,
    hps', hqs', hrs', hst', le_refl, true_or, false_or, and_true,
    hp.dvd_mul, hq.dvd_mul, hr.dvd_mul,
    hp.coprime_iff_not_dvd.mp hpN, hq.coprime_iff_not_dvd.mp hqN,
    hr.coprime_iff_not_dvd.mp hrN, or_false]

theorem labelsSurvive_six_iff {N d p q r s t u : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hs : s.Prime) (ht : t.Prime) (hu : u.Prime)
    (hpN : p.Coprime N) (hqN : q.Coprime N)
    (hrN : r.Coprime N) (hsN : s.Coprime N)
    (hpt : p < t) (hqt : q < t) (hrt : r < t) (hst : s < t) (htu : t ≤ u) :
    labelsSurvive N d [p, q, r, s, t, u] ↔ p ∣ d ∧ q ∣ d ∧ r ∣ d ∧ s ∣ d := by
  have hbase : Sifted (d * N) d (t : ℝ) :=
    fun v hv hc hz => siftedLE_of_dvd_modulus (dvd_mul_right d N) _ v hv hc hz.le
  have hpt' : ¬(t : ℝ) ≤ p := not_le.mpr (by exact_mod_cast hpt)
  have hqt' : ¬(t : ℝ) ≤ q := not_le.mpr (by exact_mod_cast hqt)
  have hrt' : ¬(t : ℝ) ≤ r := not_le.mpr (by exact_mod_cast hrt)
  have hst' : ¬(t : ℝ) ≤ s := not_le.mpr (by exact_mod_cast hst)
  have htu' : (t : ℝ) ≤ u := by exact_mod_cast htu
  simp only [labelsSurvive, List.length_cons, List.length_nil, List.getD,
    List.prod_cons, List.prod_nil, mul_one, Nat.reduceAdd, Nat.reduceSub,
    sifted_mul_iff, hbase, true_and, sifted_prime_iff hp, sifted_prime_iff hq,
    sifted_prime_iff hr, sifted_prime_iff hs, sifted_prime_iff ht, sifted_prime_iff hu,
    hpt', hqt', hrt', hst', htu', le_refl, true_or, false_or, and_true,
    hp.dvd_mul, hq.dvd_mul, hr.dvd_mul, hs.dvd_mul,
    hp.coprime_iff_not_dvd.mp hpN, hq.coprime_iff_not_dvd.mp hqN,
    hr.coprime_iff_not_dvd.mp hrN, hs.coprime_iff_not_dvd.mp hsN, or_false]

noncomputable def rawTerm (N d M : ℕ) (a b c e f : ℝ) (cs : List ℕ) : ℝ :=
  ∑ l ∈ secondFunctionalMotherTuples (primeWindow M a f) cs.length,
    if l.map (secondFunctionalMotherColour b c e) = cs then
      ((rawCarrier N d l).card : ℝ) else 0

noncomputable def exceptionTerm (N d M : ℕ) (a b c e f : ℝ) (cs : List ℕ) : ℝ :=
  ∑ l ∈ secondFunctionalMotherTuples (primeWindow M a f) cs.length,
    if l.map (secondFunctionalMotherColour b c e) = cs then
      ((exceptionalCarrier N d l).card : ℝ) else 0

theorem term_exact (N d M : ℕ) (a b c e f : ℝ) (cs : List ℕ) :
    secondFunctionalMotherPrefixTerm N d M a b c e f cs =
      rawTerm N d M a b c e f cs + exceptionTerm N d M a b c e f cs := by
  unfold secondFunctionalMotherPrefixTerm rawTerm exceptionTerm
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro l _
  split_ifs
  · exact prefix_card_exact N d l
  · simp

theorem ordered_raw_empty {N d : ℕ} {a f : ℝ} {l : List ℕ}
    (hlen : 3 ≤ l.length) (hord : l.Pairwise (· < ·))
    (hmem : ∀ q ∈ l, q ∈ primeWindow (d * N) a f) :
    rawCarrier N d l = ∅ := by
  cases l with
  | nil => simp at hlen
  | cons p l =>
    have hllen : 2 ≤ l.length := by simpa using hlen
    have hi : l.length - 2 < l.length := by omega
    have hcutmem : l.getD (l.length - 2) 0 ∈ l := by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
      exact List.getElem_mem hi
    obtain ⟨hp, hpN, _, _⟩ := mem_primeWindow.mp (hmem p (by simp))
    apply rawCarrier_empty_of_selected hp hpN (by simp)
    have hlt := (List.pairwise_cons.mp hord).1 _ hcutmem
    have heq : (p :: l).getD ((p :: l).length - 2) 0 =
        l.getD (l.length - 2) 0 := by
      simp only [List.length_cons, show l.length + 1 - 2 = (l.length - 2) + 1 by omega,
        List.getD_cons_succ]
    rw [heq]
    exact_mod_cast hlt

theorem rawTerm_masked_zero (N d : ℕ) (a b c e f : ℝ) (cs : List ℕ)
    (hcs : 3 ≤ cs.length) :
    rawTerm N d (d * N) a b c e f cs = 0 := by
  apply sum_eq_zero
  intro l hl
  obtain ⟨hlen, hord, hmem⟩ := (secondFunctionalMother_tuple_mem _ _ _).mp hl
  have he := ordered_raw_empty (hlen ▸ hcs) hord hmem
  split_ifs <;> simp [he]

theorem rawTerm_unit_zero (N : ℕ) (a b c e f : ℝ) (cs : List ℕ)
    (hcs : 3 ≤ cs.length) :
    rawTerm N 1 N a b c e f cs = 0 := by
  simpa only [one_mul] using rawTerm_masked_zero N 1 a b c e f cs hcs

theorem exceptionTerm_unit_eq_prefix (N : ℕ) (a b c e f : ℝ) (cs : List ℕ)
    (hcs : 3 ≤ cs.length) :
    exceptionTerm N 1 N a b c e f cs =
      secondFunctionalMotherPrefixTerm N 1 N a b c e f cs := by
  have h := term_exact N 1 N a b c e f cs
  rw [rawTerm_unit_zero N a b c e f cs hcs, zero_add] at h
  exact h.symm

end WuPaper.R2RawMother

#check @WuPaper.R2RawMother.sifted_prime_iff
#print axioms WuPaper.R2RawMother.sifted_prime_iff
#check @WuPaper.R2RawMother.labelsSurvive_five_iff
#print axioms WuPaper.R2RawMother.labelsSurvive_five_iff
#check @WuPaper.R2RawMother.labelsSurvive_six_iff
#print axioms WuPaper.R2RawMother.labelsSurvive_six_iff
#check @WuPaper.R2RawMother.rawTerm
#print axioms WuPaper.R2RawMother.rawTerm
#check @WuPaper.R2RawMother.exceptionTerm
#print axioms WuPaper.R2RawMother.exceptionTerm
#check @WuPaper.R2RawMother.term_exact
#print axioms WuPaper.R2RawMother.term_exact
#check @WuPaper.R2RawMother.ordered_raw_empty
#print axioms WuPaper.R2RawMother.ordered_raw_empty
#check @WuPaper.R2RawMother.rawTerm_masked_zero
#print axioms WuPaper.R2RawMother.rawTerm_masked_zero
#check @WuPaper.R2RawMother.rawTerm_unit_zero
#print axioms WuPaper.R2RawMother.rawTerm_unit_zero
#check @WuPaper.R2RawMother.exceptionTerm_unit_eq_prefix
#print axioms WuPaper.R2RawMother.exceptionTerm_unit_eq_prefix
