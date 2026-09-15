import MathlibNt.Wu2008DoubleSieve.SquareExceptions
import MathlibNt.Wu2008DoubleSieve.Counting

/-!
# The pointwise lower weight of Wu (2008), Lemma 2.1

The positive triple term uses the already constructed `firstTwoTriples`.
Unlike the upper-weight argument, its exact cardinality is needed here.
All sifting inequalities are strict; prime-square and common-factor
exceptions are kept separate.
-/

namespace Wu2008DoubleSieve

open Finset
open scoped Classical ArithmeticFunction.Omega

theorem firstTwoTriples_first_two_unique {s : Finset ℕ} {a b c d e f : ℕ}
    (h : (a, b, c) ∈ firstTwoTriples s) (h' : (d, e, f) ∈ firstTwoTriples s) :
    a = d ∧ b = e := by
  obtain ⟨ha, hb, _, hab, _, hmin⟩ := mem_firstTwoTriples.mp h
  obtain ⟨hd, he, _, hde, _, hmin'⟩ := mem_firstTwoTriples.mp h'
  have hbe : b = e := by
    rcases lt_trichotomy b e with hlt | heq | hgt
    · have hbd := hmin' b hb hlt
      have had := hmin' a ha (hab.trans hlt)
      omega
    · exact heq
    · have hea := hmin e he hgt
      have hda := hmin d hd (hde.trans hgt)
      omega
  exact ⟨hmin' a ha (by omega), hbe⟩

/-- Exact cancellation of the positive triple term, not just an upper weight. -/
theorem firstTwoTriples_card (s : Finset ℕ) :
    (firstTwoTriples s).card = s.card - 2 := by
  by_cases ht : (firstTwoTriples s).Nonempty
  · obtain ⟨⟨a, b, c⟩, ht⟩ := ht
    obtain ⟨ha, hb, _, hab, _, _⟩ := mem_firstTwoTriples.mp ht
    have hb' : b ∈ s.erase a := mem_erase.mpr ⟨by omega, hb⟩
    have hu : (firstTwoTriples s).card ≤ ((s.erase a).erase b).card := by
      apply card_le_card_of_injOn (fun t : ℕ × ℕ × ℕ => t.2.2)
      · rintro ⟨d, e, f⟩ hf
        change f ∈ (s.erase a).erase b
        obtain ⟨hd, he⟩ := firstTwoTriples_first_two_unique hf ht
        obtain ⟨_, _, hfs, hde, hef, _⟩ := mem_firstTwoTriples.mp hf
        exact mem_erase.mpr ⟨by omega, mem_erase.mpr ⟨by omega, hfs⟩⟩
      · rintro ⟨d, e, f⟩ hf ⟨g, i, j⟩ hj heq
        obtain ⟨hdg, hei⟩ := firstTwoTriples_first_two_unique hf hj
        dsimp at heq
        simp only [Prod.mk.injEq]
        exact ⟨hdg, hei, heq⟩
    have hca := card_erase_add_one ha
    have hcb := card_erase_add_one hb'
    have hl := card_le_two_add_firstTwoTriples s
    omega
  · have he : firstTwoTriples s = ∅ := not_nonempty_iff_eq_empty.mp ht
    have hl := card_le_two_add_firstTwoTriples s
    rw [he, card_empty] at hl ⊢
    omega

theorem two_sub_card_add_triples (s : Finset ℕ) :
    2 - (s.card : ℤ) + ((firstTwoTriples s).card : ℤ) =
      ((2 - s.card : ℕ) : ℤ) := by
  rw [firstTwoTriples_card]
  omega

/-- The source's two pair ranges, joined without identifying their coefficients.
The condition `a*b^2 < N` is exactly `b < sqrt(N/a)` for positive primes. -/
noncomputable def lowerPairs (N M : ℕ) (z w : ℝ) : Finset (ℕ × ℕ) :=
  ((primeWindow M z (N + 1)) ×ˢ (primeWindow M w (N + 1))).filter
    (fun t => t.1 < t.2 ∧ t.1 * t.2 ^ 2 < N)

def lowerPairSurvives (M n : ℕ) (t : ℕ × ℕ) : Prop :=
  t.1 * t.2 ∣ n ∧ Sifted (M * t.1) (n / (t.1 * t.2)) (t.2 : ℝ)

noncomputable def lowerPairPenalty (N M n : ℕ) (z w : ℝ) : ℤ :=
  ∑ t ∈ lowerPairs N M z w,
    if lowerPairSurvives M n t then (if w ≤ (t.1 : ℝ) then 2 else 1) else 0

noncomputable def lowerWeight (N M n : ℕ) (z w : ℝ) : ℤ :=
  2 - ((divisorsIn (primeWindow M z w) n).card : ℤ) +
    ((firstTwoTriples (divisorsIn (primeWindow M z w) n)).card : ℤ) -
    lowerPairPenalty N M n z w

theorem lowerPairPenalty_nonneg (N M n : ℕ) (z w : ℝ) :
    0 ≤ lowerPairPenalty N M n z w := by
  apply sum_nonneg
  intro t _
  split_ifs <;> norm_num

/-- Crucially, squareful terms require only a one-sided constant bound. -/
theorem lowerWeight_le_two (N M n : ℕ) (z w : ℝ) :
    lowerWeight N M n z w ≤ 2 := by
  unfold lowerWeight
  rw [two_sub_card_add_triples]
  have h := lowerPairPenalty_nonneg N M n z w
  omega

theorem lowerWeight_nonpos_of_two_small {N M n : ℕ} {z w : ℝ}
    (h : 2 ≤ (divisorsIn (primeWindow M z w) n).card) :
    lowerWeight N M n z w ≤ 0 := by
  unfold lowerWeight
  rw [two_sub_card_add_triples]
  have hp := lowerPairPenalty_nonneg N M n z w
  omega

/-- The first two distinct prime factors survive the source pair sieve. -/
theorem first_two_lowerPairSurvives {M n a b c : ℕ}
    (ht : (a, b, c) ∈ firstTwoTriples n.primeFactors) :
    lowerPairSurvives M n (a, b) := by
  obtain ⟨ha, hb, _, hab, _, hmin⟩ := mem_firstTwoTriples.mp ht
  obtain ⟨hap, had, hn⟩ := Nat.mem_primeFactors.mp ha
  obtain ⟨hbp, hbd, _⟩ := Nat.mem_primeFactors.mp hb
  have habcop := (Nat.coprime_primes hap hbp).mpr (ne_of_lt hab)
  have habd := habcop.mul_dvd_of_dvd_of_dvd had hbd
  refine ⟨habd, ?_⟩
  apply (sifted_quotient_iff habd ?_).mpr
  · intro q hq hqMa hqb hqn
    have hqa := hmin q (Nat.mem_primeFactors.mpr ⟨hq, hqn, hn⟩)
      (by exact_mod_cast hqb)
    have hcop := (Nat.coprime_mul_iff_right.mp hqMa).2
    exact ((Nat.coprime_primes hq hap).mp hcop) hqa
  · intro q hq hqMa hqb
    exact Nat.coprime_mul_iff_right.mpr
      ⟨(Nat.coprime_mul_iff_right.mp hqMa).2,
        (Nat.coprime_primes hq hbp).mpr (by
          have : q < b := by exact_mod_cast hqb
          omega)⟩

theorem first_two_size_bound {N n a b c : ℕ} (hnN : n ≤ N)
    (ht : (a, b, c) ∈ firstTwoTriples n.primeFactors) :
    a * b ^ 2 < N := by
  obtain ⟨ha, hb, hc, hab, hbc, _⟩ := mem_firstTwoTriples.mp ht
  obtain ⟨hap, had, hn⟩ := Nat.mem_primeFactors.mp ha
  obtain ⟨hbp, hbd, _⟩ := Nat.mem_primeFactors.mp hb
  obtain ⟨hcp, hcd, _⟩ := Nat.mem_primeFactors.mp hc
  have hd := (triple_dvd_iff hap hbp hcp hab hbc).mpr ⟨had, hbd, hcd⟩
  have hle := (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hd).trans hnN
  have ha0 := hap.pos
  have hb0 := hbp.pos
  calc
    a * b ^ 2 < a * b * c := by
      rw [pow_two, ← mul_assoc]
      exact Nat.mul_lt_mul_of_pos_left hbc (Nat.mul_pos ha0 hb0)
    _ ≤ N := hle

theorem primeFactor_ge_cutoff {M n q : ℕ} {z : ℝ}
    (hcop : n.Coprime M) (hs : Sifted M n z) (hq : q ∈ n.primeFactors) :
    z ≤ (q : ℝ) := by
  obtain ⟨hqp, hqd, _⟩ := Nat.mem_primeFactors.mp hq
  exact le_of_not_gt (fun hlt => hs q hqp (hcop.of_dvd_left hqd) hlt hqd)

theorem small_primeFactor_mem {M n q : ℕ} {z w : ℝ}
    (hcop : n.Coprime M) (hs : Sifted M n z) (hq : q ∈ n.primeFactors)
    (hqw : (q : ℝ) < w) :
    q ∈ divisorsIn (primeWindow M z w) n := by
  obtain ⟨hqp, hqd, _⟩ := Nat.mem_primeFactors.mp hq
  exact mem_filter.mpr ⟨mem_primeWindow.mpr
    ⟨hqp, hcop.of_dvd_left hqd, primeFactor_ge_cutoff hcop hs hq, hqw⟩, hqd⟩

/-- If at most one factor is below `w`, the source pair has the needed sign
and coefficient. Three distinct factors suffice, before squarefree reduction. -/
theorem lowerPairPenalty_ge_deficit {N M n : ℕ} {z w : ℝ}
    (hnN : n ≤ N) (hcop : n.Coprime M) (hs : Sifted M n z)
    (hthree : 3 ≤ n.primeFactors.card)
    (hsmall : (divisorsIn (primeWindow M z w) n).card ≤ 1) :
    ((2 - (divisorsIn (primeWindow M z w) n).card : ℕ) : ℤ) ≤
      lowerPairPenalty N M n z w := by
  have hnon : (firstTwoTriples n.primeFactors).Nonempty := by
    apply card_pos.mp
    rw [firstTwoTriples_card]
    omega
  obtain ⟨⟨a, b, c⟩, ht⟩ := hnon
  obtain ⟨ha, hb, _, hab, _, _⟩ := mem_firstTwoTriples.mp ht
  obtain ⟨hap, had, hn⟩ := Nat.mem_primeFactors.mp ha
  obtain ⟨hbp, hbd, _⟩ := Nat.mem_primeFactors.mp hb
  have haN := (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) had).trans hnN
  have hbN := (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hbd).trans hnN
  have hbw : w ≤ (b : ℝ) := by
    by_contra h
    have hbsmall := small_primeFactor_mem hcop hs hb (lt_of_not_ge h)
    have hasmall := small_primeFactor_mem hcop hs ha
      ((by exact_mod_cast hab : (a : ℝ) < b).trans (lt_of_not_ge h))
    have hcard : 2 ≤ (divisorsIn (primeWindow M z w) n).card := by
      have hsub : {a, b} ⊆ divisorsIn (primeWindow M z w) n := by
        intro q hq
        simp only [mem_insert, mem_singleton] at hq
        rcases hq with rfl | rfl <;> assumption
      have h := card_le_card hsub
      simpa [ne_of_lt hab] using h
    omega
  have hpair : (a, b) ∈ lowerPairs N M z w := by
    apply mem_filter.mpr
    refine ⟨mem_product.mpr ⟨?_, ?_⟩, hab, first_two_size_bound hnN ht⟩
    · exact mem_primeWindow.mpr ⟨hap, hcop.of_dvd_left had,
        primeFactor_ge_cutoff hcop hs ha, by exact_mod_cast (show a < N + 1 by omega)⟩
    · exact mem_primeWindow.mpr ⟨hbp, hcop.of_dvd_left hbd, hbw,
        by exact_mod_cast (show b < N + 1 by omega)⟩
  have hsurv := first_two_lowerPairSurvives (M := M) ht
  have hsum : (if w ≤ (a : ℝ) then (2 : ℤ) else 1) ≤
      lowerPairPenalty N M n z w := by
    have h := single_le_sum (s := lowerPairs N M z w)
      (f := fun t => if lowerPairSurvives M n t then
        (if w ≤ (t.1 : ℝ) then (2 : ℤ) else 1) else 0)
      (fun t _ => by split_ifs <;> norm_num) hpair
    simpa only [lowerPairPenalty, if_pos hsurv] using h
  by_cases haw : w ≤ (a : ℝ)
  · rw [if_pos haw] at hsum
    omega
  · rw [if_neg haw] at hsum
    have ha' := small_primeFactor_mem hcop hs ha (lt_of_not_ge haw)
    have hpos := card_pos.mpr (show (divisorsIn (primeWindow M z w) n).Nonempty from
      ⟨a, ha'⟩)
    omega

theorem lowerWeight_nonpos_of_three_factors {N M n : ℕ} {z w : ℝ}
    (hnN : n ≤ N) (hcop : n.Coprime M) (hs : Sifted M n z)
    (hthree : 3 ≤ n.primeFactors.card) :
    lowerWeight N M n z w ≤ 0 := by
  by_cases hsmall : 2 ≤ (divisorsIn (primeWindow M z w) n).card
  · exact lowerWeight_nonpos_of_two_small hsmall
  · have h := lowerPairPenalty_ge_deficit (z := z) (w := w)
      hnN hcop hs hthree (by omega)
    unfold lowerWeight
    rw [two_sub_card_add_triples]
    omega

theorem primeFactors_card_eq_omega_of_squarefree {n : ℕ} (hn : Squarefree n) :
    n.primeFactors.card = Ω n := by
  have h := (ArithmeticFunction.cardDistinctFactors_eq_cardFactors_iff_squarefree
    hn.ne_zero).mpr hn
  simpa only [ArithmeticFunction.cardDistinctFactors_apply,
    ← List.card_toFinset, Nat.toFinset_factors] using h

/-- Wu04 (9.3), doubled. Multiplicity-sensitive `Omega` is used only after
the genuine squarefree reduction. No Cai--Lu parameter restriction is needed. -/
theorem lowerWeight_le_omega_indicator {N M n : ℕ} {z w : ℝ}
    (hnN : n ≤ N) (hcop : n.Coprime M) (hs : Sifted M n z)
    (hsq : Squarefree n) :
    lowerWeight N M n z w ≤ if Ω n ≤ 2 then 2 else 0 := by
  split_ifs with h
  · exact lowerWeight_le_two N M n z w
  · apply lowerWeight_nonpos_of_three_factors hnN hcop hs
    rw [primeFactors_card_eq_omega_of_squarefree hsq]
    omega

end Wu2008DoubleSieve
