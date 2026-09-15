import MathlibNt.Wu2008DoubleSieve.SecondFunctionalMotherSource

namespace WuPaper.R2RawMother

open Finset Wu2008DoubleSieve
open scoped Classical

theorem source_modulus_dichotomy (N D M K : ℕ) (z : ℝ) (hKD : K ∣ D) :
    sourceSieveCarrier N D M z =
      if Sifted M D z then sourceSieveCarrier N D (M * K) z else ∅ := by
  by_cases h : Sifted M D z
  · rw [if_pos h]
    ext ell
    simp only [sourceSieveCarrier, mem_filter]
    constructor
    · rintro ⟨hr, hp, hd, hs⟩
      exact ⟨hr, hp, hd, fun q hq hc hz =>
        hs q hq (hc.of_dvd_right (dvd_mul_right M K)) hz⟩
    · rintro ⟨hr, hp, hd, hs⟩
      refine ⟨hr, hp, hd, ?_⟩
      intro q hq hc hz
      have hqK : ¬q ∣ K := fun hdiv => h q hq hc hz (hdiv.trans hKD)
      exact hs q hq (hc.mul_right (hq.coprime_iff_not_dvd.mpr hqK)) hz
  · rw [if_neg h, sourceSieveCarrier_eq_ite, if_neg h]

noncomputable def rawCarrier (N d : ℕ) (l : List ℕ) : Finset ℕ :=
  sourceSieveCarrier N (d * l.prod) (d * N) (l.getD (l.length - 2) 0)

def labelsSurvive (N d : ℕ) (l : List ℕ) : Prop :=
  Sifted (d * N) (d * l.prod) (l.getD (l.length - 2) 0)

noncomputable def exceptionalCarrier (N d : ℕ) (l : List ℕ) : Finset ℕ :=
  if labelsSurvive N d l then ∅ else secondFunctionalMotherPrefixCarrier N d l

theorem rawCarrier_dichotomy (N d : ℕ) (l : List ℕ) :
    rawCarrier N d l =
      if labelsSurvive N d l then secondFunctionalMotherPrefixCarrier N d l else ∅ := by
  have htake : (l.take (l.length - 2)).prod ∣ l.prod :=
    ⟨(l.drop (l.length - 2)).prod, by
      rw [← List.prod_append, List.take_append_drop]⟩
  have h := source_modulus_dichotomy N (d * l.prod) (d * N)
    (l.take (l.length - 2)).prod (l.getD (l.length - 2) 0)
    (htake.trans (dvd_mul_left l.prod d))
  simpa only [rawCarrier, labelsSurvive, fourthRowMotherPrefixCarrier,
    mul_assoc, mul_comm N] using h

theorem prefix_card_exact (N d : ℕ) (l : List ℕ) :
    ((secondFunctionalMotherPrefixCarrier N d l).card : ℝ) =
      (rawCarrier N d l).card + (exceptionalCarrier N d l).card := by
  rw [rawCarrier_dichotomy]
  unfold exceptionalCarrier
  split_ifs <;> simp

theorem rawCarrier_empty_of_selected {N d q : ℕ} {l : List ℕ}
    (hq : q.Prime) (hqN : q.Coprime (d * N)) (hql : q ∈ l)
    (hqcut : (q : ℝ) < l.getD (l.length - 2) 0) :
    rawCarrier N d l = ∅ :=
  sourceSieveCarrier_eq_empty_of_selected hq hqN
    ((List.dvd_prod hql).trans (dvd_mul_left l.prod d)) hqcut

theorem exceptional_eq_prefix_of_selected {N d q : ℕ} {l : List ℕ}
    (hq : q.Prime) (hqN : q.Coprime (d * N)) (hql : q ∈ l)
    (hqcut : (q : ℝ) < l.getD (l.length - 2) 0) :
    exceptionalCarrier N d l = secondFunctionalMotherPrefixCarrier N d l := by
  apply if_neg
  intro hs
  exact hs q hq hqN hqcut
    ((List.dvd_prod hql).trans (dvd_mul_left l.prod d))

theorem raw_five_empty {N d p q r s t : ℕ}
    (hp : p.Prime) (hpN : p.Coprime (d * N)) (hps : p < s) :
    rawCarrier N d [p, q, r, s, t] = ∅ := by
  apply rawCarrier_empty_of_selected hp hpN (by simp)
  simpa using (show (p : ℝ) < s by exact_mod_cast hps)

theorem raw_six_empty {N d p q r s t u : ℕ}
    (hp : p.Prime) (hpN : p.Coprime (d * N)) (hpt : p < t) :
    rawCarrier N d [p, q, r, s, t, u] = ∅ := by
  apply rawCarrier_empty_of_selected hp hpN (by simp)
  simpa using (show (p : ℝ) < t by exact_mod_cast hpt)

theorem exceptional_card_floor {N d : ℕ} (l : List ℕ)
    (hN : 4 ≤ N) (he : Even N) :
    (exceptionalCarrier N d l).card ≤
      if labelsSurvive N d l then 0 else N / (d * l.prod) := by
  unfold exceptionalCarrier
  split_ifs
  · simp
  · calc
      _ ≤ ((range (N + 1)).filter fun m => m ≠ 0 ∧ d * l.prod ∣ m).card := by
        apply card_le_card_of_injOn (fun ell => N - ell)
        · intro ell hell
          change N - ell ∈ _
          obtain ⟨hr, hp, hd, _⟩ := mem_filter.mp hell
          have hlt := omega3_prime_output_lt hN he hp
            (Nat.le_of_lt_succ (mem_range.mp hr))
          exact mem_filter.mpr ⟨mem_range.mpr (by omega), by omega, hd⟩
        · intro ell hell ell' hell' h
          have hl := mem_range.mp (mem_filter.mp hell).1
          have hl' := mem_range.mp (mem_filter.mp hell').1
          dsimp at h
          omega
      _ = _ := Nat.card_multiples' N (d * l.prod)

end WuPaper.R2RawMother

#check @WuPaper.R2RawMother.source_modulus_dichotomy
#print axioms WuPaper.R2RawMother.source_modulus_dichotomy
#check @WuPaper.R2RawMother.rawCarrier
#print axioms WuPaper.R2RawMother.rawCarrier
#check @WuPaper.R2RawMother.labelsSurvive
#print axioms WuPaper.R2RawMother.labelsSurvive
#check @WuPaper.R2RawMother.exceptionalCarrier
#print axioms WuPaper.R2RawMother.exceptionalCarrier
#check @WuPaper.R2RawMother.rawCarrier_dichotomy
#print axioms WuPaper.R2RawMother.rawCarrier_dichotomy
#check @WuPaper.R2RawMother.prefix_card_exact
#print axioms WuPaper.R2RawMother.prefix_card_exact
#check @WuPaper.R2RawMother.rawCarrier_empty_of_selected
#print axioms WuPaper.R2RawMother.rawCarrier_empty_of_selected
#check @WuPaper.R2RawMother.exceptional_eq_prefix_of_selected
#print axioms WuPaper.R2RawMother.exceptional_eq_prefix_of_selected
#check @WuPaper.R2RawMother.raw_five_empty
#print axioms WuPaper.R2RawMother.raw_five_empty
#check @WuPaper.R2RawMother.raw_six_empty
#print axioms WuPaper.R2RawMother.raw_six_empty
#check @WuPaper.R2RawMother.exceptional_card_floor
#print axioms WuPaper.R2RawMother.exceptional_card_floor
