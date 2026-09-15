import MathlibNt.Wu2008DoubleSieve.Omega3NonCoprime

/-! # The actual labelled missing mass in a non-coprime sieve modulus -/

namespace Wu2008DoubleSieve

open Finset Real
open scoped Classical

theorem omega3_prime_fibre_card_le {N : ℕ} {δ s : ℝ} {c : Omega3CofactorIndex}
    (he : 0 < omega3CofactorValue c) :
    ((omega3CofactorPrimeFibreLE N δ s c).card : ℝ) ≤
      (N : ℝ) / omega3CofactorValue c := by
  have hsub : omega3CofactorPrimeFibreLE N δ s c ⊆
      Icc 1 (N / omega3CofactorValue c) := by
    intro p hp
    obtain ⟨_, hprime, _, _, hsize⟩ := mem_filter.mp hp
    exact mem_Icc.mpr ⟨hprime.one_lt.le,
      (Nat.le_div_iff_mul_le he).mpr (by simpa only [mul_comm] using hsize)⟩
  have hcard : (omega3CofactorPrimeFibreLE N δ s c).card ≤
      N / omega3CofactorValue c := by
    simpa only [Nat.card_Icc, Nat.add_sub_cancel] using card_le_card hsub
  exact (show ((omega3CofactorPrimeFibreLE N δ s c).card : ℝ) ≤
      (N / omega3CofactorValue c : ℕ) by exact_mod_cast hcard).trans (Nat.cast_div_le ..)

theorem omega3_non_coprime_mass_le {i N q : ℕ} {δ s t Y C : ℝ}
    (W : Fin i → Finset ℕ) (hY : 0 < Y) (hC : 0 ≤ C)
    (hq : 0 < q) (hqN : q ≤ N)
    (hgeom : ∀ c ∈ omega3CofactorLabels N δ s t W,
      0 < omega3CofactorValue c ∧ omega3CofactorValue c ≤ N ∧
      ∀ p : ℕ, p.Prime → p ∣ omega3CofactorValue c → Y ≤ p)
    (hfibre : ∀ e : ℕ,
      (∑ c ∈ (omega3CofactorLabels N δ s t W).filter
          (fun c => omega3CofactorValue c = e), (convolutionCoeff W c.1 : ℝ)) ≤ C) :
    (∑ c ∈ (omega3CofactorLabels N δ s t W).filter
        (fun c => ¬ (omega3CofactorValue c).Coprime q),
      (convolutionCoeff W c.1 : ℝ) * (omega3CofactorPrimeFibreLE N δ s c).card) ≤
      C * N * ((1 + log N) * log N / (Y * log 2)) := by
  let L := omega3CofactorLabels N δ s t W
  let E := L.image omega3CofactorValue
  have hE : ∀ e ∈ E, 0 < e ∧ e ≤ N := by
    intro e he
    obtain ⟨c, hc, rfl⟩ := mem_image.mp he
    exact ⟨(hgeom c hc).1, (hgeom c hc).2.1⟩
  have hrough : ∀ e ∈ E, ∀ p : ℕ, p.Prime → p ∣ e → Y ≤ p := by
    intro e he
    obtain ⟨c, hc, rfl⟩ := mem_image.mp he
    exact (hgeom c hc).2.2
  have hinner (e : ℕ) (he : e ∈ E) :
      (∑ c ∈ L.filter (fun c => omega3CofactorValue c = e),
        (convolutionCoeff W c.1 : ℝ) *
          (if ¬ (omega3CofactorValue c).Coprime q then
            ((omega3CofactorPrimeFibreLE N δ s c).card : ℝ) else 0)) ≤
        if ¬ e.Coprime q then C * N * (1 / (e : ℝ)) else 0 := by
    by_cases hbad : ¬ e.Coprime q
    · rw [if_pos hbad]
      calc
        _ ≤ ∑ c ∈ L.filter (fun c => omega3CofactorValue c = e),
            (convolutionCoeff W c.1 : ℝ) * ((N : ℝ) / e) := by
          apply sum_le_sum
          intro c hc
          obtain ⟨hc, hce⟩ := mem_filter.mp hc
          rw [hce, if_pos hbad]
          apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
          simpa only [hce] using omega3_prime_fibre_card_le (hgeom c hc).1
        _ = (∑ c ∈ L.filter (fun c => omega3CofactorValue c = e),
            (convolutionCoeff W c.1 : ℝ)) * ((N : ℝ) / e) := (sum_mul ..).symm
        _ ≤ C * ((N : ℝ) / e) :=
          mul_le_mul_of_nonneg_right (hfibre e) (by positivity)
        _ = _ := by ring
    · rw [if_neg hbad]
      apply le_of_eq
      apply sum_eq_zero
      intro c hc
      rw [(mem_filter.mp hc).2, if_neg hbad, mul_zero]
  calc
    _ = ∑ c ∈ L, (convolutionCoeff W c.1 : ℝ) *
        (if ¬ (omega3CofactorValue c).Coprime q then
          ((omega3CofactorPrimeFibreLE N δ s c).card : ℝ) else 0) := by
      rw [sum_filter]
      simp only [mul_ite, mul_zero, L]
    _ = ∑ e ∈ E, ∑ c ∈ L.filter (fun c => omega3CofactorValue c = e),
        (convolutionCoeff W c.1 : ℝ) *
          (if ¬ (omega3CofactorValue c).Coprime q then
            ((omega3CofactorPrimeFibreLE N δ s c).card : ℝ) else 0) :=
      omega3_cofactor_label_fibres N δ s t W _
    _ ≤ ∑ e ∈ E, if ¬ e.Coprime q then C * N * (1 / (e : ℝ)) else 0 :=
      sum_le_sum hinner
    _ = C * N * ∑ e ∈ E.filter (fun e => ¬ e.Coprime q), 1 / (e : ℝ) := by
      rw [sum_filter, mul_sum]
      apply sum_congr rfl
      intro e _
      split_ifs <;> ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (omega3_rough_non_coprime_reciprocal_le N q E hY hq hqN hE hrough)
      (mul_nonneg hC (Nat.cast_nonneg _))

end Wu2008DoubleSieve
