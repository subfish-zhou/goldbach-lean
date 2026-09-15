import R2MotherTerms

namespace WuPaper.R2Mother

open Finset Wu2008DoubleSieve
open scoped Classical

private theorem source_count_of_sifted (N d M : ℕ) (z : ℝ) (h : Sifted M d z) :
    sourceSieveCount N d M z = sieveCount N d M z := by
  unfold sourceSieveCount sieveCount
  rw [sourceSieveCarrier_eq_ite, if_pos h]

private theorem source_base (N : ℕ) (z : ℝ) :
    sourceSieveCount N 1 N z = sieveCount N 1 N z := by
  unfold sourceSieveCount sieveCount
  rw [sourceSieveCarrier_of_dvd_modulus N (one_dvd N)]

private theorem source_single_sum (N : ℕ) (z v : ℝ) :
    (∑ p ∈ primeWindow N z v, sourceSieveCount N p N z) =
      ∑ p ∈ primeWindow N z v, sieveCount N p N z := by
  apply sum_congr rfl
  intro p hp
  obtain ⟨hp, _, hz, _⟩ := mem_primeWindow.mp hp
  exact source_count_of_sifted N p N z (sifted_prime_of_le hp hz)

private theorem source_fifth_sum (N : ℕ) (z w : ℝ) :
    (∑ c ∈ primeWindow N z w, ∑ b ∈ primeWindow N z (c : ℝ),
      sourceSieveCount N (b * c) N z) = upsilon5 N z w := by
  apply sum_congr rfl
  intro c hc
  apply sum_congr rfl
  intro b hb
  obtain ⟨hc, _, hzc, _⟩ := mem_primeWindow.mp hc
  obtain ⟨hb, _, hzb, _⟩ := mem_primeWindow.mp hb
  exact source_count_of_sifted N (b * c) N z
    ((sifted_mul_iff N b c z).mpr
      ⟨sifted_prime_of_le hb hzb, sifted_prime_of_le hc hzc⟩)

private theorem source_sixth_sum (N : ℕ) {z w : ℝ} (u : ℝ) (hzw : z ≤ w) :
    (∑ c ∈ primeWindow N w u, ∑ b ∈ primeWindow N z w,
      sourceSieveCount N (b * c) N z) = upsilon6 N z w u := by
  apply sum_congr rfl
  intro c hc
  apply sum_congr rfl
  intro b hb
  obtain ⟨hc, _, hwc, _⟩ := mem_primeWindow.mp hc
  obtain ⟨hb, _, hzb, _⟩ := mem_primeWindow.mp hb
  exact source_count_of_sifted N (b * c) N z
    ((sifted_mul_iff N b c z).mpr
      ⟨sifted_prime_of_le hb hzb, sifted_prime_of_le hc (hzw.trans hwc)⟩)

private theorem source_pair_sum (N : ℕ) (z w : ℝ)
    (F : ℕ × ℕ → Prop) [DecidablePred F] :
    (∑ t ∈ (lowerPairs N N z w).filter F,
      sourceSieveCount N (t.1 * t.2) (N * t.1) (t.2 : ℝ)) =
    ∑ t ∈ (lowerPairs N N z w).filter F,
      sieveCount N (t.1 * t.2) (N * t.1) (t.2 : ℝ) := by
  apply sum_congr rfl
  intro t ht
  have hb := (mem_lowerPairs_source.mp (mem_filter.mp ht).1).2.1
  unfold sourceSieveCount sieveCount
  rw [source_strict_pair_carrier hb]

theorem source_four_count_zero {N a b c d : ℕ}
    (ha : a.Prime) (haN : a.Coprime N) (hab : a < b) :
    sourceSieveCount N (a * b * c * d) N (b : ℝ) = 0 := by
  have hdiv : a ∣ a * b * c * d := by
    exact ((dvd_mul_right a b).trans (dvd_mul_right (a * b) c)).trans
      (dvd_mul_right (a * b * c) d)
  unfold sourceSieveCount
  rw [sourceSieveCarrier_eq_empty_of_selected ha haN hdiv
    (by exact_mod_cast hab : (a : ℝ) < b)]
  simp only [card_empty, Int.natCast_zero]

theorem source_upsilon10_zero (N : ℕ) (z w : ℝ) :
    (∑ t ∈ s3DistinctQuadruples N (orderedTriples (primeWindow N z w)),
      sourceSieveCount N (t.1 * t.2.1 * t.2.2.1 * t.2.2.2) N (t.2.1 : ℝ)) = 0 := by
  apply sum_eq_zero
  rintro ⟨a, b, c, d⟩ ht
  obtain ⟨ha, haN, _, _, _, _, _, _, _, _, hab, _, _⟩ :=
    mem_s3_first_quadruples.mp ht
  exact source_four_count_zero ha haN hab

theorem source_upsilon11_zero (N : ℕ) (z w V : ℝ) :
    (∑ t ∈ s3Upsilon11Range N z w V,
      sourceSieveCount N (t.1 * t.2.1 * t.2.2.1 * t.2.2.2) N (t.2.1 : ℝ)) = 0 := by
  apply sum_eq_zero
  rintro ⟨a, b, c, d⟩ ht
  obtain ⟨ha, haN, _, _, _, _, _, _, _, hab, _, _, _, _⟩ :=
    mem_s3Upsilon11Range.mp ht
  exact source_four_count_zero ha haN hab

theorem unscaled_eq_firstNine_add_crossing (N : ℕ) {z w : ℝ}
    (u v V : ℝ) (hzw : z ≤ w) :
    finiteElevenUnscaled N z w u v V =
      firstNine N z w u v + variableS3CrossingCorrection N w u := by
  have h9 := variableS3Main_eq_source_add_correction N w u
  unfold finiteElevenUnscaled finiteElevenExpression
  rw [source_base, source_base, source_single_sum, source_single_sum,
    source_fifth_sum, source_sixth_sum N u hzw,
    source_pair_sum, source_pair_sum, source_upsilon10_zero, source_upsilon11_zero]
  change _ - sourceVariableS3Main N w u - 0 - 0 = _
  unfold firstNine upsilon1 upsilon2 upsilon3 upsilon4 upsilon7 upsilon8 upsilon9
  unfold variableS3Main at h9
  omega

theorem quotient_to_unscaled_signed (N : ℕ) {z w : ℝ}
    (u v V : ℝ) (hzw : z ≤ w) :
    eleven N z w u v V =
      finiteElevenUnscaled N z w u v V - variableS3CrossingCorrection N w u -
        upsilon10 N z w - upsilon11 N z w V := by
  rw [unscaled_eq_firstNine_add_crossing N u v V hzw, eleven_eq_firstNine]
  omega

theorem literal_transport_nonpos (N : ℕ) {z w : ℝ}
    (u v V : ℝ) (hzw : z ≤ w) :
    eleven N z w u v V ≤ finiteElevenUnscaled N z w u v V := by
  rw [quotient_to_unscaled_signed N u v V hzw]
  have hc : 0 ≤ variableS3CrossingCorrection N w u := by
    apply sum_nonneg
    intro t _
    split_ifs
    · exact sieveCount_nonneg _ _ _ _
    · exact le_refl 0
  have h10 : 0 ≤ upsilon10 N z w :=
    sum_nonneg (fun _ _ => sieveCount_nonneg _ _ _ _)
  have h11 : 0 ≤ upsilon11 N z w V :=
    sum_nonneg (fun _ _ => sieveCount_nonneg _ _ _ _)
  omega

end WuPaper.R2Mother

#check @WuPaper.R2Mother.source_four_count_zero
#check @WuPaper.R2Mother.source_upsilon10_zero
#check @WuPaper.R2Mother.source_upsilon11_zero
#check @WuPaper.R2Mother.unscaled_eq_firstNine_add_crossing
#check @WuPaper.R2Mother.quotient_to_unscaled_signed
#check @WuPaper.R2Mother.literal_transport_nonpos
#print axioms WuPaper.R2Mother.source_four_count_zero
#print axioms WuPaper.R2Mother.source_upsilon10_zero
#print axioms WuPaper.R2Mother.source_upsilon11_zero
#print axioms WuPaper.R2Mother.unscaled_eq_firstNine_add_crossing
#print axioms WuPaper.R2Mother.quotient_to_unscaled_signed
#print axioms WuPaper.R2Mother.literal_transport_nonpos
