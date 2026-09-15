import MathlibNt.Wu2008DoubleSieve.SourceCarriers

/-!
# S3 carrier majorants and finite Delta2 comparisons

Wu08, Lemma 2.2 (pp. 369--371), uses a moving S3 cutoff and three
disjoint triple ranges. Wu04, p. 220, defines unscaled divisible
subsequences and strict sifting. These conventions are not silently
identified: the source carriers below exclude all selected primes.
The old crossing correction is a sum of whole carriers, not the
repeated-prime loss isolated here.
-/

namespace Wu2008DoubleSieve

open Finset
open scoped Classical

theorem sifted_modulus_mul {M n b : ℕ} {z : ℝ} (h : Sifted M n z) :
    Sifted (M * b) n z := by
  intro q hq hcop hqz
  exact h q hq (Nat.coprime_mul_iff_right.mp hcop).1 hqz

theorem siftedLE_modulus_mul {M n b : ℕ} {z : ℝ} (h : SiftedLE M n z) :
    SiftedLE (M * b) n z := by
  intro q hq hcop hqz
  exact h q hq (Nat.coprime_mul_iff_right.mp hcop).1 hqz

/-- Removing the selected prime `b` from the sifting primes is an upper
majorant. The lost restriction is active only for `b < z`. -/
theorem sifted_mul_modulus_iff {M n b : ℕ} {z : ℝ}
    (hb : b.Prime) (hbM : b.Coprime M) :
    Sifted M n z ↔
      Sifted (M * b) n z ∧ ((b : ℝ) < z → ¬b ∣ n) := by
  constructor
  · intro h
    exact ⟨sifted_modulus_mul h, fun hz => h b hb hbM hz⟩
  · rintro ⟨h, hbn⟩ q hq hqM hqz
    by_cases hqb : q = b
    · subst q
      exact hbn hqz
    · exact h q hq (Nat.coprime_mul_iff_right.mpr
        ⟨hqM, (Nat.coprime_primes hq hb).mpr hqb⟩) hqz

/-- The closed version retains the endpoint `b = z`. -/
theorem siftedLE_mul_modulus_iff {M n b : ℕ} {z : ℝ}
    (hb : b.Prime) (hbM : b.Coprime M) :
    SiftedLE M n z ↔
      SiftedLE (M * b) n z ∧ ((b : ℝ) ≤ z → ¬b ∣ n) := by
  constructor
  · intro h
    exact ⟨siftedLE_modulus_mul h, fun hz => h b hb hbM hz⟩
  · rintro ⟨h, hbn⟩ q hq hqM hqz
    by_cases hqb : q = b
    · subst q
      exact hbn hqz
    · exact h q hq (Nat.coprime_mul_iff_right.mpr
        ⟨hqM, (Nat.coprime_primes hq hb).mpr hqb⟩) hqz

theorem sieveCarrier_subset_mul_modulus (N d M b : ℕ) (z : ℝ) :
    sieveCarrier N d M z ⊆ sieveCarrier N d (M * b) z := by
  intro p hp
  obtain ⟨hp, hprime, hd, hs⟩ := mem_filter.mp hp
  exact mem_filter.mpr ⟨hp, hprime, hd, sifted_modulus_mul hs⟩

theorem sieveCarrierLE_subset_mul_modulus (N d M b : ℕ) (z : ℝ) :
    sieveCarrierLE N d M z ⊆ sieveCarrierLE N d (M * b) z := by
  intro p hp
  obtain ⟨hp, hprime, hd, hs⟩ := mem_filter.mp hp
  exact mem_filter.mpr ⟨hp, hprime, hd, siftedLE_modulus_mul hs⟩

theorem s3_sieveCount_le_mul_modulus (N d M b : ℕ) (z : ℝ) :
    sieveCount N d M z ≤ sieveCount N d (M * b) z :=
  Int.ofNat_le.mpr (card_le_card (sieveCarrier_subset_mul_modulus N d M b z))

theorem sieveCountLE_le_mul_modulus (N d M b : ℕ) (z : ℝ) :
    sieveCountLE N d M z ≤ sieveCountLE N d (M * b) z :=
  Int.ofNat_le.mpr (card_le_card (sieveCarrierLE_subset_mul_modulus N d M b z))

theorem sieveCarrier_mul_modulus_difference (N d M b : ℕ) (z : ℝ)
    (hb : b.Prime) (hbM : b.Coprime M) :
    sieveCarrier N d (M * b) z \ sieveCarrier N d M z =
      (sieveCarrier N d (M * b) z).filter
        (fun p => (b : ℝ) < z ∧ b ∣ (N - p) / d) := by
  ext p
  simp only [mem_sdiff, mem_filter, sieveCarrier]
  rw [sifted_mul_modulus_iff hb hbM]
  tauto

theorem sieveCarrierLE_mul_modulus_difference (N d M b : ℕ) (z : ℝ)
    (hb : b.Prime) (hbM : b.Coprime M) :
    sieveCarrierLE N d (M * b) z \ sieveCarrierLE N d M z =
      (sieveCarrierLE N d (M * b) z).filter
        (fun p => (b : ℝ) ≤ z ∧ b ∣ (N - p) / d) := by
  ext p
  simp only [mem_sdiff, mem_filter, sieveCarrierLE]
  rw [siftedLE_mul_modulus_iff hb hbM]
  tauto

/-- An exact count identity, not an estimate for the whole old crossing
correction. Each prime-complement index remains counted once. -/
theorem sieveCount_mul_modulus_eq_add_loss (N d M b : ℕ) (z : ℝ)
    (hb : b.Prime) (hbM : b.Coprime M) :
    sieveCount N d (M * b) z = sieveCount N d M z +
      (((sieveCarrier N d (M * b) z).filter
        (fun p => (b : ℝ) < z ∧ b ∣ (N - p) / d)).card : ℤ) := by
  have h := card_sdiff_add_card_eq_card (sieveCarrier_subset_mul_modulus N d M b z)
  rw [sieveCarrier_mul_modulus_difference N d M b z hb hbM] at h
  unfold sieveCount
  exact_mod_cast h.symm.trans (Nat.add_comm _ _)

theorem sieveCountLE_mul_modulus_eq_add_loss (N d M b : ℕ) (z : ℝ)
    (hb : b.Prime) (hbM : b.Coprime M) :
    sieveCountLE N d (M * b) z = sieveCountLE N d M z +
      (((sieveCarrierLE N d (M * b) z).filter
        (fun p => (b : ℝ) ≤ z ∧ b ∣ (N - p) / d)).card : ℤ) := by
  have h := card_sdiff_add_card_eq_card (sieveCarrierLE_subset_mul_modulus N d M b z)
  rw [sieveCarrierLE_mul_modulus_difference N d M b z hb hbM] at h
  unfold sieveCountLE
  exact_mod_cast h.symm.trans (Nat.add_comm _ _)

theorem selected_pair_loss_square {N a b p : ℕ} {z : ℝ}
    (hb : b.Prime) (hbNa : b.Coprime (N * a))
    (hp : p ∈ sieveCarrier N (a * b) (N * a * b) z \
      sieveCarrier N (a * b) (N * a) z) :
    (b : ℝ) < z ∧ a * b ^ 2 ∣ N - p := by
  rw [sieveCarrier_mul_modulus_difference N (a * b) (N * a) b z hb hbNa] at hp
  obtain ⟨hp, hbz, hbd⟩ := mem_filter.mp hp
  have hd := (mem_filter.mp hp).2.2.1
  refine ⟨hbz, ?_⟩
  have h := Nat.mul_dvd_mul_left (a * b) hbd
  rw [Nat.mul_div_cancel' hd] at h
  simpa only [pow_two, mul_assoc] using h

theorem selected_pair_closed_loss_square {N a b p : ℕ} {z : ℝ}
    (hb : b.Prime) (hbNa : b.Coprime (N * a))
    (hp : p ∈ sieveCarrierLE N (a * b) (N * a * b) z \
      sieveCarrierLE N (a * b) (N * a) z) :
    (b : ℝ) ≤ z ∧ a * b ^ 2 ∣ N - p := by
  rw [sieveCarrierLE_mul_modulus_difference N (a * b) (N * a) b z hb hbNa] at hp
  obtain ⟨hp, hbz, hbd⟩ := mem_filter.mp hp
  have hd := (mem_filter.mp hp).2.2.1
  refine ⟨hbz, ?_⟩
  have h := Nat.mul_dvd_mul_left (a * b) hbd
  rw [Nat.mul_div_cancel' hd] at h
  simpa only [pow_two, mul_assoc] using h

theorem sifted_mul_modulus_of_le {M n b : ℕ} {z : ℝ}
    (hb : b.Prime) (hz : z ≤ (b : ℝ)) :
    Sifted (M * b) n z ↔ Sifted M n z := by
  constructor
  · intro h q hq hqM hqz
    apply h q hq (Nat.coprime_mul_iff_right.mpr ⟨hqM, ?_⟩) hqz
    apply (Nat.coprime_primes hq hb).mpr
    intro he
    subst q
    exact (not_lt_of_ge hz) hqz
  · exact sifted_modulus_mul

theorem source_pair_majorant_eq_add_loss (N a b : ℕ) (z : ℝ)
    (hb : b.Prime) (hbNa : b.Coprime (N * a)) :
    sourceSieveCount N (a * b) ((a * b) * N) z =
      sieveCount N (a * b) (N * a) z +
        (((sieveCarrier N (a * b) (N * a * b) z).filter
          (fun p => (b : ℝ) < z ∧ b ∣ (N - p) / (a * b))).card : ℤ) := by
  unfold sourceSieveCount
  rw [sourceSieveCarrier_of_dvd_modulus N (dvd_mul_right (a * b) N)]
  have he : (a * b) * N = N * a * b := by ring
  rw [he]
  exact sieveCount_mul_modulus_eq_add_loss N (a * b) (N * a) b z hb hbNa

/-- At the strict triple cutoff `c`, removing `c` makes no difference.
Removing the earlier selected prime `b` loses exactly a repeated `b` in
the quotient, not the whole triple carrier. -/
theorem source_triple_majorant_eq_add_loss (N a b c : ℕ)
    (hb : b.Prime) (hc : c.Prime) (hbNa : b.Coprime (N * a)) :
    sourceSieveCount N (a * b * c) ((a * b * c) * N) (c : ℝ) =
      sieveCount N (a * b * c) (N * a) (c : ℝ) +
        (((sieveCarrier N (a * b * c) (N * a * b) (c : ℝ)).filter
          (fun p => (b : ℝ) < c ∧ b ∣ (N - p) / (a * b * c))).card : ℤ) := by
  unfold sourceSieveCount
  rw [sourceSieveCarrier_of_dvd_modulus N (dvd_mul_right (a * b * c) N)]
  have he : (a * b * c) * N = (N * a * b) * c := by ring
  have hcarrier : sieveCarrier N (a * b * c) ((N * a * b) * c) (c : ℝ) =
      sieveCarrier N (a * b * c) (N * a * b) (c : ℝ) := by
    ext p
    simp only [sieveCarrier, mem_filter, sifted_mul_modulus_of_le hc le_rfl]
  rw [he, hcarrier]
  exact sieveCount_mul_modulus_eq_add_loss N (a * b * c) (N * a) b c hb hbNa

theorem selected_triple_loss_square {N a b c p : ℕ} {z : ℝ}
    (hb : b.Prime) (hbNa : b.Coprime (N * a))
    (hp : p ∈ sieveCarrier N (a * b * c) (N * a * b) z \
      sieveCarrier N (a * b * c) (N * a) z) :
    (b : ℝ) < z ∧ a * b ^ 2 * c ∣ N - p := by
  rw [sieveCarrier_mul_modulus_difference N (a * b * c) (N * a) b z hb hbNa] at hp
  obtain ⟨hp, hbz, hbd⟩ := mem_filter.mp hp
  have hd := (mem_filter.mp hp).2.2.1
  refine ⟨hbz, ?_⟩
  have h := Nat.mul_dvd_mul_left (a * b * c) hbd
  rw [Nat.mul_div_cancel' hd] at h
  simpa only [pow_two, mul_assoc, mul_comm, mul_left_comm] using h

theorem sieveCount_le_source_selected_modulus (N d M : ℕ) (z : ℝ) :
    sieveCount N d M z ≤ sourceSieveCount N d (d * M) z := by
  have h := s3_sieveCount_le_mul_modulus N d M d z
  simpa only [sourceSieveCount, sieveCount,
    sourceSieveCarrier_of_dvd_modulus N (dvd_mul_right d M) z, mul_comm M d] using h

noncomputable def s3SourceMajorantMain (N : ℕ) (z w : ℝ) : ℤ :=
  ∑ t ∈ (lowerPairs N N z w).filter (fun t => (t.1 : ℝ) < w),
    sourceSieveCount N (t.1 * t.2) ((t.1 * t.2) * N)
      (Real.sqrt ((N : ℝ) / ((t.1 : ℝ) * t.2)))

noncomputable def s3SourceMajorantTriples (N : ℕ) (z w : ℝ) : ℤ :=
  ∑ t ∈ (lowerPairs N N z w).filter (fun t => (t.1 : ℝ) < w),
    ∑ c ∈ (primeWindow N (t.2 : ℝ)
        (Real.sqrt ((N : ℝ) / ((t.1 : ℝ) * t.2)))).filter (fun c => t.2 < c),
      sourceSieveCount N (t.1 * t.2 * c) ((t.1 * t.2 * c) * N) (c : ℝ)

theorem variableS3Main_le_source_majorant (N : ℕ) (z w : ℝ) :
    variableS3Main N z w ≤ s3SourceMajorantMain N z w := by
  apply sum_le_sum
  intro t _
  change sieveCount _ _ _ _ ≤ sourceSieveCount _ _ _ _
  unfold sourceSieveCount
  rw [sourceSieveCarrier_of_dvd_modulus N (dvd_mul_right (t.1 * t.2) N)]
  have h := s3_sieveCount_le_mul_modulus N (t.1 * t.2) (N * t.1) t.2
    (Real.sqrt ((N : ℝ) / ((t.1 : ℝ) * t.2)))
  simpa only [sieveCount, mul_assoc, mul_comm, mul_left_comm] using h

theorem variableS3Triples_le_source_majorant (N : ℕ) (z w : ℝ) :
    variableS3Triples N z w ≤ s3SourceMajorantTriples N z w := by
  apply sum_le_sum
  intro t _
  apply sum_le_sum
  intro c _
  change sieveCount _ _ _ _ ≤ sourceSieveCount _ _ _ _
  unfold sourceSieveCount
  rw [sourceSieveCarrier_of_dvd_modulus N (dvd_mul_right (t.1 * t.2 * c) N)]
  have h := s3_sieveCount_le_mul_modulus N (t.1 * t.2 * c) (N * t.1) (t.2 * c) c
  simpa only [sieveCount, mul_assoc, mul_comm, mul_left_comm] using h

/-- Both terms, including every triple, have the genuine unscaled
`P(d*N)` carrier. The only paid error here is the old repeated-pair error. -/
theorem lowerS3_le_source_majorants {N : ℕ} (hN : 4 ≤ N) (he : Even N)
    {κ w : ℝ} (hκ : 0 < κ) (hz : 2 ≤ (N : ℝ) ^ κ)
    (hzw : (N : ℝ) ^ κ ≤ w) :
    (lowerS3 N ((N : ℝ) ^ κ) w : ℝ) ≤
      (s3SourceMajorantMain N ((N : ℝ) ^ κ) w : ℝ) +
        (s3SourceMajorantTriples N ((N : ℝ) ^ κ) w : ℝ) +
        2 * (1 / κ) ^ 2 * (N : ℝ) ^ (1 - κ) := by
  have h := lowerS3_le_variable_add_paid_error hN he hκ hz hzw
  have hm : (variableS3Main N ((N : ℝ) ^ κ) w : ℝ) ≤
      (s3SourceMajorantMain N ((N : ℝ) ^ κ) w : ℝ) := by
    exact_mod_cast variableS3Main_le_source_majorant N ((N : ℝ) ^ κ) w
  have ht : (variableS3Triples N ((N : ℝ) ^ κ) w : ℝ) ≤
      (s3SourceMajorantTriples N ((N : ℝ) ^ κ) w : ℝ) := by
    exact_mod_cast variableS3Triples_le_source_majorant N ((N : ℝ) ^ κ) w
  linarith

/-- The actual third-range square-root bound in Wu08 Lemma 2.2.
The non-strict conclusion already follows at the closed parameter edge. -/
theorem s3_third_cutoff_le_cuberoot {N a b : ℕ} {κ₁ κ₂ : ℝ}
    (hN : 1 ≤ N) (hparam : 3 * κ₁ - κ₂ ≤ 1 / 6)
    (ha : (N : ℝ) ^ κ₂ ≤ a)
    (hb : (N : ℝ) ^ (1 / 2 - 3 * κ₁) ≤ b) :
    Real.sqrt ((N : ℝ) / ((a : ℝ) * b)) ≤ (N : ℝ) ^ (1 / 3 : ℝ) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hprod : (N : ℝ) ^ (κ₂ + (1 / 2 - 3 * κ₁)) ≤ (a : ℝ) * b := by
    rw [Real.rpow_add hN0]
    exact mul_le_mul ha hb (Real.rpow_nonneg hN0.le _) (by positivity)
  have hp : 0 < (N : ℝ) ^ (κ₂ + (1 / 2 - 3 * κ₁)) := Real.rpow_pos_of_pos hN0 _
  have hdiv : (N : ℝ) / ((a : ℝ) * b) ≤
      (N : ℝ) ^ (1 - (κ₂ + (1 / 2 - 3 * κ₁))) := by
    rw [Real.rpow_sub hN0, Real.rpow_one]
    exact div_le_div_of_nonneg_left hN0.le hp hprod
  calc
    _ ≤ Real.sqrt ((N : ℝ) ^ (1 - (κ₂ + (1 / 2 - 3 * κ₁)))) :=
      Real.sqrt_le_sqrt hdiv
    _ = (N : ℝ) ^ ((1 - (κ₂ + (1 / 2 - 3 * κ₁))) * (1 / 2)) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hN0.le]
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)

/-- This is the actual nested S3 triple range, with no enlarged upper box. -/
noncomputable def s3ThirdRange (N : ℕ) (z w : ℝ) : Finset (ℕ × ℕ × ℕ) :=
  ((lowerPairs N N z w).filter (fun t => (t.1 : ℝ) < w)).biUnion
    (fun t => ((primeWindow N (t.2 : ℝ)
      (Real.sqrt ((N : ℝ) / ((t.1 : ℝ) * t.2)))).filter
        (fun c => t.2 < c)).image (fun c => (t.1, t.2, c)))

theorem mem_s3ThirdRange {N a b c : ℕ} {z w : ℝ} :
    (a, b, c) ∈ s3ThirdRange N z w ↔
      (a, b) ∈ lowerPairs N N z w ∧ (a : ℝ) < w ∧
        c ∈ primeWindow N (b : ℝ) (Real.sqrt ((N : ℝ) / ((a : ℝ) * b))) ∧ b < c := by
  simp only [s3ThirdRange, mem_biUnion, mem_image, mem_filter, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨x, y⟩, ⟨ht, hx⟩, r, ⟨hr, hyr⟩, hxa, hyb, hrc⟩
    dsimp at hxa hyb
    subst x; subst y; subst r
    exact ⟨ht, hx, hr, hyr⟩
  · rintro ⟨ht, ha, hc, hbc⟩
    exact ⟨(a, b), ⟨ht, ha⟩, c, ⟨hc, hbc⟩, rfl, rfl, rfl⟩

theorem s3ThirdRange_subset_source_triples {N : ℕ} {κ₁ κ₂ : ℝ}
    (hN : 1 ≤ N) (hκ : κ₁ ≤ κ₂) (hparam : 3 * κ₁ - κ₂ ≤ 1 / 6) :
    s3ThirdRange N ((N : ℝ) ^ κ₂) ((N : ℝ) ^ (1 / 2 - 3 * κ₁)) ⊆
      orderedTriples (primeWindow N ((N : ℝ) ^ κ₁) ((N : ℝ) ^ (1 / 3 : ℝ))) := by
  rintro ⟨a, b, c⟩ ht
  obtain ⟨ht, _, hc, hbc⟩ := mem_s3ThirdRange.mp ht
  obtain ⟨hap, hbp, hcop, ha, hb, hab, _⟩ := mem_lowerPairs_source.mp ht
  obtain ⟨hcp, hcN, _, hcT⟩ := mem_primeWindow.mp hc
  obtain ⟨haN, hbN⟩ := Nat.coprime_mul_iff_left.mp hcop
  have hcU := hcT.trans_le (s3_third_cutoff_le_cuberoot hN hparam ha hb)
  have haz : (N : ℝ) ^ κ₁ ≤ a :=
    (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) hκ).trans ha
  have hab' : (a : ℝ) < b := by exact_mod_cast hab
  have hbc' : (b : ℝ) < c := by exact_mod_cast hbc
  exact mem_filter.mpr ⟨mem_product.mpr
    ⟨mem_primeWindow.mpr ⟨hap, haN, haz, hab'.trans (hbc'.trans hcU)⟩,
      mem_product.mpr
        ⟨mem_primeWindow.mpr ⟨hbp, hbN, haz.trans hab'.le, hbc'.trans hcU⟩,
          mem_primeWindow.mpr ⟨hcp, hcN, (haz.trans hab'.le).trans hbc'.le, hcU⟩⟩⟩,
    hab, hbc⟩

theorem sum_s3ThirdRange (N : ℕ) (z w : ℝ) (f : ℕ × ℕ × ℕ → ℤ) :
    ∑ t ∈ s3ThirdRange N z w, f t =
      ∑ t ∈ (lowerPairs N N z w).filter (fun t => (t.1 : ℝ) < w),
        ∑ c ∈ (primeWindow N (t.2 : ℝ)
          (Real.sqrt ((N : ℝ) / ((t.1 : ℝ) * t.2)))).filter (fun c => t.2 < c),
          f (t.1, t.2, c) := by
  unfold s3ThirdRange
  rw [sum_biUnion]
  · apply sum_congr rfl
    intro t _
    apply sum_image
    intro c _ d _ h
    exact congrArg (fun x : ℕ × ℕ × ℕ => x.2.2) h
  · intro t _ r _ htr
    apply disjoint_left.mpr
    intro x hx hy
    obtain ⟨c, _, hc⟩ := mem_image.mp hx
    obtain ⟨d, _, hd⟩ := mem_image.mp hy
    have he := hc.trans hd.symm
    exact htr (Prod.ext (congrArg (fun x : ℕ × ℕ × ℕ => x.1) he)
      (congrArg (fun x : ℕ × ℕ × ℕ => x.2.1) he))

theorem variableS3Triples_eq_third_range_sum (N : ℕ) (z w : ℝ) :
    variableS3Triples N z w =
      ∑ t ∈ s3ThirdRange N z w,
        sieveCount N (t.1 * t.2.1 * t.2.2) (N * t.1) (t.2.2 : ℝ) := by
  rw [sum_s3ThirdRange]
  rfl

theorem mem_s3_ordered_triples {N a b c : ℕ} {z w : ℝ} :
    (a, b, c) ∈ orderedTriples (primeWindow N z w) ↔
      a.Prime ∧ a.Coprime N ∧ z ≤ (a : ℝ) ∧
      b.Prime ∧ b.Coprime N ∧
      c.Prime ∧ c.Coprime N ∧ (c : ℝ) < w ∧ a < b ∧ b < c := by
  simp only [orderedTriples, mem_filter, mem_product, mem_primeWindow]
  constructor
  · tauto
  · rintro ⟨ha, haN, hza, hb, hbN, hc, hcN, hcw, hab, hbc⟩
    have hab' : (a : ℝ) < b := by exact_mod_cast hab
    have hbc' : (b : ℝ) < c := by exact_mod_cast hbc
    exact ⟨⟨⟨ha, haN, hza, hab'.trans (hbc'.trans hcw)⟩,
      ⟨hb, hbN, hza.trans hab'.le, hbc'.trans hcw⟩,
      hc, hcN, (hza.trans hab'.le).trans hbc'.le, hcw⟩, hab, hbc⟩

theorem s3_ordered_triples_mono (N : ℕ) (z : ℝ) {w v : ℝ} (hwv : w ≤ v) :
    orderedTriples (primeWindow N z w) ⊆ orderedTriples (primeWindow N z v) := by
  rintro ⟨a, b, c⟩ ht
  obtain ⟨ha, haN, hza, hb, hbN, hc, hcN, hcw, hab, hbc⟩ :=
    mem_s3_ordered_triples.mp ht
  exact mem_s3_ordered_triples.mpr
    ⟨ha, haN, hza, hb, hbN, hc, hcN, hcw.trans_le hwv, hab, hbc⟩

noncomputable def s3SecondRange (N : ℕ) (z w u : ℝ) : Finset (ℕ × ℕ × ℕ) :=
  (orderedTriples (primeWindow N z u)).filter
    (fun t => (t.2.1 : ℝ) < w ∧ w ≤ (t.2.2 : ℝ))

theorem s3_delta_ranges_disjoint (N : ℕ) (z w u : ℝ) :
    Disjoint (orderedTriples (primeWindow N z w)) (s3SecondRange N z w u) ∧
      Disjoint (orderedTriples (primeWindow N z w)) (s3ThirdRange N w u) ∧
      Disjoint (s3SecondRange N z w u) (s3ThirdRange N w u) := by
  refine ⟨disjoint_left.mpr ?_, disjoint_left.mpr ?_, disjoint_left.mpr ?_⟩
  · rintro ⟨a, b, c⟩ ha hb
    have hc := (mem_s3_ordered_triples.mp ha).2.2.2.2.2.2.2.1
    have hc' := (mem_filter.mp hb).2.2
    exact (not_lt_of_ge hc') hc
  · rintro ⟨a, b, c⟩ ha hc
    obtain ⟨_, _, _, _, _, _, _, hcw, hab, hbc⟩ := mem_s3_ordered_triples.mp ha
    have haz := (mem_lowerPairs_source.mp (mem_s3ThirdRange.mp hc).1).2.2.2.1
    have hac : (a : ℝ) < c := by exact_mod_cast hab.trans hbc
    linarith
  · rintro ⟨a, b, c⟩ hb hc
    obtain ⟨hb, hbw, _⟩ := mem_filter.mp hb
    have hab := (mem_s3_ordered_triples.mp hb).2.2.2.2.2.2.2.2.1
    have haz := (mem_lowerPairs_source.mp (mem_s3ThirdRange.mp hc).1).2.2.2.1
    have hab' : (a : ℝ) < b := by exact_mod_cast hab
    linarith

/-- The exact four-factor remainder, including `q = a`. The distinct
four-prime part and the repeated first-prime part are separated below. -/
noncomputable def s3FourPrimeRemainder (N : ℕ) (t : ℕ × ℕ × ℕ) : ℤ :=
  ∑ q ∈ primeWindow N (t.1 : ℝ) (t.2.1 : ℝ),
    sieveCount N (t.1 * t.2.1 * t.2.2 * q) N (q : ℝ)

theorem s3_triple_cutoff_difference (N a b c : ℕ) (hab : a ≤ b) :
    sieveCount N (a * b * c) N (a : ℝ) -
      sieveCount N (a * b * c) N (b : ℝ) =
        s3FourPrimeRemainder N (a, b, c) := by
  have h := goldbach_buchstab N (a * b * c) N (by exact_mod_cast hab : (a : ℝ) ≤ b)
  change _ = _ - s3FourPrimeRemainder N (a, b, c) at h
  omega

noncomputable def s3Delta2Quotient (N : ℕ) (z w u v : ℝ) : ℤ :=
  (∑ t ∈ orderedTriples (primeWindow N z v),
    sieveCount N (t.1 * t.2.1 * t.2.2) (N * t.1) (t.2.1 : ℝ)) -
  (∑ t ∈ orderedTriples (primeWindow N z w),
    sieveCount N (t.1 * t.2.1 * t.2.2) N (t.1 : ℝ)) -
  (∑ t ∈ s3SecondRange N z w u,
    sieveCount N (t.1 * t.2.1 * t.2.2) N (t.1 : ℝ)) -
  variableS3Triples N w u

private theorem delta2_finite_core (N : ℕ) (z w u v : ℝ)
    (hwv : w ≤ v) (huv : u ≤ v)
    (hthird : s3ThirdRange N w u ⊆ orderedTriples (primeWindow N z v)) :
    -(∑ t ∈ orderedTriples (primeWindow N z w), s3FourPrimeRemainder N t) -
      (∑ t ∈ s3SecondRange N z w u, s3FourPrimeRemainder N t) ≤
        s3Delta2Quotient N z w u v := by
  let A := orderedTriples (primeWindow N z w)
  let B := s3SecondRange N z w u
  let C := s3ThirdRange N w u
  let F := fun t : ℕ × ℕ × ℕ =>
    sieveCount N (t.1 * t.2.1 * t.2.2) (N * t.1) (t.2.1 : ℝ)
  obtain ⟨hAB, hAC, hBC⟩ := s3_delta_ranges_disjoint N z w u
  have hsub : A ∪ B ∪ C ⊆ orderedTriples (primeWindow N z v) := by
    apply union_subset
    · apply union_subset
      · exact s3_ordered_triples_mono N z hwv
      · exact (filter_subset _ _).trans (s3_ordered_triples_mono N z huv)
    · exact hthird
  have hsum := sum_le_sum_of_subset_of_nonneg (f := F) hsub
    (fun t _ _ => sieveCount_nonneg _ _ _ _)
  rw [sum_union (disjoint_union_left.mpr ⟨hAC, hBC⟩), sum_union hAB] at hsum
  have hfirst : ∀ t ∈ A, sieveCount N (t.1 * t.2.1 * t.2.2) N (t.1 : ℝ) ≤
      F t + s3FourPrimeRemainder N t := by
    intro t ht
    rcases t with ⟨a, b, c⟩
    have hab := (mem_filter.mp ht).2.1.le
    have he := s3_triple_cutoff_difference N a b c hab
    have hm := s3_sieveCount_le_mul_modulus N (a * b * c) N a (b : ℝ)
    change _ ≤ F (a, b, c) at hm
    change sieveCount N (a * b * c) N (a : ℝ) ≤
      F (a, b, c) + s3FourPrimeRemainder N (a, b, c)
    omega
  have hsecond : ∀ t ∈ B, sieveCount N (t.1 * t.2.1 * t.2.2) N (t.1 : ℝ) ≤
      F t + s3FourPrimeRemainder N t := by
    intro t ht
    rcases t with ⟨a, b, c⟩
    have hab := (mem_filter.mp (mem_filter.mp ht).1).2.1.le
    have he := s3_triple_cutoff_difference N a b c hab
    have hm := s3_sieveCount_le_mul_modulus N (a * b * c) N a (b : ℝ)
    change _ ≤ F (a, b, c) at hm
    change sieveCount N (a * b * c) N (a : ℝ) ≤
      F (a, b, c) + s3FourPrimeRemainder N (a, b, c)
    omega
  have hthirdSum : variableS3Triples N w u ≤ ∑ t ∈ C, F t := by
    rw [variableS3Triples_eq_third_range_sum]
    apply sum_le_sum
    intro t ht
    have hbc := (mem_s3ThirdRange.mp ht).2.2.2.le
    exact sieveCount_antitone N _ _ (by exact_mod_cast hbc)
  have hA := sum_le_sum hfirst
  have hB := sum_le_sum hsecond
  rw [sum_add_distrib] at hA hB
  unfold s3Delta2Quotient
  change -(∑ t ∈ A, _) - (∑ t ∈ B, _) ≤ _
  dsimp only [A, B, C, F] at hsum hA hB hthirdSum
  dsimp only [A, B]
  omega

/-- Actual source parameter ranges, exact multiplicity, and correct
quotient signs. This is a finite Delta2 bound, not yet the printed
`-Upsilon10-Upsilon11+O(...)` bound. -/
theorem s3_delta2_ge_fourprime_remainders {N : ℕ} {κ₁ κ₂ : ℝ}
    (hN : 1 ≤ N) (hκ₁ : 1 / 18 ≤ κ₁) (hκ : κ₁ ≤ κ₂)
    (hupper : 3 * κ₁ + κ₂ ≤ 1 / 2) (hparam : 3 * κ₁ - κ₂ ≤ 1 / 6) :
    -(∑ t ∈ orderedTriples (primeWindow N ((N : ℝ) ^ κ₁) ((N : ℝ) ^ κ₂)),
        s3FourPrimeRemainder N t) -
      (∑ t ∈ s3SecondRange N ((N : ℝ) ^ κ₁) ((N : ℝ) ^ κ₂)
        ((N : ℝ) ^ (1 / 2 - 3 * κ₁)), s3FourPrimeRemainder N t) ≤
      s3Delta2Quotient N ((N : ℝ) ^ κ₁) ((N : ℝ) ^ κ₂)
        ((N : ℝ) ^ (1 / 2 - 3 * κ₁)) ((N : ℝ) ^ (1 / 3 : ℝ)) := by
  apply delta2_finite_core
  · apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN)
    linarith
  · apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN)
    linarith
  · exact s3ThirdRange_subset_source_triples hN hκ hparam

theorem s3_fourprime_remainder_split (N a b c : ℕ)
    (ha : a.Prime) (haN : a.Coprime N) (hab : a < b) :
    s3FourPrimeRemainder N (a, b, c) =
      (∑ q ∈ (primeWindow N (a : ℝ) (b : ℝ)).filter (fun q => a < q),
        sieveCount N (a * q * b * c) N (q : ℝ)) +
      sieveCount N (a * b * c * a) N (a : ℝ) := by
  have he : primeWindow N (a : ℝ) (b : ℝ) =
      insert a ((primeWindow N (a : ℝ) (b : ℝ)).filter (fun q => a < q)) := by
    ext q
    constructor
    · intro hq
      have haq : a ≤ q := by exact_mod_cast (mem_primeWindow.mp hq).2.2.1
      by_cases heq : q = a
      · exact mem_insert.mpr (Or.inl heq)
      · exact mem_insert.mpr (Or.inr (mem_filter.mpr ⟨hq, by omega⟩))
    · intro hq
      rcases mem_insert.mp hq with rfl | hq
      · exact mem_primeWindow.mpr ⟨ha, haN, le_rfl, by exact_mod_cast hab⟩
      · exact (mem_filter.mp hq).1
  unfold s3FourPrimeRemainder
  dsimp only
  conv_lhs => rw [he, sum_insert (by simp)]
  rw [add_comm]
  congr 1
  apply sum_congr rfl
  intro q _
  congr 1
  ring

/-- The image records the new prime in its sorted second position. It
does not forget tuple multiplicity by passing to a product support. -/
noncomputable def s3DistinctQuadruples (N : ℕ) (T : Finset (ℕ × ℕ × ℕ)) :
    Finset (ℕ × ℕ × ℕ × ℕ) :=
  T.biUnion (fun t =>
    ((primeWindow N (t.1 : ℝ) (t.2.1 : ℝ)).filter (fun q => t.1 < q)).image
      (fun q => (t.1, q, t.2.1, t.2.2)))

theorem mem_s3DistinctQuadruples {N a q b c : ℕ} {T : Finset (ℕ × ℕ × ℕ)} :
    (a, q, b, c) ∈ s3DistinctQuadruples N T ↔
      (a, b, c) ∈ T ∧ q.Prime ∧ q.Coprime N ∧ a < q ∧ q < b := by
  simp only [s3DistinctQuadruples, mem_biUnion, mem_image, mem_filter,
    mem_primeWindow, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨x, y, z⟩, ht, r, ⟨⟨hr, hrN, _, hry⟩, hxr⟩, hxa, hrq, hyb, hzc⟩
    dsimp at hxa hyb hzc hxr hry
    subst x; subst y; subst z; subst r
    exact ⟨ht, hr, hrN, hxr, by exact_mod_cast hry⟩
  · rintro ⟨ht, hq, hqN, haq, hqb⟩
    exact ⟨(a, b, c), ht, q,
      ⟨⟨hq, hqN, by exact_mod_cast haq.le, by exact_mod_cast hqb⟩, haq⟩,
      rfl, rfl, rfl, rfl⟩

theorem sum_s3DistinctQuadruples (N : ℕ) (T : Finset (ℕ × ℕ × ℕ))
    (f : ℕ × ℕ × ℕ × ℕ → ℤ) :
    ∑ t ∈ s3DistinctQuadruples N T, f t =
      ∑ t ∈ T, ∑ q ∈ (primeWindow N (t.1 : ℝ) (t.2.1 : ℝ)).filter
        (fun q => t.1 < q), f (t.1, q, t.2.1, t.2.2) := by
  unfold s3DistinctQuadruples
  rw [sum_biUnion]
  · apply sum_congr rfl
    intro t _
    apply sum_image
    intro q _ r _ h
    exact congrArg (fun x : ℕ × ℕ × ℕ × ℕ => x.2.1) h
  · intro t _ r _ htr
    apply disjoint_left.mpr
    intro x hx hy
    obtain ⟨q, _, hq⟩ := mem_image.mp hx
    obtain ⟨p, _, hp⟩ := mem_image.mp hy
    have he := hq.trans hp.symm
    apply htr
    exact Prod.ext (congrArg (fun x : ℕ × ℕ × ℕ × ℕ => x.1) he)
      (Prod.ext (congrArg (fun x : ℕ × ℕ × ℕ × ℕ => x.2.2.1) he)
        (congrArg (fun x : ℕ × ℕ × ℕ × ℕ => x.2.2.2) he))

theorem s3_fourprime_sum_split (N : ℕ) (T : Finset (ℕ × ℕ × ℕ))
    (hT : ∀ t ∈ T, t.1.Prime ∧ t.1.Coprime N ∧ t.1 < t.2.1) :
    ∑ t ∈ T, s3FourPrimeRemainder N t =
      (∑ t ∈ s3DistinctQuadruples N T,
        sieveCount N (t.1 * t.2.1 * t.2.2.1 * t.2.2.2) N (t.2.1 : ℝ)) +
      ∑ t ∈ T, sieveCount N (t.1 * t.2.1 * t.2.2 * t.1) N (t.1 : ℝ) := by
  rw [sum_s3DistinctQuadruples, ← sum_add_distrib]
  apply sum_congr rfl
  rintro ⟨a, b, c⟩ ht
  obtain ⟨ha, haN, hab⟩ := hT _ ht
  exact s3_fourprime_remainder_split N a b c ha haN hab

/-- The first distinct four-prime range is exactly the increasing
`z ≤ a < b < c < d < w` range of Upsilon10, not a factorial multiple. -/
theorem mem_s3_first_quadruples {N a b c d : ℕ} {z w : ℝ} :
    (a, b, c, d) ∈ s3DistinctQuadruples N (orderedTriples (primeWindow N z w)) ↔
      a.Prime ∧ a.Coprime N ∧ z ≤ (a : ℝ) ∧
      b.Prime ∧ b.Coprime N ∧ c.Prime ∧ c.Coprime N ∧
      d.Prime ∧ d.Coprime N ∧ (d : ℝ) < w ∧ a < b ∧ b < c ∧ c < d := by
  rw [mem_s3DistinctQuadruples, mem_s3_ordered_triples]
  constructor
  · tauto
  · rintro ⟨ha, haN, hz, hb, hbN, hc, hcN, hd, hdN, hw, hab, hbc, hcd⟩
    exact ⟨⟨ha, haN, hz, hc, hcN, hd, hdN, hw, hab.trans hbc, hcd⟩,
      hb, hbN, hab, hbc⟩

/-- The second distinct range still has `d < u`. Transport to the
different moving Upsilon11 bound is a separate, unproved step. -/
theorem mem_s3_second_quadruples {N a b c d : ℕ} {z w u : ℝ} :
    (a, b, c, d) ∈ s3DistinctQuadruples N (s3SecondRange N z w u) ↔
      a.Prime ∧ a.Coprime N ∧ z ≤ (a : ℝ) ∧
      b.Prime ∧ b.Coprime N ∧ c.Prime ∧ c.Coprime N ∧
      d.Prime ∧ d.Coprime N ∧ (d : ℝ) < u ∧
      a < b ∧ b < c ∧ c < d ∧ (c : ℝ) < w ∧ w ≤ (d : ℝ) := by
  rw [mem_s3DistinctQuadruples]
  simp only [s3SecondRange, mem_filter, mem_s3_ordered_triples]
  constructor
  · tauto
  · rintro ⟨ha, haN, hz, hb, hbN, hc, hcN, hd, hdN, hu, hab, hbc, hcd, hcw, hwd⟩
    exact ⟨⟨⟨ha, haN, hz, hc, hcN, hd, hdN, hu, hab.trans hbc, hcd⟩, hcw, hwd⟩,
      hb, hbN, hab, hbc⟩

theorem s3_distinct_fourprime_le_source_majorant (N : ℕ) (T : Finset (ℕ × ℕ × ℕ)) :
    (∑ t ∈ s3DistinctQuadruples N T,
      sieveCount N (t.1 * t.2.1 * t.2.2.1 * t.2.2.2) N (t.2.1 : ℝ)) ≤
    ∑ t ∈ s3DistinctQuadruples N T,
      sourceSieveCount N (t.1 * t.2.1 * t.2.2.1 * t.2.2.2)
        ((t.1 * t.2.1 * t.2.2.1 * t.2.2.2) * N) (t.2.1 : ℝ) := by
  apply sum_le_sum
  intro t _
  exact sieveCount_le_source_selected_modulus N _ N _

noncomputable def s3FourSourceMajorant (N : ℕ) (T : Finset (ℕ × ℕ × ℕ)) : ℤ :=
  ∑ t ∈ s3DistinctQuadruples N T,
    sourceSieveCount N (t.1 * t.2.1 * t.2.2.1 * t.2.2.2)
      ((t.1 * t.2.1 * t.2.2.1 * t.2.2.2) * N) (t.2.1 : ℝ)

noncomputable def s3RepeatedFirstPrimeMass (N : ℕ) (T : Finset (ℕ × ℕ × ℕ)) : ℤ :=
  ∑ t ∈ T, sieveCount N (t.1 * t.2.1 * t.2.2 * t.1) N (t.1 : ℝ)

theorem s3_fourprime_sum_le_source_add_repeated (N : ℕ) (T : Finset (ℕ × ℕ × ℕ))
    (hT : ∀ t ∈ T, t.1.Prime ∧ t.1.Coprime N ∧ t.1 < t.2.1) :
    ∑ t ∈ T, s3FourPrimeRemainder N t ≤
      s3FourSourceMajorant N T + s3RepeatedFirstPrimeMass N T := by
  rw [s3_fourprime_sum_split N T hT]
  exact add_le_add (s3_distinct_fourprime_le_source_majorant N T) le_rfl

/-- Source-faithful finite Delta2 endpoint: all distinct four-prime
terms use the unscaled `P(d*N)` carriers; all repeated first-prime terms
are still explicit. No negligibility is claimed for either correction. -/
theorem s3_delta2_ge_source_fourprime_add_repeated {N : ℕ} {κ₁ κ₂ : ℝ}
    (hN : 1 ≤ N) (hκ₁ : 1 / 18 ≤ κ₁) (hκ : κ₁ ≤ κ₂)
    (hupper : 3 * κ₁ + κ₂ ≤ 1 / 2) (hparam : 3 * κ₁ - κ₂ ≤ 1 / 6) :
    -(s3FourSourceMajorant N
        (orderedTriples (primeWindow N ((N : ℝ) ^ κ₁) ((N : ℝ) ^ κ₂))) +
      s3RepeatedFirstPrimeMass N
        (orderedTriples (primeWindow N ((N : ℝ) ^ κ₁) ((N : ℝ) ^ κ₂)))) -
    (s3FourSourceMajorant N
        (s3SecondRange N ((N : ℝ) ^ κ₁) ((N : ℝ) ^ κ₂) ((N : ℝ) ^ (1 / 2 - 3 * κ₁))) +
      s3RepeatedFirstPrimeMass N
        (s3SecondRange N ((N : ℝ) ^ κ₁) ((N : ℝ) ^ κ₂) ((N : ℝ) ^ (1 / 2 - 3 * κ₁)))) ≤
    s3Delta2Quotient N ((N : ℝ) ^ κ₁) ((N : ℝ) ^ κ₂)
      ((N : ℝ) ^ (1 / 2 - 3 * κ₁)) ((N : ℝ) ^ (1 / 3 : ℝ)) := by
  have h := s3_delta2_ge_fourprime_remainders hN hκ₁ hκ hupper hparam
  have hfirst := s3_fourprime_sum_le_source_add_repeated N
    (orderedTriples (primeWindow N ((N : ℝ) ^ κ₁) ((N : ℝ) ^ κ₂))) (by
      rintro ⟨a, b, c⟩ ht
      obtain ⟨ha, haN, _, _, _, _, _, _, hab, _⟩ := mem_s3_ordered_triples.mp ht
      exact ⟨ha, haN, hab⟩)
  have hsecond := s3_fourprime_sum_le_source_add_repeated N
    (s3SecondRange N ((N : ℝ) ^ κ₁) ((N : ℝ) ^ κ₂) ((N : ℝ) ^ (1 / 2 - 3 * κ₁))) (by
      rintro ⟨a, b, c⟩ ht
      obtain ⟨ha, haN, _, _, _, _, _, _, hab, _⟩ :=
        mem_s3_ordered_triples.mp (mem_filter.mp ht).1
      exact ⟨ha, haN, hab⟩)
  omega

end Wu2008DoubleSieve
