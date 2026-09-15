import MathlibNt.Wu2008DoubleSieve.VariableS3

/-!
# Unscaled divisible subsequences versus quotient sequences

Wu04, pp. 219--220, defines `A_d` as the unscaled divisible subsequence.
Wu08, p. 369, prints closed sifting. Removing a selected prime from the
integer being sifted is not harmless at or above that prime.

The identities below retain the entire discrepancy, including squarefree
complements. They also give an unconditional carrier bridge for the actual
double-sieve modulus `P(d*N)` at every real cutoff.
-/

namespace Wu2008DoubleSieve

open Finset
open scoped Classical

noncomputable def sourceSieveCarrier (N d M : ℕ) (z : ℝ) : Finset ℕ :=
  (range (N + 1)).filter (fun p => p.Prime ∧ d ∣ N - p ∧ Sifted M (N - p) z)

noncomputable def sourceSieveCarrierLE (N d M : ℕ) (z : ℝ) : Finset ℕ :=
  (range (N + 1)).filter (fun p => p.Prime ∧ d ∣ N - p ∧ SiftedLE M (N - p) z)

noncomputable def sourceSieveCount (N d M : ℕ) (z : ℝ) : ℤ :=
  (sourceSieveCarrier N d M z).card

noncomputable def sourceSieveCountLE (N d M : ℕ) (z : ℝ) : ℤ :=
  (sourceSieveCarrierLE N d M z).card

theorem sifted_mul_iff (M a b : ℕ) (z : ℝ) :
    Sifted M (a * b) z ↔ Sifted M a z ∧ Sifted M b z := by
  constructor
  · intro h
    exact ⟨fun q hq hM hz hd => h q hq hM hz (dvd_mul_of_dvd_left hd b),
      fun q hq hM hz hd => h q hq hM hz (dvd_mul_of_dvd_right hd a)⟩
  · rintro ⟨ha, hb⟩ q hq hM hz hd
    exact (hq.dvd_mul.mp hd).elim (ha q hq hM hz) (hb q hq hM hz)

theorem siftedLE_mul_iff (M a b : ℕ) (z : ℝ) :
    SiftedLE M (a * b) z ↔ SiftedLE M a z ∧ SiftedLE M b z := by
  constructor
  · intro h
    exact ⟨fun q hq hM hz hd => h q hq hM hz (dvd_mul_of_dvd_left hd b),
      fun q hq hM hz hd => h q hq hM hz (dvd_mul_of_dvd_right hd a)⟩
  · rintro ⟨ha, hb⟩ q hq hM hz hd
    exact (hq.dvd_mul.mp hd).elim (ha q hq hM hz) (hb q hq hM hz)

theorem sourceSieveCarrier_eq_ite (N d M : ℕ) (z : ℝ) :
    sourceSieveCarrier N d M z =
      if Sifted M d z then sieveCarrier N d M z else ∅ := by
  have hs (n : ℕ) (hd : d ∣ n) :
      Sifted M n z ↔ Sifted M d z ∧ Sifted M (n / d) z := by
    conv_lhs => rw [← Nat.mul_div_cancel' hd]
    exact sifted_mul_iff M d (n / d) z
  by_cases h : Sifted M d z
  · simp only [if_pos h]
    ext p
    simp only [sourceSieveCarrier, sieveCarrier, mem_filter]
    constructor
    · rintro ⟨hp, hprime, hd, hz⟩
      exact ⟨hp, hprime, hd, ((hs _ hd).mp hz).2⟩
    · rintro ⟨hp, hprime, hd, hz⟩
      exact ⟨hp, hprime, hd, (hs _ hd).mpr ⟨h, hz⟩⟩
  · simp only [if_neg h]
    apply eq_empty_iff_forall_notMem.mpr
    intro p hp
    obtain ⟨_, _, hd, hz⟩ := mem_filter.mp hp
    exact h ((hs _ hd).mp hz).1

theorem sourceSieveCarrierLE_eq_ite (N d M : ℕ) (z : ℝ) :
    sourceSieveCarrierLE N d M z =
      if SiftedLE M d z then sieveCarrierLE N d M z else ∅ := by
  have hs (n : ℕ) (hd : d ∣ n) :
      SiftedLE M n z ↔ SiftedLE M d z ∧ SiftedLE M (n / d) z := by
    conv_lhs => rw [← Nat.mul_div_cancel' hd]
    exact siftedLE_mul_iff M d (n / d) z
  by_cases h : SiftedLE M d z
  · simp only [if_pos h]
    ext p
    simp only [sourceSieveCarrierLE, sieveCarrierLE, mem_filter]
    constructor
    · rintro ⟨hp, hprime, hd, hz⟩
      exact ⟨hp, hprime, hd, ((hs _ hd).mp hz).2⟩
    · rintro ⟨hp, hprime, hd, hz⟩
      exact ⟨hp, hprime, hd, (hs _ hd).mpr ⟨h, hz⟩⟩
  · simp only [if_neg h]
    apply eq_empty_iff_forall_notMem.mpr
    intro p hp
    obtain ⟨_, _, hd, hz⟩ := mem_filter.mp hp
    exact h ((hs _ hd).mp hz).1

theorem siftedLE_of_dvd_modulus {d M : ℕ} (hdM : d ∣ M) (z : ℝ) :
    SiftedLE M d z := by
  intro q hq hcop _ hqd
  have hqM := hqd.trans hdM
  have hq1 : q ∣ 1 := by
    simpa only [hcop.gcd_eq_one] using Nat.dvd_gcd (dvd_refl q) hqM
  exact hq.not_dvd_one hq1

theorem sourceSieveCarrier_of_dvd_modulus (N : ℕ) {d M : ℕ}
    (hdM : d ∣ M) (z : ℝ) :
    sourceSieveCarrier N d M z = sieveCarrier N d M z := by
  rw [sourceSieveCarrier_eq_ite, if_pos]
  exact fun q hq hc hz => siftedLE_of_dvd_modulus hdM z q hq hc hz.le

theorem sourceSieveCarrierLE_of_dvd_modulus (N : ℕ) {d M : ℕ}
    (hdM : d ∣ M) (z : ℝ) :
    sourceSieveCarrierLE N d M z = sieveCarrierLE N d M z := by
  rw [sourceSieveCarrierLE_eq_ite, if_pos (siftedLE_of_dvd_modulus hdM z)]

/-- The actual `Phi` modulus removes every selected factor, at all cutoffs. -/
theorem source_double_sieve_carriers (N d : ℕ) (z : ℝ) :
    sourceSieveCarrier N d (d * N) z = sieveCarrier N d (d * N) z ∧
      sourceSieveCarrierLE N d (d * N) z = sieveCarrierLE N d (d * N) z :=
  ⟨sourceSieveCarrier_of_dvd_modulus N (dvd_mul_right d N) z,
    sourceSieveCarrierLE_of_dvd_modulus N (dvd_mul_right d N) z⟩

theorem sifted_selected_pair_iff {N a b : ℕ} (hb : b.Prime)
    (hbNa : b.Coprime (N * a)) (z : ℝ) :
    Sifted (N * a) (a * b) z ↔ z ≤ (b : ℝ) := by
  rw [sifted_mul_iff]
  have ha : Sifted (N * a) a z :=
    fun q hq hc hz => siftedLE_of_dvd_modulus (dvd_mul_left a N) z q hq hc hz.le
  simp only [ha, true_and]
  constructor
  · intro h
    by_contra hz
    exact h b hb hbNa (lt_of_not_ge hz) (dvd_refl b)
  · intro hz q hq _ hqz hqb
    rcases (Nat.dvd_prime hb).mp hqb with he | he
    · exact hq.ne_one he
    · subst q
      exact (not_lt_of_ge hz) hqz

theorem siftedLE_selected_pair_iff {N a b : ℕ} (hb : b.Prime)
    (hbNa : b.Coprime (N * a)) (z : ℝ) :
    SiftedLE (N * a) (a * b) z ↔ z < (b : ℝ) := by
  rw [siftedLE_mul_iff]
  simp only [siftedLE_of_dvd_modulus (dvd_mul_left a N) z, true_and]
  constructor
  · intro h
    by_contra hz
    exact h b hb hbNa (le_of_not_gt hz) (dvd_refl b)
  · intro hz q hq _ hqz hqb
    rcases (Nat.dvd_prime hb).mp hqb with he | he
    · exact hq.ne_one he
    · subst q
      exact (not_le_of_gt hz) hqz

/-- If a moving cutoff crosses `b`, the entire unscaled pair carrier is
empty, not just its squareful part. -/
theorem source_pair_carrier (N a b : ℕ) (hb : b.Prime)
    (hbNa : b.Coprime (N * a)) (z : ℝ) :
    sourceSieveCarrier N (a * b) (N * a) z =
      if z ≤ (b : ℝ) then sieveCarrier N (a * b) (N * a) z else ∅ := by
  rw [sourceSieveCarrier_eq_ite, sifted_selected_pair_iff hb hbNa]

theorem source_closed_pair_carrier (N a b : ℕ) (hb : b.Prime)
    (hbNa : b.Coprime (N * a)) (z : ℝ) :
    sourceSieveCarrierLE N (a * b) (N * a) z =
      if z < (b : ℝ) then sieveCarrierLE N (a * b) (N * a) z else ∅ := by
  rw [sourceSieveCarrierLE_eq_ite, siftedLE_selected_pair_iff hb hbNa]

theorem source_closed_pair_at_selected_prime (N a b : ℕ) (hb : b.Prime)
    (hbNa : b.Coprime (N * a)) :
    sourceSieveCarrierLE N (a * b) (N * a) (b : ℝ) = ∅ := by
  simp only [source_closed_pair_carrier N a b hb hbNa, lt_self_iff_false, if_false]

/-- Exact correction, with no assertion that the second summand is small. -/
theorem quotient_pair_count_eq_source_add_correction (N a b : ℕ) (hb : b.Prime)
    (hbNa : b.Coprime (N * a)) (z : ℝ) :
    sieveCount N (a * b) (N * a) z =
      sourceSieveCount N (a * b) (N * a) z +
        if (b : ℝ) < z then sieveCount N (a * b) (N * a) z else 0 := by
  unfold sourceSieveCount
  rw [source_pair_carrier N a b hb hbNa]
  by_cases hz : z ≤ (b : ℝ)
  · simp [hz, not_lt_of_ge hz, sieveCount]
  · simp [hz, lt_of_not_ge hz]

theorem sourceSieveCarrier_eq_empty_of_selected {N d M q : ℕ} {z : ℝ}
    (hq : q.Prime) (hqM : q.Coprime M) (hqd : q ∣ d) (hqz : (q : ℝ) < z) :
    sourceSieveCarrier N d M z = ∅ := by
  rw [sourceSieveCarrier_eq_ite, if_neg]
  exact fun hs => hs q hq hqM hqz hqd

theorem sifted_prime_of_le {M q : ℕ} {z : ℝ} (hq : q.Prime) (hz : z ≤ (q : ℝ)) :
    Sifted M q z := by
  intro r hr _ hrz hrd
  rcases (Nat.dvd_prime hq).mp hrd with he | he
  · exact hr.ne_one he
  · subst r
    exact (not_lt_of_ge hz) hrz

theorem source_strict_pair_carrier {N a b : ℕ} (hb : b.Prime) :
    sourceSieveCarrier N (a * b) (N * a) (b : ℝ) =
      sieveCarrier N (a * b) (N * a) (b : ℝ) := by
  rw [sourceSieveCarrier_eq_ite, if_pos]
  exact (sifted_mul_iff _ _ _ _).mpr
    ⟨fun q hq hc hz => siftedLE_of_dvd_modulus (dvd_mul_left a N) _ q hq hc hz.le,
      sifted_prime_of_le hb le_rfl⟩

theorem source_strict_triple_carrier {N a b c : ℕ}
    (hb : b.Prime) (hc : c.Prime) (hbc : b ≤ c) :
    sourceSieveCarrier N (a * b * c) (N * a) (b : ℝ) =
      sieveCarrier N (a * b * c) (N * a) (b : ℝ) := by
  rw [sourceSieveCarrier_eq_ite, if_pos]
  rw [sifted_mul_iff, sifted_mul_iff]
  exact ⟨⟨fun q hq hM hz =>
    siftedLE_of_dvd_modulus (dvd_mul_left a N) _ q hq hM hz.le,
      sifted_prime_of_le hb le_rfl⟩,
    sifted_prime_of_le hc (by exact_mod_cast hbc)⟩

/-- The complete strict/unscaled lower-weight RHS, with the original
divisible subsequences and the same finite prime ranges. -/
noncomputable def sourceLowerWeightRHS (N : ℕ) (z w : ℝ) : ℤ :=
  2 * sourceSieveCount N 1 N z -
    (∑ q ∈ primeWindow N z w, sourceSieveCount N q N z) -
    (∑ t ∈ lowerPairs N N z w,
      (if w ≤ (t.1 : ℝ) then 2 else 1) *
        sourceSieveCount N (t.1 * t.2) (N * t.1) (t.2 : ℝ)) +
    ∑ t ∈ orderedTriples (primeWindow N z w),
      sourceSieveCount N (t.1 * t.2.1 * t.2.2) (N * t.1) (t.2.1 : ℝ)

theorem sourceLowerWeightRHS_eq (N : ℕ) (z w : ℝ) :
    sourceLowerWeightRHS N z w = lowerWeightRHS N z w := by
  have hbase : sourceSieveCount N 1 N z = sieveCount N 1 N z := by
    unfold sourceSieveCount sieveCount
    rw [sourceSieveCarrier_of_dvd_modulus N (one_dvd N)]
  have hsingle :
      (∑ q ∈ primeWindow N z w, sourceSieveCount N q N z) =
        ∑ q ∈ primeWindow N z w, sieveCount N q N z := by
    apply sum_congr rfl
    intro q hq
    obtain ⟨hp, _, hz, _⟩ := mem_primeWindow.mp hq
    simp only [sourceSieveCount, sieveCount, sourceSieveCarrier_eq_ite,
      if_pos (sifted_prime_of_le hp hz)]
  have hpairs :
      (∑ t ∈ lowerPairs N N z w,
        (if w ≤ (t.1 : ℝ) then 2 else 1) *
          sourceSieveCount N (t.1 * t.2) (N * t.1) (t.2 : ℝ)) =
        2 * lowerS2 N z w + lowerS3 N z w := by
    rw [← lower_pair_sum_split]
    apply sum_congr rfl
    intro t ht
    have hb := ((mem_lowerPairs_source.mp ht).2).1
    simp only [sourceSieveCount, sieveCount, source_strict_pair_carrier hb]
  have htriples :
      (∑ t ∈ orderedTriples (primeWindow N z w),
        sourceSieveCount N (t.1 * t.2.1 * t.2.2) (N * t.1) (t.2.1 : ℝ)) =
      ∑ t ∈ orderedTriples (primeWindow N z w),
        sieveCount N (t.1 * t.2.1 * t.2.2) (N * t.1) (t.2.1 : ℝ) := by
    apply sum_congr rfl
    intro t ht
    obtain ⟨hm, _, hbc⟩ := mem_filter.mp ht
    obtain ⟨_, hm⟩ := mem_product.mp hm
    obtain ⟨hb, hc⟩ := mem_product.mp hm
    simp only [sourceSieveCount, sieveCount,
      source_strict_triple_carrier (mem_primeWindow.mp hb).1
        (mem_primeWindow.mp hc).1 hbc.le]
  unfold sourceLowerWeightRHS lowerWeightRHS
  rw [hbase, hsingle, hpairs, htriples]
  ring

/-- A genuine strict/unscaled realization of the source lower weight.
This deliberately does not identify Wu08's printed closed product with it. -/
theorem wu_lemma21_strict_source {κ σ : ℝ}
    (hκ : 0 < κ) (hκσ : κ < σ) (hσ : σ ≤ 1 / 3) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      (sourceLowerWeightRHS N ((N : ℝ) ^ κ) ((N : ℝ) ^ σ) : ℝ) -
        8 * (N : ℝ) ^ (1 - κ) ≤
          2 * ((MathlibNt.Wu2008DoubleSieve.wuPrimeComplements N).card : ℝ) := by
  simpa only [sourceLowerWeightRHS_eq] using wu_lemma21_strict hκ hκσ hσ

noncomputable def sourceVariableS3Main (N : ℕ) (z w : ℝ) : ℤ :=
  ∑ t ∈ (lowerPairs N N z w).filter (fun t => (t.1 : ℝ) < w),
    sourceSieveCount N (t.1 * t.2) (N * t.1)
      (Real.sqrt ((N : ℝ) / ((t.1 : ℝ) * t.2)))

/-- The source-convention defect is an explicit sum of whole quotient
carriers. The previously paid repeated-prime error does not pay this sum. -/
noncomputable def variableS3CrossingCorrection (N : ℕ) (z w : ℝ) : ℤ :=
  ∑ t ∈ (lowerPairs N N z w).filter (fun t => (t.1 : ℝ) < w),
    if (t.2 : ℝ) < Real.sqrt ((N : ℝ) / ((t.1 : ℝ) * t.2)) then
      sieveCount N (t.1 * t.2) (N * t.1)
        (Real.sqrt ((N : ℝ) / ((t.1 : ℝ) * t.2))) else 0

theorem variableS3Main_eq_source_add_correction (N : ℕ) (z w : ℝ) :
    variableS3Main N z w =
      sourceVariableS3Main N z w + variableS3CrossingCorrection N z w := by
  unfold variableS3Main sourceVariableS3Main variableS3CrossingCorrection
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro t ht
  obtain ⟨ha, hb, hcop, _, _, hab, _⟩ :=
    mem_lowerPairs_source.mp (mem_filter.mp ht).1
  apply quotient_pair_count_eq_source_add_correction N t.1 t.2 hb
  exact Nat.coprime_mul_iff_right.mpr
    ⟨(Nat.coprime_mul_iff_left.mp hcop).2,
      (Nat.coprime_primes hb ha).mpr (ne_of_gt hab)⟩

end Wu2008DoubleSieve
