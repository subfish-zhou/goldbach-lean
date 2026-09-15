import MathlibNt.Wu2008DoubleSieve.S3FourPrimeCompletion

/-!
# The joint original four-label domain and its modulus excess

The Upsilon11 moving cutoff is unchanged. At the strict second-label
cutoff, only the first selected prime can distinguish the selected
modulus from P(N); its excess forces a square in the actual complement.
-/

namespace Wu2008DoubleSieve

open Finset
open scoped Classical

noncomputable def fourModulusDomain (N : ℕ) (z w V : ℝ) :
    Finset (ℕ × ℕ × ℕ × ℕ) :=
  s3DistinctQuadruples N (orderedTriples (primeWindow N z w)) ∪
    s3Upsilon11Range N z w V

def fourModulusProduct (t : ℕ × ℕ × ℕ × ℕ) : ℕ :=
  t.1 * t.2.1 * t.2.2.1 * t.2.2.2

noncomputable def fourModulusQuotientTerm (N : ℕ) (t : ℕ × ℕ × ℕ × ℕ) : ℤ :=
  sieveCount N (fourModulusProduct t) N (t.2.1 : ℝ)

noncomputable def fourModulusLoss (N : ℕ) (t : ℕ × ℕ × ℕ × ℕ) : Finset ℕ :=
  sourceSieveCarrier N (fourModulusProduct t) (fourModulusProduct t * N) (t.2.1 : ℝ) \
    sieveCarrier N (fourModulusProduct t) N (t.2.1 : ℝ)

noncomputable def fourModulusGain (N : ℕ) (z w V : ℝ) : ℤ :=
  ∑ t ∈ fourModulusDomain N z w V, (s3FourSourceTerm N t - fourModulusQuotientTerm N t)

theorem fourModulus_domains_disjoint (N : ℕ) (z w V : ℝ) :
    Disjoint (s3DistinctQuadruples N (orderedTriples (primeWindow N z w)))
      (s3Upsilon11Range N z w V) := by
  apply disjoint_left.mpr
  rintro ⟨a, b, c, d⟩ h10 h11
  obtain ⟨_, _, _, _, _, _, _, _, _, hdw, _⟩ := mem_s3_first_quadruples.mp h10
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hwd, _⟩ :=
    mem_s3Upsilon11Range.mp h11
  exact (not_lt_of_ge hwd) hdw

theorem fourModulusDomain_labels {N a b c d : ℕ} {z w V : ℝ}
    (ht : (a, b, c, d) ∈ fourModulusDomain N z w V) :
    a.Prime ∧ a.Coprime N ∧ z ≤ (a : ℝ) ∧
      b.Prime ∧ b.Coprime N ∧ c.Prime ∧ c.Coprime N ∧
      d.Prime ∧ d.Coprime N ∧ a < b ∧ b < c ∧ c < d := by
  rcases mem_union.mp ht with h10 | h11
  · obtain ⟨ha, haN, hz, hb, hbN, hc, hcN, hd, hdN, _, hab, hbc, hcd⟩ :=
      mem_s3_first_quadruples.mp h10
    exact ⟨ha, haN, hz, hb, hbN, hc, hcN, hd, hdN, hab, hbc, hcd⟩
  · obtain ⟨ha, haN, hz, hb, hbN, hc, hcN, hd, hdN, hab, hbc, hcw, hwd, _⟩ :=
      mem_s3Upsilon11Range.mp h11
    exact ⟨ha, haN, hz, hb, hbN, hc, hcN, hd, hdN, hab, hbc,
      by exact_mod_cast hcw.trans_le hwd⟩

theorem fourModulus_moving_bound {N a b c d : ℕ} {z w V : ℝ}
    (ht : (a, b, c, d) ∈ s3Upsilon11Range N z w V) :
    (c : ℝ) * d < V := by
  obtain ⟨_, _, _, _, _, hc, _, _, _, _, _, _, _, hdV⟩ :=
    mem_s3Upsilon11Range.mp ht
  have hc0 : (0 : ℝ) < c := by exact_mod_cast hc.pos
  simpa only [mul_comm] using (lt_div_iff₀ hc0).mp hdV

theorem fourModulus_quotient_le_source (N : ℕ) (t : ℕ × ℕ × ℕ × ℕ) :
    fourModulusQuotientTerm N t ≤ s3FourSourceTerm N t :=
  sieveCount_le_source_selected_modulus N _ N _

theorem fourModulusGain_nonneg (N : ℕ) (z w V : ℝ) :
    0 ≤ fourModulusGain N z w V :=
  sum_nonneg (fun t _ => sub_nonneg.mpr (fourModulus_quotient_le_source N t))

theorem fourModulus_quotient_subset_source (N D : ℕ) (b : ℝ) :
    sieveCarrier N D N b ⊆ sourceSieveCarrier N D (D * N) b := by
  rw [sourceSieveCarrier_of_dvd_modulus N (dvd_mul_right D N), mul_comm D N]
  exact sieveCarrier_subset_mul_modulus N D N D b

theorem fourModulus_difference_eq_card (N : ℕ) (t : ℕ × ℕ × ℕ × ℕ) :
    s3FourSourceTerm N t - fourModulusQuotientTerm N t =
      ((fourModulusLoss N t).card : ℤ) := by
  have h := card_sdiff_add_card_eq_card
    (fourModulus_quotient_subset_source N (fourModulusProduct t) (t.2.1 : ℝ))
  have h' : ((fourModulusLoss N t).card : ℤ) + fourModulusQuotientTerm N t =
      s3FourSourceTerm N t := by
    unfold fourModulusLoss fourModulusQuotientTerm s3FourSourceTerm
      sieveCount sourceSieveCount
    exact_mod_cast h
  omega

/-- The other three selected primes lie at or above the strict cutoff.
Their exemptions do not change this carrier. -/
theorem fourModulus_source_carrier {N a b c d : ℕ} {z w V : ℝ}
    (ht : (a, b, c, d) ∈ fourModulusDomain N z w V) :
    sourceSieveCarrier N (a * b * c * d) ((a * b * c * d) * N) (b : ℝ) =
      sieveCarrier N (a * b * c * d) (N * a) (b : ℝ) := by
  obtain ⟨_, _, _, hb, _, hc, _, hd, _, _, hbc, hcd⟩ :=
    fourModulusDomain_labels ht
  rw [sourceSieveCarrier_of_dvd_modulus N (dvd_mul_right (a * b * c * d) N)]
  have he (n : ℕ) :
      Sifted ((a * b * c * d) * N) n (b : ℝ) ↔ Sifted (N * a) n (b : ℝ) := by
    rw [show (a * b * c * d) * N = N * a * b * c * d by ring,
      sifted_mul_modulus_of_le hd (by exact_mod_cast (hbc.trans hcd).le),
      sifted_mul_modulus_of_le hc (by exact_mod_cast hbc.le),
      sifted_mul_modulus_of_le hb le_rfl]
  ext r
  simp only [sieveCarrier, mem_filter, he]

theorem fourModulusLoss_eq_filter {N a b c d : ℕ} {z w V : ℝ}
    (ht : (a, b, c, d) ∈ fourModulusDomain N z w V) :
    fourModulusLoss N (a, b, c, d) =
      (sieveCarrier N (a * b * c * d) (N * a) (b : ℝ)).filter
        (fun r => a ∣ (N - r) / (a * b * c * d)) := by
  obtain ⟨ha, haN, _, _, _, _, _, _, _, hab, _⟩ := fourModulusDomain_labels ht
  unfold fourModulusLoss fourModulusProduct
  dsimp only
  rw [fourModulus_source_carrier ht,
    sieveCarrier_mul_modulus_difference N (a * b * c * d) N a (b : ℝ) ha haN]
  simp only [show (a : ℝ) < b by exact_mod_cast hab, true_and]

theorem fourModulusLoss_first_square {N a b c d r : ℕ} {z w V : ℝ}
    (ht : (a, b, c, d) ∈ fourModulusDomain N z w V)
    (hr : r ∈ fourModulusLoss N (a, b, c, d)) :
    a ^ 2 ∣ N - r := by
  rw [fourModulusLoss_eq_filter ht] at hr
  obtain ⟨hr, haq⟩ := mem_filter.mp hr
  have hD := (mem_filter.mp hr).2.2.1
  have haD : a ∣ a * b * c * d :=
    ((dvd_mul_right a b).trans (dvd_mul_right (a * b) c)).trans
      (dvd_mul_right (a * b * c) d)
  have hs := Nat.mul_dvd_mul haD haq
  rw [Nat.mul_div_cancel' hD] at hs
  simpa only [pow_two] using hs

theorem fourModulusLoss_mem_square {N : ℕ} {z w V : ℝ}
    (hN : 4 ≤ N) (he : Even N) {t : ℕ × ℕ × ℕ × ℕ} {r : ℕ}
    (ht : t ∈ fourModulusDomain N z w V) (hr : r ∈ fourModulusLoss N t) :
    r ∈ primeIndices N ∧ N - r ∈ largePrimeSquareExceptions N z := by
  obtain ⟨hrR, hrp, _⟩ := mem_filter.mp (mem_sdiff.mp hr).1
  have hrN : r ≤ N := by simpa only [mem_range, Nat.lt_succ_iff] using hrR
  obtain ⟨ha, _, hza, _⟩ := fourModulusDomain_labels ht
  exact ⟨mem_primeIndices.mpr ⟨hrN, hrp⟩,
    mem_largePrimeSquareExceptions.mpr
      ⟨complement_pos_of_even hN he hrN hrp, Nat.sub_le N r,
        t.1, ha, hza, fourModulusLoss_first_square ht hr⟩⟩

end Wu2008DoubleSieve
