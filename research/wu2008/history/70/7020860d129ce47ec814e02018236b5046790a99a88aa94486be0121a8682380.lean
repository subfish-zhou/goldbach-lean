import MathlibNt.Wu2008DoubleSieve.FourModulusTransportCarriers

/-!
# One square-exception budget with full four-label multiplicity

The two original domains are joined before the fibre count. The fibre
embeds into four independent slots of large prime divisors, not a set
of products and not a quotient by permutations.
-/

namespace Wu2008DoubleSieve

open Finset
open scoped Classical

theorem fourModulus_divisor_fibre_le {N n : ℕ} {κ w V : ℝ}
    (hN : 1 < N) (hn : 0 < n) (hnN : n ≤ N) (hκ : 0 < κ) :
    (((fourModulusDomain N ((N : ℝ) ^ κ) w V).filter
      (fun t => fourModulusProduct t ∣ n)).card : ℝ) ≤ (1 / κ) ^ 4 := by
  let F := largePrimeDivisors n ((N : ℝ) ^ κ)
  have hsub : (fourModulusDomain N ((N : ℝ) ^ κ) w V).filter
      (fun t => fourModulusProduct t ∣ n) ⊆ F ×ˢ (F ×ˢ (F ×ˢ F)) := by
    rintro ⟨a, b, c, d⟩ ht
    obtain ⟨ht, hD⟩ := mem_filter.mp ht
    obtain ⟨ha, _, hza, hb, _, hc, _, hd, _, hab, hbc, hcd⟩ :=
      fourModulusDomain_labels ht
    change a * b * c * d ∣ n at hD
    have han : a ∣ n := (((dvd_mul_right a b).trans
      (dvd_mul_right (a * b) c)).trans (dvd_mul_right (a * b * c) d)).trans hD
    have hbn : b ∣ n := (((dvd_mul_left b a).trans
      (dvd_mul_right (a * b) c)).trans (dvd_mul_right (a * b * c) d)).trans hD
    have hcn : c ∣ n := ((dvd_mul_left c (a * b)).trans
      (dvd_mul_right (a * b * c) d)).trans hD
    have hdn : d ∣ n := (dvd_mul_left d (a * b * c)).trans hD
    have hab' : (a : ℝ) ≤ b := by exact_mod_cast hab.le
    have hbc' : (b : ℝ) ≤ c := by exact_mod_cast hbc.le
    have hcd' : (c : ℝ) ≤ d := by exact_mod_cast hcd.le
    exact mem_product.mpr
      ⟨mem_largePrimeDivisors.mpr ⟨ha, han, hn.ne', hza⟩,
        mem_product.mpr
          ⟨mem_largePrimeDivisors.mpr ⟨hb, hbn, hn.ne', hza.trans hab'⟩,
            mem_product.mpr
              ⟨mem_largePrimeDivisors.mpr ⟨hc, hcn, hn.ne', (hza.trans hab').trans hbc'⟩,
                mem_largePrimeDivisors.mpr
                  ⟨hd, hdn, hn.ne', ((hza.trans hab').trans hbc').trans hcd'⟩⟩⟩⟩
  calc
    _ ≤ ((F ×ˢ (F ×ˢ (F ×ˢ F))).card : ℝ) := by exact_mod_cast card_le_card hsub
    _ = (F.card : ℝ) ^ 4 := by simp only [card_product, Nat.cast_mul]; ring
    _ ≤ _ := pow_le_pow_left₀ (Nat.cast_nonneg _)
      (largePrimeDivisors_card_le_inv hN hn hnN hκ) 4

theorem fourModulus_loss_fibre_le {N r : ℕ} {κ w V : ℝ}
    (hN : 1 < N) (hn : 0 < N - r) (hκ : 0 < κ) :
    (((fourModulusDomain N ((N : ℝ) ^ κ) w V).filter
      (fun t => r ∈ fourModulusLoss N t)).card : ℝ) ≤ (1 / κ) ^ 4 := by
  have hsub : (fourModulusDomain N ((N : ℝ) ^ κ) w V).filter
      (fun t => r ∈ fourModulusLoss N t) ⊆
      (fourModulusDomain N ((N : ℝ) ^ κ) w V).filter
        (fun t => fourModulusProduct t ∣ N - r) := by
    intro t ht
    obtain ⟨ht, hr⟩ := mem_filter.mp ht
    exact mem_filter.mpr ⟨ht, (mem_filter.mp (mem_sdiff.mp hr).1).2.2.1⟩
  exact (show (_ : ℝ) ≤ _ by exact_mod_cast card_le_card hsub).trans
    (fourModulus_divisor_fibre_le hN hn (Nat.sub_le N r) hκ)

theorem fourModulusGain_le {N : ℕ} {κ w V : ℝ}
    (hN : 4 ≤ N) (he : Even N) (hκ : 0 < κ) (hz : 2 ≤ (N : ℝ) ^ κ) :
    (fourModulusGain N ((N : ℝ) ^ κ) w V : ℝ) ≤
      2 / κ ^ 4 * (N : ℝ) ^ (1 - κ) := by
  let T := fourModulusDomain N ((N : ℝ) ^ κ) w V
  let E := (primeIndices N).filter
    (fun r => N - r ∈ largePrimeSquareExceptions N ((N : ℝ) ^ κ))
  have hf : ∀ t ∈ T, fourModulusLoss N t ⊆ E := by
    intro t ht r hr
    exact mem_filter.mpr (fourModulusLoss_mem_square hN he ht hr)
  have hmass : (fourModulusGain N ((N : ℝ) ^ κ) w V : ℝ) =
      ∑ t ∈ T, ((fourModulusLoss N t).card : ℝ) := by
    simp only [fourModulusGain, fourModulus_difference_eq_card,
      Int.cast_sum, Int.cast_natCast, T]
  rw [hmass, endpoint_sum_cards_eq T E (fourModulusLoss N) hf]
  have hcard : (E.card : ℝ) ≤ 2 * (N : ℝ) ^ (1 - κ) := by
    calc
      _ ≤ ((largePrimeSquareExceptions N ((N : ℝ) ^ κ)).card : ℝ) := by
        exact_mod_cast primeComplement_filter_card_le N
          (largePrimeSquareExceptions N ((N : ℝ) ^ κ))
      _ ≤ _ := largePrimeSquareExceptions_card_le_rpow (by omega) hz
  calc
    _ ≤ ∑ _r ∈ E, (1 / κ) ^ 4 := by
      apply sum_le_sum
      intro r hr
      have hn := (mem_largePrimeSquareExceptions.mp (mem_filter.mp hr).2).1
      exact fourModulus_loss_fibre_le (by omega) hn hκ
    _ = (E.card : ℝ) * (1 / κ) ^ 4 := by simp
    _ ≤ (2 * (N : ℝ) ^ (1 - κ)) * (1 / κ) ^ 4 :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by rw [div_pow, one_pow]; ring

theorem fourModulusGain_eq_two_sums (N : ℕ) (z w V : ℝ) :
    fourModulusGain N z w V =
      (∑ t ∈ s3DistinctQuadruples N (orderedTriples (primeWindow N z w)),
        (s3FourSourceTerm N t - fourModulusQuotientTerm N t)) +
      ∑ t ∈ s3Upsilon11Range N z w V,
        (s3FourSourceTerm N t - fourModulusQuotientTerm N t) := by
  exact sum_union (fourModulus_domains_disjoint N z w V)

theorem fourModulusGain_eq_source_sub_quotient (N : ℕ) (z w V : ℝ) :
    fourModulusGain N z w V =
      s3FourSourceMajorant N (orderedTriples (primeWindow N z w)) +
        s3Upsilon11Source N z w V -
        (∑ t ∈ s3DistinctQuadruples N (orderedTriples (primeWindow N z w)),
          fourModulusQuotientTerm N t) -
        ∑ t ∈ s3Upsilon11Range N z w V, fourModulusQuotientTerm N t := by
  rw [fourModulusGain_eq_two_sums]
  simp only [sum_sub_distrib, s3FourSourceMajorant, s3Upsilon11Source, s3FourSourceTerm]
  ring

/-- The sum of both actual differences has one quartic budget. -/
theorem fourModulus_original_two_sums_bounds {N : ℕ} {κ w V : ℝ}
    (hN : 4 ≤ N) (he : Even N) (hκ : 0 < κ) (hz : 2 ≤ (N : ℝ) ^ κ) :
    0 ≤ ((∑ t ∈ s3DistinctQuadruples N
        (orderedTriples (primeWindow N ((N : ℝ) ^ κ) w)),
        (s3FourSourceTerm N t - fourModulusQuotientTerm N t)) +
      ∑ t ∈ s3Upsilon11Range N ((N : ℝ) ^ κ) w V,
        (s3FourSourceTerm N t - fourModulusQuotientTerm N t) : ℤ) ∧
    (((∑ t ∈ s3DistinctQuadruples N
        (orderedTriples (primeWindow N ((N : ℝ) ^ κ) w)),
        (s3FourSourceTerm N t - fourModulusQuotientTerm N t)) +
      ∑ t ∈ s3Upsilon11Range N ((N : ℝ) ^ κ) w V,
        (s3FourSourceTerm N t - fourModulusQuotientTerm N t) : ℤ) : ℝ) ≤
      2 / κ ^ 4 * (N : ℝ) ^ (1 - κ) := by
  rw [← fourModulusGain_eq_two_sums]
  exact ⟨fourModulusGain_nonneg N _ w V, fourModulusGain_le hN he hκ hz⟩

end Wu2008DoubleSieve
