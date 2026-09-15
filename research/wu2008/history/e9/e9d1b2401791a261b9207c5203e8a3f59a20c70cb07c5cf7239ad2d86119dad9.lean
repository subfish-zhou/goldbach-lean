import MathlibNt.Wu2008DoubleSieve.S3FourPrimeCompletion

/-!
# The retained, signed finite Delta2 decomposition

Wu08, Lemma 2.2, source lines 445--527.  The three disjoint subranges do
not exhaust the positive triple range.  Moreover the third range has a
positive cutoff difference, and relaxing a modulus has a positive cost.
None of these contributions is discarded here.

All triple counts are the existing strict quotient counts.  The four-prime
majorants use the unscaled `P(d*N)` counts, not the printed `P(N)` counts.
The moving-range excess is an enlargement loss, not an unavoidable error.
-/

namespace Wu2008DoubleSieve

open Finset
open scoped Classical

noncomputable def s3PositiveTripleTerm (N : ℕ) (t : ℕ × ℕ × ℕ) : ℤ :=
  sieveCount N (t.1 * t.2.1 * t.2.2) (N * t.1) (t.2.1 : ℝ)

noncomputable def s3TripleModulusGain (N : ℕ) (t : ℕ × ℕ × ℕ) : ℤ :=
  s3PositiveTripleTerm N t -
    sieveCount N (t.1 * t.2.1 * t.2.2) N (t.2.1 : ℝ)

noncomputable def s3ThirdCutoffGain (N : ℕ) (t : ℕ × ℕ × ℕ) : ℤ :=
  s3PositiveTripleTerm N t -
    sieveCount N (t.1 * t.2.1 * t.2.2) (N * t.1) (t.2.2 : ℝ)

noncomputable def s3LeftoverTripleMass (N : ℕ) (z w u v : ℝ) : ℤ :=
  ∑ t ∈ orderedTriples (primeWindow N z v) \
      (orderedTriples (primeWindow N z w) ∪ s3SecondRange N z w u ∪
        s3ThirdRange N w u), s3PositiveTripleTerm N t

noncomputable def s3RetainedTripleMass (N : ℕ) (z w u v : ℝ) : ℤ :=
  s3LeftoverTripleMass N z w u v +
    (∑ t ∈ orderedTriples (primeWindow N z w), s3TripleModulusGain N t) +
    (∑ t ∈ s3SecondRange N z w u, s3TripleModulusGain N t) +
    ∑ t ∈ s3ThirdRange N w u, s3ThirdCutoffGain N t

theorem s3TripleModulusGain_nonneg (N : ℕ) (t : ℕ × ℕ × ℕ) :
    0 ≤ s3TripleModulusGain N t :=
  sub_nonneg.mpr (s3_sieveCount_le_mul_modulus N _ N t.1 _)

theorem s3ThirdCutoffGain_nonneg {N : ℕ} {z w : ℝ}
    {t : ℕ × ℕ × ℕ} (ht : t ∈ s3ThirdRange N z w) :
    0 ≤ s3ThirdCutoffGain N t :=
  sub_nonneg.mpr (sieveCount_antitone N _ _
    (by exact_mod_cast (mem_s3ThirdRange.mp ht).2.2.2.le))

theorem s3RetainedTripleMass_nonneg (N : ℕ) (z w u v : ℝ) :
    0 ≤ s3RetainedTripleMass N z w u v := by
  unfold s3RetainedTripleMass s3LeftoverTripleMass
  exact add_nonneg (add_nonneg (add_nonneg
    (sum_nonneg (fun _ _ => sieveCount_nonneg _ _ _ _))
    (sum_nonneg (fun t _ => s3TripleModulusGain_nonneg N t)))
    (sum_nonneg (fun t _ => s3TripleModulusGain_nonneg N t)))
    (sum_nonneg (fun _ ht => s3ThirdCutoffGain_nonneg ht))

/-- Exact replacement for the inequality that previously discarded the
leftover triples and both kinds of positive difference. -/
theorem s3_delta2_exact_retained (N : ℕ) (z w u v : ℝ)
    (hwv : w ≤ v) (huv : u ≤ v)
    (hthird : s3ThirdRange N w u ⊆ orderedTriples (primeWindow N z v)) :
    s3Delta2Quotient N z w u v =
      s3RetainedTripleMass N z w u v -
        (∑ t ∈ orderedTriples (primeWindow N z w), s3FourPrimeRemainder N t) -
        ∑ t ∈ s3SecondRange N z w u, s3FourPrimeRemainder N t := by
  let A := orderedTriples (primeWindow N z w)
  let B := s3SecondRange N z w u
  let C := s3ThirdRange N w u
  let T := orderedTriples (primeWindow N z v)
  obtain ⟨hAB, hAC, hBC⟩ := s3_delta_ranges_disjoint N z w u
  have hsub : A ∪ B ∪ C ⊆ T :=
    union_subset (union_subset (s3_ordered_triples_mono N z hwv)
      ((filter_subset _ _).trans (s3_ordered_triples_mono N z huv))) hthird
  have hsum := sum_sdiff (f := s3PositiveTripleTerm N) hsub
  rw [sum_union (disjoint_union_left.mpr ⟨hAC, hBC⟩), sum_union hAB] at hsum
  have hfirst : ∀ t ∈ A,
      sieveCount N (t.1 * t.2.1 * t.2.2) N (t.1 : ℝ) =
        sieveCount N (t.1 * t.2.1 * t.2.2) N (t.2.1 : ℝ) +
          s3FourPrimeRemainder N t := by
    rintro ⟨a, b, c⟩ ht
    have h := s3_triple_cutoff_difference N a b c (mem_filter.mp ht).2.1.le
    dsimp only
    omega
  have hsecond : ∀ t ∈ B,
      sieveCount N (t.1 * t.2.1 * t.2.2) N (t.1 : ℝ) =
        sieveCount N (t.1 * t.2.1 * t.2.2) N (t.2.1 : ℝ) +
          s3FourPrimeRemainder N t := by
    rintro ⟨a, b, c⟩ ht
    have h := s3_triple_cutoff_difference N a b c
      (mem_filter.mp (mem_filter.mp ht).1).2.1.le
    dsimp only
    omega
  have hA := sum_congr rfl hfirst
  have hB := sum_congr rfl hsecond
  rw [sum_add_distrib] at hA hB
  unfold s3Delta2Quotient s3RetainedTripleMass s3LeftoverTripleMass
  rw [variableS3Triples_eq_third_range_sum]
  simp only [s3TripleModulusGain, s3ThirdCutoffGain, sum_sub_distrib]
  dsimp only [A, B, C, T, s3PositiveTripleTerm] at hsum hA hB ⊢
  omega

noncomputable def s3FourModulusGain (N : ℕ) (T : Finset (ℕ × ℕ × ℕ)) : ℤ :=
  ∑ t ∈ s3DistinctQuadruples N T,
    (s3FourSourceTerm N t -
      sieveCount N (t.1 * t.2.1 * t.2.2.1 * t.2.2.2) N (t.2.1 : ℝ))

theorem s3FourModulusGain_nonneg (N : ℕ) (T : Finset (ℕ × ℕ × ℕ)) :
    0 ≤ s3FourModulusGain N T :=
  sum_nonneg (fun _ _ => sub_nonneg.mpr (sieveCount_le_source_selected_modulus N _ N _))

theorem s3_fourprime_sum_exact_majorant (N : ℕ) (T : Finset (ℕ × ℕ × ℕ))
    (hT : ∀ t ∈ T, t.1.Prime ∧ t.1.Coprime N ∧ t.1 < t.2.1) :
    (∑ t ∈ T, s3FourPrimeRemainder N t) =
      s3FourSourceMajorant N T - s3FourModulusGain N T +
        s3RepeatedFirstPrimeMass N T := by
  rw [s3_fourprime_sum_split N T hT]
  simp only [s3FourSourceMajorant, s3FourModulusGain, s3FourSourceTerm,
    s3RepeatedFirstPrimeMass, sum_sub_distrib]
  omega

noncomputable def s3Upsilon11MissingMass (N : ℕ) (z w u V : ℝ) : ℤ :=
  ∑ t ∈ s3Upsilon11Range N z w V \
    s3DistinctQuadruples N (s3SecondRange N z w u), s3FourSourceTerm N t

theorem s3Upsilon11MissingMass_nonneg (N : ℕ) (z w u V : ℝ) :
    0 ≤ s3Upsilon11MissingMass N z w u V :=
  sum_nonneg (fun _ _ => Int.natCast_nonneg _)

/-- Every term omitted from the old majorant is restored with its sign.
To pay the excess it is enough to use their aggregate; no pointwise
cancellation or smallness of the excess alone is required. -/
theorem s3_delta2_exact_moving (N : ℕ) (z w u v V : ℝ)
    (hwv : w ≤ v) (huv : u ≤ v)
    (hthird : s3ThirdRange N w u ⊆ orderedTriples (primeWindow N z v)) :
    s3Delta2Quotient N z w u v +
        s3FourSourceMajorant N (orderedTriples (primeWindow N z w)) +
        s3Upsilon11Source N z w V =
      s3RetainedTripleMass N z w u v +
        s3FourModulusGain N (orderedTriples (primeWindow N z w)) +
        s3FourModulusGain N (s3SecondRange N z w u) +
        s3Upsilon11MissingMass N z w u V -
        s3Upsilon11ExcessMass N z w u V -
        s3RepeatedFirstPrimeMass N (orderedTriples (primeWindow N z w)) -
        s3RepeatedFirstPrimeMass N (s3SecondRange N z w u) := by
  have hA := s3_fourprime_sum_exact_majorant N
    (orderedTriples (primeWindow N z w)) (by
      rintro ⟨a, b, c⟩ ht
      obtain ⟨ha, haN, _, _, _, _, _, _, hab, _⟩ := mem_s3_ordered_triples.mp ht
      exact ⟨ha, haN, hab⟩)
  have hB := s3_fourprime_sum_exact_majorant N (s3SecondRange N z w u) (by
    rintro ⟨a, b, c⟩ ht
    obtain ⟨ha, haN, _, _, _, _, _, _, hab, _⟩ :=
      mem_s3_ordered_triples.mp (mem_filter.mp ht).1
    exact ⟨ha, haN, hab⟩)
  have hD := s3_delta2_exact_retained N z w u v hwv huv hthird
  have hM := s3_second_source_eq_moving_add_excess_sub_missing N z w u V
  change _ = _ + _ - s3Upsilon11MissingMass N z w u V at hM
  omega

theorem s3_delta2_exact_source_parameters {N : ℕ} {κ₁ κ₂ : ℝ}
    (hN : 1 ≤ N) (hκ₁ : 1 / 18 ≤ κ₁) (hκ : κ₁ ≤ κ₂)
    (hupper : 3 * κ₁ + κ₂ ≤ 1 / 2) (hparam : 3 * κ₁ - κ₂ ≤ 1 / 6) :
    let z := (N : ℝ) ^ κ₁
    let w := (N : ℝ) ^ κ₂
    let u := (N : ℝ) ^ (1 / 2 - 3 * κ₁)
    let v := (N : ℝ) ^ (1 / 3 : ℝ)
    let V := (N : ℝ) ^ (1 / 2 - 2 * κ₁)
    s3Delta2Quotient N z w u v +
        s3FourSourceMajorant N (orderedTriples (primeWindow N z w)) +
        s3Upsilon11Source N z w V =
      s3RetainedTripleMass N z w u v +
        s3FourModulusGain N (orderedTriples (primeWindow N z w)) +
        s3FourModulusGain N (s3SecondRange N z w u) +
        s3Upsilon11MissingMass N z w u V -
        s3Upsilon11ExcessMass N z w u V -
        s3RepeatedFirstPrimeMass N (orderedTriples (primeWindow N z w)) -
        s3RepeatedFirstPrimeMass N (s3SecondRange N z w u) := by
  apply s3_delta2_exact_moving
  · apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN)
    linarith
  · apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN)
    linarith
  · exact s3ThirdRange_subset_source_triples hN hκ hparam

end Wu2008DoubleSieve
