import MathlibNt.Wu2008DoubleSieve.TruncatedSixthInjection

/-!
# Finite assembly with the omitted positive pairs paying the excess

All four-prime sums in the comparison are quotient sums. The exact
accepted mixed identity is converted algebraically, without estimating
or paying a selected-modulus majorant.
-/

namespace Wu2008DoubleSieve

open Finset
open scoped Classical

theorem truncatedSixth_quotient_lower_weights (N : ℕ) (z w u v V : ℝ)
    (hzw : z ≤ w) (hwu : w ≤ u) :
    lowerWeightRHS N w u + lowerWeightRHS N z v =
      fourModulusQuotientEleven N z w u v V + s3Delta2Quotient N z w u v +
        (∑ t ∈ s3DistinctQuadruples N (orderedTriples (primeWindow N z w)),
          fourModulusQuotientTerm N t) +
        (∑ t ∈ s3Upsilon11Range N z w V, fourModulusQuotientTerm N t) +
        (∑ t ∈ orderedTriples (primeWindow N w u), s3PositiveTripleTerm N t) +
        s3VariableSlack N w u - s3PairRepeatedBudget N w u - 2 * lowerS2 N z v := by
  have hW := finiteElevenMixed_exact_lower_weights N z w u v V hzw hwu
  have hE := fourModulus_eleven_difference N z w u v V
  have hG := fourModulusGain_eq_source_sub_quotient N z w V
  omega

theorem truncatedSixth_delta_exact (N : ℕ) (z w u v V : ℝ)
    (hwv : w ≤ v) (huv : u ≤ v) (hu : 0 ≤ u) (hV : V ≤ z * u)
    (hthird : s3ThirdRange N w u ⊆ orderedTriples (primeWindow N z v)) :
    s3Delta2Quotient N z w u v +
        (∑ t ∈ s3DistinctQuadruples N (orderedTriples (primeWindow N z w)),
          fourModulusQuotientTerm N t) +
        (∑ t ∈ s3Upsilon11Range N z w V, fourModulusQuotientTerm N t) =
      s3RetainedTripleMass N z w u v -
        s3RepeatedFirstPrimeMass N (orderedTriples (primeWindow N z w)) -
        s3RepeatedFirstPrimeMass N (s3SecondRange N z w u) -
        truncatedSixthExcessMass N z w u V := by
  have hA := s3_fourprime_sum_split N (orderedTriples (primeWindow N z w)) (by
    rintro ⟨a, b, c⟩ ht
    obtain ⟨ha, haN, _, _, _, _, _, _, hab, _⟩ := mem_s3_ordered_triples.mp ht
    exact ⟨ha, haN, hab⟩)
  have hB := s3_fourprime_sum_split N (s3SecondRange N z w u) (by
    rintro ⟨a, b, c⟩ ht
    obtain ⟨ha, haN, _, _, _, _, _, _, hab, _⟩ :=
      mem_s3_ordered_triples.mp (mem_filter.mp ht).1
    exact ⟨ha, haN, hab⟩)
  have hD := s3_delta2_exact_retained N z w u v hwv huv hthird
  have hsplit := truncatedSixth_rectangle_split (N := N) (w := w) hu hV
  simp only [fourModulusQuotientTerm, fourModulusProduct] at hsplit ⊢
  simp only [s3RepeatedFirstPrimeMass]
  omega

/-- The actual injection removes the entire moving excess from the
upper bound. Only the already known repeated-prime budgets remain. -/
theorem truncatedSixth_le_lower_weights (N : ℕ) (z w u v V : ℝ)
    (hzw : z ≤ w) (hwu : w ≤ u) (hwv : w ≤ v) (huv : u ≤ v)
    (hu : 0 ≤ u) (hV : V ≤ z * u) (hv : 0 ≤ v) (hNv : (N : ℝ) ≤ v ^ 3)
    (hthird : s3ThirdRange N w u ⊆ orderedTriples (primeWindow N z v)) :
    truncatedSixthExpression N z w u v V ≤
      lowerWeightRHS N w u + lowerWeightRHS N z v +
        s3RepeatedFirstPrimeMass N (orderedTriples (primeWindow N z w)) +
        s3RepeatedFirstPrimeMass N (s3SecondRange N z w u) +
        s3PairRepeatedBudget N w u := by
  have hW := truncatedSixth_quotient_lower_weights N z w u v V hzw hwu
  have hD := truncatedSixth_delta_exact N z w u v V hwv huv hu hV hthird
  have hX := truncatedSixth_excess_le_omitted N z w u V
  have hR := s3RetainedTripleMass_nonneg N z w u v
  have hS := s3VariableSlack_nonneg N w u
  have hT : 0 ≤ ∑ t ∈ orderedTriples (primeWindow N w u), s3PositiveTripleTerm N t :=
    sum_nonneg (fun _ _ => sieveCount_nonneg _ _ _ _)
  rw [lowerS2_eq_zero_of_cubic_cutoff hv hNv] at hW
  unfold truncatedSixthExpression
  rw [truncatedSixth_full_sub_kept]
  omega

theorem truncatedSixth_le_count_explicit {N : ℕ} {z w u v V : ℝ}
    (hN : 0 < N) (hz : 2 ≤ z)
    (hzw : z ≤ w) (hwu : w ≤ u) (hwv : w ≤ v) (huv : u ≤ v)
    (hu : 0 ≤ u) (hV : V ≤ z * u) (hv : 0 ≤ v) (hNv : (N : ℝ) ≤ v ^ 3)
    (hthird : s3ThirdRange N w u ⊆ orderedTriples (primeWindow N z v)) :
    (truncatedSixthExpression N z w u v V : ℝ) ≤
      4 * ((MathlibNt.Wu2008DoubleSieve.wuPrimeComplements N).card : ℝ) +
        (4 * (N : ℝ) / w + 2 * (Real.sqrt N + 1)) +
        (4 * (N : ℝ) / z + 2 * (Real.sqrt N + 1)) +
        (s3RepeatedFirstPrimeMass N (orderedTriples (primeWindow N z w)) : ℝ) +
        (s3RepeatedFirstPrimeMass N (s3SecondRange N z w u) : ℝ) +
        (s3PairRepeatedBudget N w u : ℝ) := by
  have h := (Int.cast_le (R := ℝ)).mpr
    (truncatedSixth_le_lower_weights N z w u v V hzw hwu hwv huv hu hV hv hNv hthird)
  push_cast at h
  have hW := lowerWeightRHS_le_count_add_explicit_error hN (hz.trans hzw) u
  have hZ := lowerWeightRHS_le_count_add_explicit_error hN hz v
  linarith

end Wu2008DoubleSieve
