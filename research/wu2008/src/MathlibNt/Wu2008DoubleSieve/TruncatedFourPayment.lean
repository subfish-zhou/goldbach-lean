import MathlibNt.Wu2008DoubleSieve.TruncatedFourGeometry

/-! Actual original Q10+Q11, with every unit and bad-output label paid once
within its original domain. This is not an analytic density estimate. -/
namespace Wu2008DoubleSieve.TruncatedFourPhysical
open Finset Real Filter
open scoped Classical

theorem root_and_one_power {N : ℕ} (hN : 1 ≤ N) :
    sqrt N + 1 + (N : ℝ)^(1-truncatedSixthLowerAlpha) ≤
      3*(N : ℝ)^(1-truncatedSixthLowerAlpha) := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hroot : sqrt N ≤ (N : ℝ)^(1-truncatedSixthLowerAlpha) := by
    rw [sqrt_eq_rpow]
    exact rpow_le_rpow_of_exponent_le hNr fixed_exponents.2.2.2
  have hone := one_le_rpow hNr (show 0 ≤ 1-truncatedSixthLowerAlpha by
    linarith [fixed_exponents.2.2.2])
  linarith

/-- Both exceptional cardinalities retain the original four-slot multiplicities. -/
theorem all_exceptional_power {N : ℕ} (hN : 4 ≤ N) (he : Even N) :
    ((exceptional N (T10 N)).card : ℝ) + (exceptional N (T11 N)).card ≤
      6/truncatedSixthLowerAlpha^4 * (N : ℝ)^(1-truncatedSixthLowerAlpha) := by
  have hX : 0 ≤ (N : ℝ)^(1-truncatedSixthLowerAlpha) := rpow_nonneg (Nat.cast_nonneg N) _
  have h10 := exceptional_bound hN he fixed_exponents.1 hX (T10_sub N)
    (fun _ ht => T10_cap (by omega) ht)
  have h11 := exceptional_bound hN he fixed_exponents.1 hX (T11_sub N)
    (fun _ ht => T11_cap (by omega) ht)
  calc
    _ ≤ (1/truncatedSixthLowerAlpha)^4 *
        (sqrt N + 1 + (N : ℝ)^(1-truncatedSixthLowerAlpha)) +
      (1/truncatedSixthLowerAlpha)^4 *
        (sqrt N + 1 + (N : ℝ)^(1-truncatedSixthLowerAlpha)) := add_le_add h10 h11
    _ = (2*(1/truncatedSixthLowerAlpha)^4) *
        (sqrt N + 1 + (N : ℝ)^(1-truncatedSixthLowerAlpha)) := by ring
    _ ≤ (2*(1/truncatedSixthLowerAlpha)^4) *
        (3*(N : ℝ)^(1-truncatedSixthLowerAlpha)) :=
      mul_le_mul_of_nonneg_left (root_and_one_power (by omega)) (by positivity)
    _ = _ := by ring

/-- Uniform complete exceptional payment. The accepted power/log budget
already includes the positive lower comparison C(1) <= C(N). -/
theorem all_exceptional_payment {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      2 ≤ (N : ℝ)^truncatedSixthLowerAlpha ∧
      ((exceptional N (T10 N)).card : ℝ) + (exceptional N (T11 N)).card ≤
        ε*wuSingularSeries N*N/log N^(2 : ℕ) := by
  obtain ⟨T,hT⟩ := eventually_atTop.mp
    (fourModulus_power_budget fixed_exponents.1 (show 0 < ε/3 by positivity))
  refine ⟨max 4 T, le_max_left _ _, ?_⟩
  intro N hN he
  obtain ⟨hN4,hcut,hpay⟩ := hT N ((le_max_right _ _).trans hN)
  refine ⟨hcut, (all_exceptional_power hN4 he).trans ?_⟩
  calc
    _ = 3*(2/truncatedSixthLowerAlpha^4 * (N : ℝ)^(1-truncatedSixthLowerAlpha)) := by ring
    _ ≤ 3*((ε/3)*wuSingularSeries N*N/log N^(2 : ℕ)) :=
      mul_le_mul_of_nonneg_left hpay (by norm_num)
    _ = _ := by ring

theorem original_pair_finite {N : ℕ} (hN : 4 ≤ N) (he : Even N) :
    (Q10 N : ℝ) + (Q11 N : ℝ) ≤ (Physical10 N).card + (Physical11 N).card +
      ((exceptional N (T10 N)).card : ℝ) + (exceptional N (T11 N)).card := by
  unfold Q10 Q11
  rw [source_cast, source_cast]
  have h10 := raw_le_physical_exceptional (S := T10 N) hN he
  have h11 := raw_le_physical_exceptional (S := T11 N) hN he
  have hh : (raw N (T10 N)).card + (raw N (T11 N)).card ≤
      (Physical10 N).card + (Physical11 N).card +
      (exceptional N (T10 N)).card + (exceptional N (T11 N)).card := by
    unfold Physical10 Physical11
    omega
  exact_mod_cast hh

/-- The requested endpoint: no count, density or payment assumption. -/
theorem original_tenth_eleventh_upper {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (Q10 N : ℝ) + (Q11 N : ℝ) ≤ (Physical10 N).card + (Physical11 N).card +
        ε*wuSingularSeries N*N/log N^(2 : ℕ) := by
  obtain ⟨T,hT,hpay⟩ := all_exceptional_payment hε
  refine ⟨T,hT,?_⟩
  intro N hN he
  have hfinite := original_pair_finite (hT.trans hN) he
  have hp := (hpay N hN he).2
  linarith only [hfinite,hp]

/-- Literal original sums, integer first and real afterwards, including the
strict moving V/c endpoint in the unchanged eleventh domain. -/
theorem original_sums_upper {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      let z := (N : ℝ)^truncatedSixthLowerAlpha
      let w := (N : ℝ)^truncatedSixthLowerBeta
      let V := (N : ℝ)^truncatedSixthLowerLambda
      ((∑ t ∈ s3DistinctQuadruples N (orderedTriples (primeWindow N z w)),
        sieveCount N (t.1*t.2.1*t.2.2.1*t.2.2.2) N (t.2.1 : ℝ) : ℤ) : ℝ) +
      ((∑ t ∈ s3Upsilon11Range N z w V,
        sieveCount N (t.1*t.2.1*t.2.2.1*t.2.2.2) N (t.2.1 : ℝ) : ℤ) : ℝ) ≤
      (Physical10 N).card + (Physical11 N).card + ε*wuSingularSeries N*N/log N^(2 : ℕ) :=
  original_tenth_eleventh_upper hε

end Wu2008DoubleSieve.TruncatedFourPhysical
