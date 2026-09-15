import MathlibNt.Wu2008DoubleSieve.FifthPairPositiveAssembly
import MathlibNt.Wu2008DoubleSieve.SingleUpperClassicalAssembly
import MathlibNt.Wu2008DoubleSieve.NinthCoefficientClosure
import MathlibNt.Wu2008DoubleSieve.TruncatedSixth

/-!
# A classical lower bound for the original truncated-sixth expression

The accepted positive, two-single and ninth producers are combined before
subtracting the four still unestimated actual negative counts. The overlap
of the singles is counted twice. No coefficient positivity is asserted.
All finite arithmetic is over the integers, followed by the real cast.
-/

namespace Wu2008DoubleSieve.TruncatedElevenSignedLower

open Finset Real
open SingleUpperCounts SingleUpperClassicalLimit
open scoped Classical

/-- Exact cutoff identities; there is no change of ninth-term carrier. -/
theorem ninth_cutoffs_literal (N : ℕ) :
    ninthProfileW N = (N : ℝ)^truncatedSixthLowerBeta ∧
    ninthProfileU N = (N : ℝ)^truncatedSixthLowerSigma := by
  constructor <;> rfl

/-- The accepted positive terms minus the original third and fourth terms.
The error is split before taking the common maximum threshold. -/
theorem first_six_actual_lower {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (24*wuLowerCoefficient (1/(2*truncatedSixthLowerAlpha)) +
        8*wuLowerCoefficient (1/(2*truncatedSixthLowerBeta)) + fifthPairFlin +
        truncatedSixthLowerF6lin + 47/481250 -
        Glin (1/3) - Glin truncatedSixthLowerSigma - ε)*
          wuSingularSeries N*N/log N^(2 : ℕ) ≤
      3*(sieveCount N 1 N ((N : ℝ)^truncatedSixthLowerAlpha) : ℝ) +
        (sieveCount N 1 N ((N : ℝ)^truncatedSixthLowerBeta) : ℝ) +
        (fifthPairCount N : ℝ) +
        (truncatedSixthMass N ((N : ℝ)^truncatedSixthLowerAlpha)
          ((N : ℝ)^truncatedSixthLowerBeta) ((N : ℝ)^truncatedSixthLowerSigma)
          ((N : ℝ)^truncatedSixthLowerLambda) : ℝ) -
        (U N (1/3) : ℝ) - (U N truncatedSixthLowerSigma : ℝ) := by
  obtain ⟨TP, hTP, hP⟩ := first_second_fifth_sixth_actual_lower (half_pos hε)
  obtain ⟨TS, _hTS, hS⟩ :=
    SingleUpperClassicalAssembly.original_third_fourth_Glin_upper (half_pos hε)
  refine ⟨max TP TS, hTP.trans (le_max_left _ _), ?_⟩
  intro N hN he
  have hp := hP N ((le_max_left _ _).trans hN) he
  have hs := hS N ((le_max_right _ _).trans hN) he
  unfold truncatedSixthMassScale at hs
  calc
    _ = (24*wuLowerCoefficient (1/(2*truncatedSixthLowerAlpha)) +
        8*wuLowerCoefficient (1/(2*truncatedSixthLowerBeta)) + fifthPairFlin +
        truncatedSixthLowerF6lin + 47/481250 - ε/2)*
          wuSingularSeries N*N/log N^(2 : ℕ) -
        (Glin (1/3) + Glin truncatedSixthLowerSigma + ε/2)*
          (wuSingularSeries N*N/log N^(2 : ℕ)) := by ring
    _ ≤ _ := by linarith only [hp, hs]

/-- The accepted ninth bound on the exact original cutoffs and common scale. -/
theorem original_ninth_upper {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (variableS3Main N ((N : ℝ)^truncatedSixthLowerBeta)
        ((N : ℝ)^truncatedSixthLowerSigma) : ℝ) ≤
      (8*J9 + ε)*wuSingularSeries N*N/log N^(2 : ℕ) := by
  obtain ⟨T, hT, h⟩ := variableS3Main_upper_F9 hε
  refine ⟨T, hT, ?_⟩
  intro N hN he
  simpa only [(ninth_cutoffs_literal N).1, (ninth_cutoffs_literal N).2] using h N hN he

/-- Terms 1--6 (with the retained sixth) and term 9, with original weights.
First-six and ninth receive epsilon/2 before the common maximum is chosen. -/
theorem first_six_sub_ninth_actual_lower {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (24*wuLowerCoefficient (1/(2*truncatedSixthLowerAlpha)) +
        8*wuLowerCoefficient (1/(2*truncatedSixthLowerBeta)) + fifthPairFlin +
        truncatedSixthLowerF6lin + 47/481250 -
        Glin (1/3) - Glin truncatedSixthLowerSigma - 8*J9 - ε)*
          wuSingularSeries N*N/log N^(2 : ℕ) ≤
      3*(sieveCount N 1 N ((N : ℝ)^truncatedSixthLowerAlpha) : ℝ) +
        (sieveCount N 1 N ((N : ℝ)^truncatedSixthLowerBeta) : ℝ) +
        (fifthPairCount N : ℝ) +
        (truncatedSixthMass N ((N : ℝ)^truncatedSixthLowerAlpha)
          ((N : ℝ)^truncatedSixthLowerBeta) ((N : ℝ)^truncatedSixthLowerSigma)
          ((N : ℝ)^truncatedSixthLowerLambda) : ℝ) -
        (U N (1/3) : ℝ) - (U N truncatedSixthLowerSigma : ℝ) -
        (variableS3Main N ((N : ℝ)^truncatedSixthLowerBeta)
          ((N : ℝ)^truncatedSixthLowerSigma) : ℝ) := by
  obtain ⟨T6, _hT6, h6⟩ := first_six_actual_lower (half_pos hε)
  obtain ⟨T9, hT9, h9⟩ := original_ninth_upper (half_pos hε)
  refine ⟨max T6 T9, hT9.trans (le_max_right _ _), ?_⟩
  intro N hN he
  have hs := h6 N ((le_max_left _ _).trans hN) he
  have hn := h9 N ((le_max_right _ _).trans hN) he
  calc
    _ = (24*wuLowerCoefficient (1/(2*truncatedSixthLowerAlpha)) +
        8*wuLowerCoefficient (1/(2*truncatedSixthLowerBeta)) + fifthPairFlin +
        truncatedSixthLowerF6lin + 47/481250 -
        Glin (1/3) - Glin truncatedSixthLowerSigma - ε/2)*
          wuSingularSeries N*N/log N^(2 : ℕ) -
        (8*J9 + ε/2)*wuSingularSeries N*N/log N^(2 : ℕ) := by ring
    _ ≤ _ := sub_le_sub hs hn

/-- Literal integer rearrangement of the actual finite expression. In particular,
the original Q is `fun D y => sieveCount N D N y`, on unchanged quadruples.
Only the full positive sixth mass is replaced by its already defined retained mass. -/
theorem truncated_expression_literal (N : ℕ) (z w u v V : ℝ) :
    truncatedSixthExpression N z w u v V =
      3*sieveCount N 1 N z + sieveCount N 1 N w +
        (∑ c ∈ primeWindow N z w, ∑ b ∈ primeWindow N z (c : ℝ),
          sieveCount N (b*c) N z) + truncatedSixthMass N z w u V -
        (∑ p ∈ primeWindow N z v, sieveCount N p N z) -
        (∑ p ∈ primeWindow N z u, sieveCount N p N z) -
        variableS3Main N w u - 2*lowerS2 N w u - lowerS3 N z v -
        (∑ t ∈ s3DistinctQuadruples N (orderedTriples (primeWindow N z w)),
          sieveCount N (t.1*t.2.1*t.2.2.1*t.2.2.2) N (t.2.1 : ℝ)) -
        ∑ t ∈ s3Upsilon11Range N z w V,
          sieveCount N (t.1*t.2.1*t.2.2.1*t.2.2.2) N (t.2.1 : ℝ) := by
  unfold truncatedSixthExpression fourModulusQuotientEleven finiteElevenExpression
  rw [truncatedSixth_full_eq_original]
  unfold lowerS2 lowerS3 variableS3Main
  ring

/-- Real cast of the literal fixed expression. All four remaining negative counts
are displayed on their original domains, without de-duplication or estimates. -/
theorem fixed_expression_literal (N : ℕ) :
    let z := (N : ℝ)^truncatedSixthLowerAlpha
    let w := (N : ℝ)^truncatedSixthLowerBeta
    let u := (N : ℝ)^truncatedSixthLowerSigma
    let v := (N : ℝ)^(1/3 : ℝ)
    let V := (N : ℝ)^truncatedSixthLowerLambda
    (truncatedSixthFixedExpression N : ℝ) =
      3*(sieveCount N 1 N z : ℝ) + (sieveCount N 1 N w : ℝ) +
        (fifthPairCount N : ℝ) + (truncatedSixthMass N z w u V : ℝ) -
        (U N (1/3) : ℝ) - (U N truncatedSixthLowerSigma : ℝ) -
        (variableS3Main N w u : ℝ) - 2*(lowerS2 N w u : ℝ) -
        (lowerS3 N z v : ℝ) -
        ((∑ t ∈ s3DistinctQuadruples N (orderedTriples (primeWindow N z w)),
          sieveCount N (t.1*t.2.1*t.2.2.1*t.2.2.2) N (t.2.1 : ℝ)) : ℤ) -
        ((∑ t ∈ s3Upsilon11Range N z w V,
          sieveCount N (t.1*t.2.1*t.2.2.1*t.2.2.2) N (t.2.1 : ℝ)) : ℤ) := by
  dsimp only
  have h := congrArg (fun a : ℤ => (a : ℝ))
    (truncated_expression_literal N ((N : ℝ)^truncatedSixthLowerAlpha)
      ((N : ℝ)^truncatedSixthLowerBeta) ((N : ℝ)^truncatedSixthLowerSigma)
      ((N : ℝ)^(1/3 : ℝ)) ((N : ℝ)^truncatedSixthLowerLambda))
  simpa only [truncatedSixthFixedExpression, truncatedSixthLowerAlpha,
    truncatedSixthLowerBeta, truncatedSixthLowerSigma, truncatedSixthLowerLambda,
    fifthPairCount, U, Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_ofNat,
    Int.cast_sum] using h

/-- Actual lower bound on the original fixed truncated-sixth expression.
Residual terms 7, 8, 10 and 11 remain actual counts with weights 2, 1, 1, 1.
The only input is a positive error; this is not a positivity theorem. -/
theorem truncated_fixed_actual_lower {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      let z := (N : ℝ)^truncatedSixthLowerAlpha
      let w := (N : ℝ)^truncatedSixthLowerBeta
      let u := (N : ℝ)^truncatedSixthLowerSigma
      let v := (N : ℝ)^(1/3 : ℝ)
      let V := (N : ℝ)^truncatedSixthLowerLambda
      (24*wuLowerCoefficient (1/(2*truncatedSixthLowerAlpha)) +
        8*wuLowerCoefficient (1/(2*truncatedSixthLowerBeta)) + fifthPairFlin +
        truncatedSixthLowerF6lin + 47/481250 -
        Glin (1/3) - Glin truncatedSixthLowerSigma - 8*J9 - ε)*
          wuSingularSeries N*N/log N^(2 : ℕ) -
        2*(lowerS2 N w u : ℝ) - (lowerS3 N z v : ℝ) -
        ((∑ t ∈ s3DistinctQuadruples N (orderedTriples (primeWindow N z w)),
          sieveCount N (t.1*t.2.1*t.2.2.1*t.2.2.2) N (t.2.1 : ℝ)) : ℤ) -
        ((∑ t ∈ s3Upsilon11Range N z w V,
          sieveCount N (t.1*t.2.1*t.2.2.1*t.2.2.2) N (t.2.1 : ℝ)) : ℤ) ≤
      (truncatedSixthFixedExpression N : ℝ) := by
  obtain ⟨T, hT, h⟩ := first_six_sub_ninth_actual_lower hε
  refine ⟨T, hT, ?_⟩
  intro N hN he
  dsimp only
  rw [fixed_expression_literal]
  exact sub_le_sub_right (sub_le_sub_right (sub_le_sub_right
    (sub_le_sub_right (h N hN he) _) _) _) _

end Wu2008DoubleSieve.TruncatedElevenSignedLower
