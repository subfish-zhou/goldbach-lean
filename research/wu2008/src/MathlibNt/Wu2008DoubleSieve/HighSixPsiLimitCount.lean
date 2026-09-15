import MathlibNt.Wu2008DoubleSieve.HighSixPsiDeltaLimit
import MathlibNt.Wu2008DoubleSieve.GCurvatureCount

namespace Wu2008DoubleSieve.HighSixDeltaLimit
open Real

/-- The witness order is epsilon, positive delta, T, then every even N. -/
theorem actual_count_delta_then_threshold {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1/100 ∧
      limitCoefficient-ε/2 < HighSixPsiMother.psiCoefficient δ ∧
      ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
        (limitCoefficient-ε)*wuSingularSeries N*N/log N^(2 : ℕ) ≤
          4*((MathlibNt.Wu2008DoubleSieve.wuPrimeComplements N).card : ℝ) := by
  obtain ⟨δ, hδ, hδhi, hcoef⟩ := choose_delta (half_pos hε)
  obtain ⟨T, hT, hcount⟩ := HighSixPsiMother.actual_count_lower hδ hδhi (half_pos hε)
  refine ⟨δ, hδ, hδhi, hcoef, T, hT, ?_⟩
  intro N hN he
  have hs : 0 ≤ wuSingularSeries N*N/log N^(2 : ℕ) := by
    have := (wuSingularSeries_pos N (by omega : 0 < N)).le
    positivity
  have hc := mul_le_mul_of_nonneg_right
    (show limitCoefficient-ε ≤ HighSixPsiMother.psiCoefficient δ-ε/2 by linarith only [hcoef]) hs
  have hm := hcount N hN he
  calc
    _ = (limitCoefficient-ε)*(wuSingularSeries N*N/log N^(2 : ℕ)) := by ring
    _ ≤ (HighSixPsiMother.psiCoefficient δ-ε/2)*(wuSingularSeries N*N/log N^(2 : ℕ)) := hc
    _ = (HighSixPsiMother.psiCoefficient δ-ε/2)*wuSingularSeries N*N/log N^(2 : ℕ) := by ring
    _ ≤ _ := hm

/-- Genuine P2 count with original complete K plus the original local PsiOne integral. -/
theorem actual_count_lower {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (TruncatedElevenClassicalCountLower.classicalCoefficient+
        4*firstFunctionalGainPsiOne HighSix.s HighSix.S*HighSix.primeIntegral 0-ε)*
        wuSingularSeries N*N/log N^(2 : ℕ) ≤
          4*((MathlibNt.Wu2008DoubleSieve.wuPrimeComplements N).card : ℝ) := by
  obtain ⟨δ, _, _, _, T, hT, h⟩ := actual_count_delta_then_threshold hε
  exact ⟨T, hT, h⟩

/-- Actual division by four; epsilon here is in ordinary P2 units. -/
theorem actual_count_quarter {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (TruncatedElevenClassicalCountLower.classicalCoefficient/4+
        firstFunctionalGainPsiOne HighSix.s HighSix.S*HighSix.primeIntegral 0-ε)*
        wuSingularSeries N*N/log N^(2 : ℕ) ≤
          ((MathlibNt.Wu2008DoubleSieve.wuPrimeComplements N).card : ℝ) := by
  obtain ⟨T, hT, h⟩ := actual_count_lower (mul_pos (by norm_num : (0 : ℝ) < 4) hε)
  refine ⟨T, hT, ?_⟩
  intro N hN he
  have hn := h N hN he
  have hid : (TruncatedElevenClassicalCountLower.classicalCoefficient/4+
      firstFunctionalGainPsiOne HighSix.s HighSix.S*HighSix.primeIntegral 0-ε)*
      wuSingularSeries N*N/log N^(2 : ℕ) =
      ((TruncatedElevenClassicalCountLower.classicalCoefficient+
        4*firstFunctionalGainPsiOne HighSix.s HighSix.S*HighSix.primeIntegral 0-4*ε)*
        wuSingularSeries N*N/log N^(2 : ℕ))/4 := by ring
  rw [hid]
  exact (div_le_iff₀ (by norm_num : (0 : ℝ) < 4)).2 (by linarith only [hn])

/-- Compare the SAME K before invoking a count bound. No two count bounds are added. -/
theorem curvature_coefficient_strict :
    GCurvatureChord.newBalance+localGainOne < limitCoefficient := by
  unfold limitCoefficient
  linarith only [GCurvatureChord.complete_coefficient_gt_newBalance]

/-- The strict classical coefficient reserve pays all epsilon without rounding. -/
theorem curvature_actual_count_same_threshold :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ((GCurvatureChord.newBalance+
          4*firstFunctionalGainPsiOne HighSix.s HighSix.S*HighSix.primeIntegral 0)*
        wuSingularSeries N*N/log N^(2 : ℕ) ≤
          4*((MathlibNt.Wu2008DoubleSieve.wuPrimeComplements N).card : ℝ)) ∧
      ((GCurvatureChord.exactQuarter+
          firstFunctionalGainPsiOne HighSix.s HighSix.S*HighSix.primeIntegral 0)*
        wuSingularSeries N*N/log N^(2 : ℕ) ≤
          ((MathlibNt.Wu2008DoubleSieve.wuPrimeComplements N).card : ℝ)) ∧
      ((GCurvatureChord.exactQuarter+
          firstFunctionalGainPsiOne HighSix.s HighSix.S*HighSix.primeIntegral 0)*
        wuSingularSeries N*N/log N^(2 : ℕ) ≤
          ((Finset.filter (fun p => Nat.Prime p ∧ 0 < N-p ∧
            ArithmeticFunction.cardFactors (N-p) ≤ 2) (Finset.range (N+1))).card : ℝ)) := by
  have he : 0 < limitCoefficient-(GCurvatureChord.newBalance+localGainOne) :=
    sub_pos.mpr curvature_coefficient_strict
  obtain ⟨T, hT, h⟩ := actual_count_lower he
  refine ⟨T, hT, ?_⟩
  intro N hN hEven
  have hn := h N hN hEven
  change (limitCoefficient-(limitCoefficient-(GCurvatureChord.newBalance+localGainOne)))*
    wuSingularSeries N*N/log N^(2 : ℕ) ≤
      4*((MathlibNt.Wu2008DoubleSieve.wuPrimeComplements N).card : ℝ) at hn
  rw [sub_sub_cancel] at hn
  have hq : (GCurvatureChord.newBalance/4+
      firstFunctionalGainPsiOne HighSix.s HighSix.S*HighSix.primeIntegral 0)*
      wuSingularSeries N*N/log N^(2 : ℕ) ≤
        ((MathlibNt.Wu2008DoubleSieve.wuPrimeComplements N).card : ℝ) := by
    have hid : (GCurvatureChord.newBalance/4+
        firstFunctionalGainPsiOne HighSix.s HighSix.S*HighSix.primeIntegral 0)*
        wuSingularSeries N*N/log N^(2 : ℕ) =
        ((GCurvatureChord.newBalance+localGainOne)*wuSingularSeries N*N/log N^(2 : ℕ))/4 := by
      unfold localGainOne
      ring
    rw [hid]
    exact (div_le_iff₀ (by norm_num : (0 : ℝ) < 4)).2 (by linarith only [hn])
  rw [GCurvatureChord.quarter_eq_exact] at hq
  exact ⟨hn, hq, hq⟩

end Wu2008DoubleSieve.HighSixDeltaLimit
