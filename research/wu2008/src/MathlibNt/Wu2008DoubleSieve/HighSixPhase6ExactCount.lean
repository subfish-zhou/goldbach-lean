import MathlibNt.Wu2008DoubleSieve.HighSixPhase6PrimeLower
import MathlibNt.Wu2008DoubleSieve.HighSixPhase5Positive
import MathlibNt.Wu2008DoubleSieve.HighSixPsiLimitCount

namespace Wu2008DoubleSieve.HighSixPhase6
open Real

/-- Natural product of the two proved lower bounds, in ordinary P2 units. -/
theorem exact_local_gain_lower :
    (3629895479136046171/11308652260919376406875 : ℝ) ≤
      firstFunctionalGainPsiOne HighSix.s HighSix.S*HighSix.primeIntegral 0 := by
  have hp : (3629895479136046171/1363514967405501300000 : ℝ) ≤
      firstFunctionalGainPsiOne HighSix.s HighSix.S := by
    simpa only [HighSix.s,HighSix.S] using HighSixPhase5.psi_lower
  have h := mul_le_mul hp primeIntegral_zero_lower (by norm_num)
    (le_trans (by norm_num) hp)
  norm_num at h ⊢
  exact h

/-- The resulting coefficient is strictly above the unmodified exactQuarter. -/
theorem exact_coefficient_strict :
    GCurvatureChord.exactQuarter < GCurvatureChord.exactQuarter+
      (3629895479136046171/11308652260919376406875 : ℝ) := by
  linarith

/-- Positivity of the original scale; no independent counting estimate is used. -/
theorem original_scale_positive {N : ℕ} (hN : 512 ≤ N) :
    0 < wuSingularSeries N*N/log N^(2 : ℕ) := by
  have hs := wuSingularSeries_pos N (by omega : 0 < N)
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hl : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  positivity

/-- The common threshold is chosen first, then every even N. The original
same-K curvature theorem pays the lower bound directly into literal ordinary P2.
The complement 1 is retained and 0 is excluded by the literal filter. -/
theorem exact_gain_actual_count_same_threshold :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ((GCurvatureChord.exactQuarter+
          (3629895479136046171/11308652260919376406875 : ℝ))*
        wuSingularSeries N*N/log N^(2 : ℕ) ≤
          ((MathlibNt.Wu2008DoubleSieve.wuPrimeComplements N).card : ℝ)) ∧
      ((GCurvatureChord.exactQuarter+
          (3629895479136046171/11308652260919376406875 : ℝ))*
        wuSingularSeries N*N/log N^(2 : ℕ) ≤
          ((Finset.filter (fun p => Nat.Prime p ∧ 0 < N-p ∧
            ArithmeticFunction.cardFactors (N-p) ≤ 2) (Finset.range (N+1))).card : ℝ)) := by
  obtain ⟨T,hT,h⟩ := HighSixDeltaLimit.curvature_actual_count_same_threshold
  refine ⟨T,hT,?_⟩
  intro N hN he
  have hs := (original_scale_positive (show 512 ≤ N by omega)).le
  have hpay := mul_le_mul_of_nonneg_right
    (add_le_add_right exact_local_gain_lower GCurvatureChord.exactQuarter) hs
  have hn := h N hN he
  have hc : (GCurvatureChord.exactQuarter+
      (3629895479136046171/11308652260919376406875 : ℝ))*
      wuSingularSeries N*N/log N^(2 : ℕ) ≤
      ((MathlibNt.Wu2008DoubleSieve.wuPrimeComplements N).card : ℝ) := by
    calc
      _ = (GCurvatureChord.exactQuarter+
        (3629895479136046171/11308652260919376406875 : ℝ))*
        (wuSingularSeries N*N/log N^(2 : ℕ)) := by ring
      _ ≤ (GCurvatureChord.exactQuarter+
        firstFunctionalGainPsiOne HighSix.s HighSix.S*HighSix.primeIntegral 0)*
        (wuSingularSeries N*N/log N^(2 : ℕ)) := hpay
      _ = (GCurvatureChord.exactQuarter+
        firstFunctionalGainPsiOne HighSix.s HighSix.S*HighSix.primeIntegral 0)*
        wuSingularSeries N*N/log N^(2 : ℕ) := by ring
      _ ≤ _ := hn.2.1
  exact ⟨hc,hc⟩

end Wu2008DoubleSieve.HighSixPhase6
