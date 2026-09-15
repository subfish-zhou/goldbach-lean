import MiddleWindowGain
import SecondCrossCount

namespace Wu2008DoubleSieve.Phase12
open Real HighSixPhase9 SingleUpperHIntegral
noncomputable section

/-- The feedback ratio and delta loss are unchanged; only raw integral mass is added. -/
def g12 : ℝ := Cfull*sourceP/(1-Phase10.rhoLog)
def penalty12 : ℝ := Cfull*envelopeE/(1-Phase10.rhoLog)

theorem g12_pos : 0 < g12 := by
  apply div_pos (mul_pos Cfull_pos (by norm_num [sourceP]))
    (sub_pos.mpr Phase10.rhoLog_bounds.2)

theorem penalty12_pos : 0 < penalty12 := by
  apply div_pos (mul_pos Cfull_pos (by norm_num [envelopeE]))
    (sub_pos.mpr Phase10.rhoLog_bounds.2)

theorem gain12_with_penalty {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100) :
    g12-penalty δ*penalty12 ≤ gainH34 δ/4 := by
  have hi := (mul_le_mul_of_nonneg_left (Phase10.amplitude_log_closed hδ hδhi)
    Cfull_pos.le).trans (actual_low_H_full_lower hδ hδhi)
  have he : g12-penalty δ*penalty12 =
      Cfull*((sourceP-penalty δ*envelopeE)/(1-Phase10.rhoLog)) := by
    unfold g12 penalty12
    ring
  rwa [he]

theorem gain12_linear_error {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100) :
    g12-((100/49)*penalty12)*δ ≤ gainH34 δ/4 := by
  have hp := mul_le_mul_of_nonneg_right (ParentPhase9HalfWeight.penalty_le hδ hδhi)
    penalty12_pos.le
  have hi := gain12_with_penalty hδ hδhi
  nlinarith only [hp,hi]

theorem g12_strict : Phase11.g11 < g12 := by
  unfold Phase11.g11 g12
  apply (div_lt_div_iff_of_pos_right (sub_pos.mpr Phase10.rhoLog_bounds.2)).2
  apply mul_lt_mul_of_pos_right _ (by norm_num [sourceP])
  unfold Cfull Phase11.Ctotal
  linarith only [Cmid_pos]

/-- The new unconditional raw-integral producer is actually supplied here. -/
theorem middle_window_actual_count :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (GCurvatureChord.exactQuarter+
        firstFunctionalGainPsiOne HighSix.s HighSix.S*HighSix.primeIntegral 0+g12)*
        wuSingularSeries N*N/log N^(2 : ℕ) ≤
          ((MathlibNt.Wu2008DoubleSieve.wuPrimeComplements N).card : ℝ) :=
  Phase10.same_mother_exact_payment g12 ((100/49)*penalty12)
    (mul_pos (by norm_num) penalty12_pos)
    (fun _ hδ hδhi => gain12_linear_error hδ hδhi)

/-- Ordinary P2 includes complement one and excludes zero; no prime-factor ratio filter.
Both spellings share the same threshold. -/
theorem middle_window_ordinary_P2_same_threshold :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ((GCurvatureChord.exactQuarter+
          (3629895479136046171/11308652260919376406875 : ℝ)+g12)*
        wuSingularSeries N*N/log N^(2 : ℕ) ≤
          ((MathlibNt.Wu2008DoubleSieve.wuPrimeComplements N).card : ℝ)) ∧
      ((GCurvatureChord.exactQuarter+
          (3629895479136046171/11308652260919376406875 : ℝ)+g12)*
        wuSingularSeries N*N/log N^(2 : ℕ) ≤
          ((Finset.filter (fun p => Nat.Prime p ∧ 0 < N-p ∧
            ArithmeticFunction.cardFactors (N-p) ≤ 2) (Finset.range (N+1))).card : ℝ)) := by
  obtain ⟨T,hT,h⟩ := middle_window_actual_count
  refine ⟨T,hT,?_⟩
  intro N hN he
  have hs := (HighSixPhase6.original_scale_positive (show 512 ≤ N by omega)).le
  have hc : GCurvatureChord.exactQuarter+
      (3629895479136046171/11308652260919376406875 : ℝ)+g12 ≤
      GCurvatureChord.exactQuarter+
      firstFunctionalGainPsiOne HighSix.s HighSix.S*HighSix.primeIntegral 0+g12 := by
    linarith only [HighSixPhase6.exact_local_gain_lower]
  have hp := mul_le_mul_of_nonneg_right hc hs
  have hn := h N hN he
  have hfinal : (GCurvatureChord.exactQuarter+
      (3629895479136046171/11308652260919376406875 : ℝ)+g12)*
      wuSingularSeries N*N/log N^(2 : ℕ) ≤
      ((MathlibNt.Wu2008DoubleSieve.wuPrimeComplements N).card : ℝ) := by
    calc
      _ = (GCurvatureChord.exactQuarter+
        (3629895479136046171/11308652260919376406875 : ℝ)+g12)*
        (wuSingularSeries N*N/log N^(2 : ℕ)) := by ring
      _ ≤ (GCurvatureChord.exactQuarter+
        firstFunctionalGainPsiOne HighSix.s HighSix.S*HighSix.primeIntegral 0+g12)*
        (wuSingularSeries N*N/log N^(2 : ℕ)) := hp
      _ = (GCurvatureChord.exactQuarter+
        firstFunctionalGainPsiOne HighSix.s HighSix.S*HighSix.primeIntegral 0+g12)*
        wuSingularSeries N*N/log N^(2 : ℕ) := by ring
      _ ≤ _ := hn
  exact ⟨hfinal,hfinal⟩

theorem ordinary_coefficient_strict :
    GCurvatureChord.exactQuarter+(3629895479136046171/11308652260919376406875 : ℝ)+
      Phase11.g11 <
    GCurvatureChord.exactQuarter+(3629895479136046171/11308652260919376406875 : ℝ)+g12 := by
  linarith only [g12_strict]

end
end Wu2008DoubleSieve.Phase12
