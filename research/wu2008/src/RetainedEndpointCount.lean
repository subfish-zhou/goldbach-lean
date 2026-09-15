import RetainedEndpointFeedback
import MiddleWindowCount

namespace Wu2008DoubleSieve.Phase13
open Real HighSixPhase9 SingleUpperHIntegral
open Phase12 (Cfull Cfull_pos actual_low_H_full_lower)
noncomputable section

/-- The original Cfull is unchanged; the new feedback improves the same raw integral. -/
def g13 : ℝ := Cfull*sourceP/(1-rhoEndpoint)
def penalty13 : ℝ := Cfull*envelopeE/(1-rhoEndpoint)

theorem g13_pos : 0 < g13 := by
  apply div_pos (mul_pos Cfull_pos (by norm_num [sourceP]))
    (sub_pos.mpr rhoEndpoint_bounds.2)

theorem penalty13_pos : 0 < penalty13 := by
  apply div_pos (mul_pos Cfull_pos (by norm_num [envelopeE]))
    (sub_pos.mpr rhoEndpoint_bounds.2)

theorem gain13_with_penalty {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100) :
    g13-penalty δ*penalty13 ≤ gainH34 δ/4 := by
  have hi := (mul_le_mul_of_nonneg_left (amplitude_endpoint_closed hδ hδhi)
    Cfull_pos.le).trans (actual_low_H_full_lower hδ hδhi)
  have he : g13-penalty δ*penalty13 =
      Cfull*((sourceP-penalty δ*envelopeE)/(1-rhoEndpoint)) := by
    unfold g13 penalty13
    ring
  rwa [he]

theorem gain13_linear_error {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100) :
    g13-((100/49)*penalty13)*δ ≤ gainH34 δ/4 := by
  have hp := mul_le_mul_of_nonneg_right (ParentPhase9HalfWeight.penalty_le hδ hδhi)
    penalty13_pos.le
  have hi := gain13_with_penalty hδ hδhi
  nlinarith only [hp,hi]

theorem g13_strict : Phase12.g12 < g13 := by
  unfold Phase12.g12 g13
  exact div_lt_div_of_pos_left (mul_pos Cfull_pos (by norm_num [sourceP]))
    (sub_pos.mpr rhoEndpoint_bounds.2) (by linarith only [rhoEndpoint_strict])

/-- The new unconditional raw-integral producer is actually supplied here. -/
theorem retained_endpoint_actual_count :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (GCurvatureChord.exactQuarter+
        firstFunctionalGainPsiOne HighSix.s HighSix.S*HighSix.primeIntegral 0+g13)*
        wuSingularSeries N*N/log N^(2 : ℕ) ≤
          ((MathlibNt.Wu2008DoubleSieve.wuPrimeComplements N).card : ℝ) :=
  Phase10.same_mother_exact_payment g13 ((100/49)*penalty13)
    (mul_pos (by norm_num) penalty13_pos)
    (fun _ hδ hδhi => gain13_linear_error hδ hδhi)

/-- Ordinary P2 includes complement one and excludes zero; no prime-factor ratio filter.
Both spellings share the same threshold. -/
theorem retained_endpoint_ordinary_P2_same_threshold :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ((GCurvatureChord.exactQuarter+
          (3629895479136046171/11308652260919376406875 : ℝ)+g13)*
        wuSingularSeries N*N/log N^(2 : ℕ) ≤
          ((MathlibNt.Wu2008DoubleSieve.wuPrimeComplements N).card : ℝ)) ∧
      ((GCurvatureChord.exactQuarter+
          (3629895479136046171/11308652260919376406875 : ℝ)+g13)*
        wuSingularSeries N*N/log N^(2 : ℕ) ≤
          ((Finset.filter (fun p => Nat.Prime p ∧ 0 < N-p ∧
            ArithmeticFunction.cardFactors (N-p) ≤ 2) (Finset.range (N+1))).card : ℝ)) := by
  obtain ⟨T,hT,h⟩ := retained_endpoint_actual_count
  refine ⟨T,hT,?_⟩
  intro N hN he
  have hs := (HighSixPhase6.original_scale_positive (show 512 ≤ N by omega)).le
  have hc : GCurvatureChord.exactQuarter+
      (3629895479136046171/11308652260919376406875 : ℝ)+g13 ≤
      GCurvatureChord.exactQuarter+
      firstFunctionalGainPsiOne HighSix.s HighSix.S*HighSix.primeIntegral 0+g13 := by
    linarith only [HighSixPhase6.exact_local_gain_lower]
  have hp := mul_le_mul_of_nonneg_right hc hs
  have hn := h N hN he
  have hfinal : (GCurvatureChord.exactQuarter+
      (3629895479136046171/11308652260919376406875 : ℝ)+g13)*
      wuSingularSeries N*N/log N^(2 : ℕ) ≤
      ((MathlibNt.Wu2008DoubleSieve.wuPrimeComplements N).card : ℝ) := by
    calc
      _ = (GCurvatureChord.exactQuarter+
        (3629895479136046171/11308652260919376406875 : ℝ)+g13)*
        (wuSingularSeries N*N/log N^(2 : ℕ)) := by ring
      _ ≤ (GCurvatureChord.exactQuarter+
        firstFunctionalGainPsiOne HighSix.s HighSix.S*HighSix.primeIntegral 0+g13)*
        (wuSingularSeries N*N/log N^(2 : ℕ)) := hp
      _ = (GCurvatureChord.exactQuarter+
        firstFunctionalGainPsiOne HighSix.s HighSix.S*HighSix.primeIntegral 0+g13)*
        wuSingularSeries N*N/log N^(2 : ℕ) := by ring
      _ ≤ _ := hn
  exact ⟨hfinal,hfinal⟩

theorem ordinary_coefficient_strict :
    GCurvatureChord.exactQuarter+(3629895479136046171/11308652260919376406875 : ℝ)+
      Phase12.g12 <
    GCurvatureChord.exactQuarter+(3629895479136046171/11308652260919376406875 : ℝ)+g13 := by
  linarith only [g13_strict]

end
end Wu2008DoubleSieve.Phase13
