import FullPolynomialWindowGain
import RetainedEndpointCount

namespace Wu2008DoubleSieve.Phase14
open Real HighSixPhase9 SingleUpperHIntegral
open Phase13 (rhoEndpoint rhoEndpoint_bounds amplitude_endpoint_closed)
noncomputable section

/-- The feedback endpoint is unchanged; the full polynomial improves the raw integral. -/
def g14 : ℝ := C14*sourceP/(1-rhoEndpoint)
def penalty14 : ℝ := C14*envelopeE/(1-rhoEndpoint)

theorem g14_pos : 0 < g14 := by
  apply div_pos (mul_pos C14_pos (by norm_num [sourceP]))
    (sub_pos.mpr rhoEndpoint_bounds.2)

theorem penalty14_pos : 0 < penalty14 := by
  apply div_pos (mul_pos C14_pos (by norm_num [envelopeE]))
    (sub_pos.mpr rhoEndpoint_bounds.2)

theorem gain14_with_penalty {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100) :
    g14-penalty δ*penalty14 ≤ gainH34 δ/4 := by
  have hi := (mul_le_mul_of_nonneg_left (amplitude_endpoint_closed hδ hδhi)
    C14_pos.le).trans (actual_low_H_polynomial_lower hδ hδhi)
  have he : g14-penalty δ*penalty14 =
      C14*((sourceP-penalty δ*envelopeE)/(1-rhoEndpoint)) := by
    unfold g14 penalty14
    ring
  rwa [he]

theorem gain14_linear_error {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100) :
    g14-((100/49)*penalty14)*δ ≤ gainH34 δ/4 := by
  have hp := mul_le_mul_of_nonneg_right (ParentPhase9HalfWeight.penalty_le hδ hδhi)
    penalty14_pos.le
  have hi := gain14_with_penalty hδ hδhi
  nlinarith only [hp,hi]

theorem g14_strict : Phase13.g13 < g14 := by
  unfold Phase13.g13 g14
  apply (div_lt_div_iff_of_pos_right (sub_pos.mpr rhoEndpoint_bounds.2)).2
  exact mul_lt_mul_of_pos_right (by unfold C14; linarith only [deltaC_pos])
    (by norm_num [sourceP])

/-- The new unconditional raw-integral producer is actually supplied here. -/
theorem full_polynomial_actual_count :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (GCurvatureChord.exactQuarter+
        firstFunctionalGainPsiOne HighSix.s HighSix.S*HighSix.primeIntegral 0+g14)*
        wuSingularSeries N*N/log N^(2 : ℕ) ≤
          ((MathlibNt.Wu2008DoubleSieve.wuPrimeComplements N).card : ℝ) :=
  Phase10.same_mother_exact_payment g14 ((100/49)*penalty14)
    (mul_pos (by norm_num) penalty14_pos)
    (fun _ hδ hδhi => gain14_linear_error hδ hδhi)

/-- Ordinary P2 includes complement one and excludes zero; no prime-factor ratio filter.
Both spellings share the same threshold. -/
theorem full_polynomial_ordinary_P2_same_threshold :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ((GCurvatureChord.exactQuarter+
          (3629895479136046171/11308652260919376406875 : ℝ)+g14)*
        wuSingularSeries N*N/log N^(2 : ℕ) ≤
          ((MathlibNt.Wu2008DoubleSieve.wuPrimeComplements N).card : ℝ)) ∧
      ((GCurvatureChord.exactQuarter+
          (3629895479136046171/11308652260919376406875 : ℝ)+g14)*
        wuSingularSeries N*N/log N^(2 : ℕ) ≤
          ((Finset.filter (fun p => Nat.Prime p ∧ 0 < N-p ∧
            ArithmeticFunction.cardFactors (N-p) ≤ 2) (Finset.range (N+1))).card : ℝ)) := by
  obtain ⟨T,hT,h⟩ := full_polynomial_actual_count
  refine ⟨T,hT,?_⟩
  intro N hN he
  have hs := (HighSixPhase6.original_scale_positive (show 512 ≤ N by omega)).le
  have hc : GCurvatureChord.exactQuarter+
      (3629895479136046171/11308652260919376406875 : ℝ)+g14 ≤
      GCurvatureChord.exactQuarter+
      firstFunctionalGainPsiOne HighSix.s HighSix.S*HighSix.primeIntegral 0+g14 := by
    linarith only [HighSixPhase6.exact_local_gain_lower]
  have hp := mul_le_mul_of_nonneg_right hc hs
  have hn := h N hN he
  have hfinal : (GCurvatureChord.exactQuarter+
      (3629895479136046171/11308652260919376406875 : ℝ)+g14)*
      wuSingularSeries N*N/log N^(2 : ℕ) ≤
      ((MathlibNt.Wu2008DoubleSieve.wuPrimeComplements N).card : ℝ) := by
    calc
      _ = (GCurvatureChord.exactQuarter+
        (3629895479136046171/11308652260919376406875 : ℝ)+g14)*
        (wuSingularSeries N*N/log N^(2 : ℕ)) := by ring
      _ ≤ (GCurvatureChord.exactQuarter+
        firstFunctionalGainPsiOne HighSix.s HighSix.S*HighSix.primeIntegral 0+g14)*
        (wuSingularSeries N*N/log N^(2 : ℕ)) := hp
      _ = (GCurvatureChord.exactQuarter+
        firstFunctionalGainPsiOne HighSix.s HighSix.S*HighSix.primeIntegral 0+g14)*
        wuSingularSeries N*N/log N^(2 : ℕ) := by ring
      _ ≤ _ := hn
  exact ⟨hfinal,hfinal⟩

theorem ordinary_coefficient_strict :
    GCurvatureChord.exactQuarter+(3629895479136046171/11308652260919376406875 : ℝ)+
      Phase13.g13 <
    GCurvatureChord.exactQuarter+(3629895479136046171/11308652260919376406875 : ℝ)+g14 := by
  linarith only [g14_strict]

end
end Wu2008DoubleSieve.Phase14
