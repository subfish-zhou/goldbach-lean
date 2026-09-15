import KernelCurvatureWindowGain
import FullPolynomialWindowCount

namespace Wu2008DoubleSieve.Phase15
open Real HighSixPhase9 SingleUpperHIntegral
open Phase13 (rhoEndpoint rhoEndpoint_bounds amplitude_endpoint_closed)
noncomputable section

/-- The feedback endpoint is unchanged; the kernel curvature improves the raw integral. -/
def g15 : ℝ := C15*sourceP/(1-rhoEndpoint)
def penalty15 : ℝ := C15*envelopeE/(1-rhoEndpoint)

theorem g15_pos : 0 < g15 := by
  apply div_pos (mul_pos C15_pos (by norm_num [sourceP]))
    (sub_pos.mpr rhoEndpoint_bounds.2)

theorem penalty15_pos : 0 < penalty15 := by
  apply div_pos (mul_pos C15_pos (by norm_num [envelopeE]))
    (sub_pos.mpr rhoEndpoint_bounds.2)

theorem gain15_with_penalty {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100) :
    g15-penalty δ*penalty15 ≤ gainH34 δ/4 := by
  have hi := (mul_le_mul_of_nonneg_left (amplitude_endpoint_closed hδ hδhi)
    C15_pos.le).trans (actual_low_H_curvature_lower hδ hδhi)
  have he : g15-penalty δ*penalty15 =
      C15*((sourceP-penalty δ*envelopeE)/(1-rhoEndpoint)) := by
    unfold g15 penalty15
    ring
  rwa [he]

theorem gain15_linear_error {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100) :
    g15-((100/49)*penalty15)*δ ≤ gainH34 δ/4 := by
  have hp := mul_le_mul_of_nonneg_right (ParentPhase9HalfWeight.penalty_le hδ hδhi)
    penalty15_pos.le
  have hi := gain15_with_penalty hδ hδhi
  nlinarith only [hp,hi]

theorem g15_strict : Phase14.g14 < g15 := by
  unfold Phase14.g14 g15
  apply (div_lt_div_iff_of_pos_right (sub_pos.mpr rhoEndpoint_bounds.2)).2
  exact mul_lt_mul_of_pos_right (by unfold C15; linarith only [deltaKernel_pos])
    (by norm_num [sourceP])

/-- The new unconditional raw-integral producer is actually supplied here. -/
theorem kernel_curvature_actual_count :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (GCurvatureChord.exactQuarter+
        firstFunctionalGainPsiOne HighSix.s HighSix.S*HighSix.primeIntegral 0+g15)*
        wuSingularSeries N*N/log N^(2 : ℕ) ≤
          ((MathlibNt.Wu2008DoubleSieve.wuPrimeComplements N).card : ℝ) :=
  Phase10.same_mother_exact_payment g15 ((100/49)*penalty15)
    (mul_pos (by norm_num) penalty15_pos)
    (fun _ hδ hδhi => gain15_linear_error hδ hδhi)

/-- Ordinary P2 includes complement one and excludes zero; no prime-factor ratio filter.
Both spellings share the same threshold. -/
theorem kernel_curvature_ordinary_P2_same_threshold :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ((GCurvatureChord.exactQuarter+
          (3629895479136046171/11308652260919376406875 : ℝ)+g15)*
        wuSingularSeries N*N/log N^(2 : ℕ) ≤
          ((MathlibNt.Wu2008DoubleSieve.wuPrimeComplements N).card : ℝ)) ∧
      ((GCurvatureChord.exactQuarter+
          (3629895479136046171/11308652260919376406875 : ℝ)+g15)*
        wuSingularSeries N*N/log N^(2 : ℕ) ≤
          ((Finset.filter (fun p => Nat.Prime p ∧ 0 < N-p ∧
            ArithmeticFunction.cardFactors (N-p) ≤ 2) (Finset.range (N+1))).card : ℝ)) := by
  obtain ⟨T,hT,h⟩ := kernel_curvature_actual_count
  refine ⟨T,hT,?_⟩
  intro N hN he
  have hs := (HighSixPhase6.original_scale_positive (show 512 ≤ N by omega)).le
  have hc : GCurvatureChord.exactQuarter+
      (3629895479136046171/11308652260919376406875 : ℝ)+g15 ≤
      GCurvatureChord.exactQuarter+
      firstFunctionalGainPsiOne HighSix.s HighSix.S*HighSix.primeIntegral 0+g15 := by
    linarith only [HighSixPhase6.exact_local_gain_lower]
  have hp := mul_le_mul_of_nonneg_right hc hs
  have hn := h N hN he
  have hfinal : (GCurvatureChord.exactQuarter+
      (3629895479136046171/11308652260919376406875 : ℝ)+g15)*
      wuSingularSeries N*N/log N^(2 : ℕ) ≤
      ((MathlibNt.Wu2008DoubleSieve.wuPrimeComplements N).card : ℝ) := by
    calc
      _ = (GCurvatureChord.exactQuarter+
        (3629895479136046171/11308652260919376406875 : ℝ)+g15)*
        (wuSingularSeries N*N/log N^(2 : ℕ)) := by ring
      _ ≤ (GCurvatureChord.exactQuarter+
        firstFunctionalGainPsiOne HighSix.s HighSix.S*HighSix.primeIntegral 0+g15)*
        (wuSingularSeries N*N/log N^(2 : ℕ)) := hp
      _ = (GCurvatureChord.exactQuarter+
        firstFunctionalGainPsiOne HighSix.s HighSix.S*HighSix.primeIntegral 0+g15)*
        wuSingularSeries N*N/log N^(2 : ℕ) := by ring
      _ ≤ _ := hn
  exact ⟨hfinal,hfinal⟩

theorem ordinary_coefficient_strict :
    GCurvatureChord.exactQuarter+(3629895479136046171/11308652260919376406875 : ℝ)+
      Phase14.g14 <
    GCurvatureChord.exactQuarter+(3629895479136046171/11308652260919376406875 : ℝ)+g15 := by
  linarith only [g15_strict]

end
end Wu2008DoubleSieve.Phase15
