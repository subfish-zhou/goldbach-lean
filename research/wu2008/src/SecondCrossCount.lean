import DisjointTailGain

namespace Wu2008DoubleSieve.Phase11
open Real HighSixPhase9 SingleUpperHIntegral
noncomputable section

/-- The feedback ratio and delta loss are unchanged; only raw integral mass is added. -/
def g11 : ℝ := Ctotal*sourceP/(1-Phase10.rhoLog)
def penalty11 : ℝ := Ctotal*envelopeE/(1-Phase10.rhoLog)


theorem penalty11_pos : 0 < penalty11 := by
  apply div_pos (mul_pos Ctotal_pos (by norm_num [envelopeE]))
    (sub_pos.mpr Phase10.rhoLog_bounds.2)

theorem gain11_with_penalty {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100) :
    g11-penalty δ*penalty11 ≤ gainH34 δ/4 := by
  have hi := (mul_le_mul_of_nonneg_left (Phase10.amplitude_log_closed hδ hδhi)
    Ctotal_pos.le).trans (actual_low_H_total_lower hδ hδhi)
  have he : g11-penalty δ*penalty11 =
      Ctotal*((sourceP-penalty δ*envelopeE)/(1-Phase10.rhoLog)) := by
    unfold g11 penalty11
    ring
  rwa [he]

theorem gain11_linear_error {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100) :
    g11-((100/49)*penalty11)*δ ≤ gainH34 δ/4 := by
  have hp := mul_le_mul_of_nonneg_right (ParentPhase9HalfWeight.penalty_le hδ hδhi)
    penalty11_pos.le
  have hi := gain11_with_penalty hδ hδhi
  nlinarith only [hp,hi]

theorem g11_strict : Phase10.gLog < g11 := by
  unfold Phase10.gLog g11
  apply (div_lt_div_iff_of_pos_right (sub_pos.mpr Phase10.rhoLog_bounds.2)).2
  apply mul_lt_mul_of_pos_right _ (by norm_num [sourceP])
  unfold Ctotal
  linarith only [Ctail_pos]

/-- The new unconditional raw-integral producer is actually supplied here. -/
theorem second_cross_actual_count :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (GCurvatureChord.exactQuarter+
        firstFunctionalGainPsiOne HighSix.s HighSix.S*HighSix.primeIntegral 0+g11)*
        wuSingularSeries N*N/log N^(2 : ℕ) ≤
          ((MathlibNt.Wu2008DoubleSieve.wuPrimeComplements N).card : ℝ) :=
  Phase10.same_mother_exact_payment g11 ((100/49)*penalty11)
    (mul_pos (by norm_num) penalty11_pos)
    (fun _ hδ hδhi => gain11_linear_error hδ hδhi)


theorem ordinary_coefficient_strict :
    GCurvatureChord.exactQuarter+(3629895479136046171/11308652260919376406875 : ℝ)+
      Phase10.gLog <
    GCurvatureChord.exactQuarter+(3629895479136046171/11308652260919376406875 : ℝ)+g11 := by
  linarith only [g11_strict]

end
end Wu2008DoubleSieve.Phase11
