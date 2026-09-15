import SrcFifthGainAnalyticConsumer

namespace WuSource.SrcFifthGain.Analytic
open Wu2008DoubleSieve WuTarget.Wu08FifthSource SharpMassBalance
open MeasureTheory Set Real
open scoped Interval
noncomputable section

theorem actual_nodes_nonneg {δ : ℝ} (hδ : 0 < δ) (hd : δ ≤ 1/1000) :
    ∀ j < 13, 0 ≤ wuImprovementLimit false δ (node (15+j)) := by
  intro j hj
  have hg := (cell_geometry hj).2.2.2.2
  exact wuImprovementLimit_nonneg false hδ (by linarith) (by linarith [hg.1]) hg.2

theorem actual_rational_source {δ : ℝ} (hδ : 0 < δ) (hd : δ ≤ 1/1000) :
    rationalGain (fun i => wuImprovementLimit false δ (node i)) ≤
      sourceGain (wuImprovementLimit false δ) :=
  rational_gain_source hδ hd (actual_nodes_nonneg hδ hd) (fun _j _hj => le_rfl)

theorem actual_mass_source {δ : ℝ} (hδ : 0 < δ) (hd : δ ≤ 1/1000) :
    massGain (fun i => wuImprovementLimit false δ (node i)) ≤
      sourceGain (wuImprovementLimit false δ) :=
  (mass_gain_le_grid (actual_nodes_nonneg hδ hd)).trans
    (grid_le_actual_source hδ hd (fun _j _hj => le_rfl))

theorem actual_rational_count {δ ε : ℝ} (hδ : 0 < δ) (hd : δ ≤ 1/1000)
    (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (fifthPairFdelta δ+rationalGain (fun i => wuImprovementLimit false δ (node i))-ε)*
        wuSingularSeries N*N/log N^(2 : ℕ) ≤ (fifthPairCount N : ℝ) := by
  obtain ⟨T, hT, hc⟩ := fifthH_actual_Fdelta_lower hδ hd hε
  have hgain := (actual_rational_source hδ hd).trans (actual_source_le_moving hδ hd)
  have hsplit := fifthH_actual_integral_split hδ hd
  have hcoef :
      fifthPairFdelta δ+rationalGain (fun i => wuImprovementLimit false δ (node i))-ε ≤
        fifthHFdelta δ-ε := by linarith only [hgain, hsplit]
  refine ⟨T, hT, fun N hN he => ?_⟩
  have h := (mul_le_mul_of_nonneg_right hcoef
    (truncatedSixthClosure_scale_nonneg (hT.trans hN))).trans (hc N hN he)
  simpa only [truncatedSixthMassScale, mul_div_assoc, mul_assoc] using h

end
end WuSource.SrcFifthGain.Analytic
