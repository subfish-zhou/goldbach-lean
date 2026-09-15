import WSrcFifthGainActual

namespace WuSource.SrcFifthGain
open Wu2008DoubleSieve WuTarget.Wu08FifthSource SharpMassBalance
open MeasureTheory Set Real
open scoped Interval
noncomputable section

theorem fifth_delta_close_below {d ε : ℝ} (hd : 0 < d) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1/1000 ∧ δ ≤ d ∧ |fifthPairFdelta δ-fifthPairFlin| < ε := by
  obtain ⟨r, hr, hc⟩ := Metric.tendsto_nhdsWithin_nhds.mp fifthPair_Fdelta_right_limit ε hε
  let δ := min (r/2) (min d (1/1000))
  have hδ : 0 < δ := lt_min (half_pos hr) (lt_min hd (by norm_num))
  have hδr : δ < r := (min_le_left _ _).trans_lt (by linarith)
  refine ⟨δ, hδ, (min_le_right _ _).trans (min_le_right _ _),
    (min_le_right _ _).trans (min_le_left _ _), ?_⟩
  have hh := hc hδ (show dist δ 0 < r by simpa [Real.dist_eq, abs_of_pos hδ] using hδr)
  simpa only [Real.dist_eq] using hh

theorem grid_count_below {h : ℕ → ℝ} {d : ℝ} (hd : 0 < d)
    (hn : ∀ j < 13, 0 ≤ h (15+j))
    (hc : ∀ δ : ℝ, 0 < δ → δ ≤ 1/1000 → δ ≤ d →
      ∀ j < 13, h (15+j) ≤ wuImprovementLimit false δ (node (15+j)))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (fifthPairFlin+gridGain h-ε)*wuSingularSeries N*N/log N^(2 : ℕ) ≤
        (fifthPairCount N : ℝ) := by
  obtain ⟨δ, hδ, hδhi, hδd, hclose⟩ := fifth_delta_close_below hd (half_pos hε)
  obtain ⟨T, hT, hcount⟩ := fifthH_actual_Fdelta_lower hδ hδhi (half_pos hε)
  have hg := grid_gain_uniform hδ hδhi hn (hc δ hδ hδhi hδd)
  have hs := fifthH_actual_integral_split hδ hδhi
  have hcoef : fifthPairFlin+gridGain h-ε ≤ fifthHFdelta δ-ε/2 := by
    linarith [(abs_lt.mp hclose).1]
  refine ⟨T, hT, fun N hN he => ?_⟩
  have hm := (mul_le_mul_of_nonneg_right hcoef
    (truncatedSixthClosure_scale_nonneg (hT.trans hN))).trans (hcount N hN he)
  simpa only [truncatedSixthMassScale, mul_div_assoc, mul_assoc] using hm

theorem certified_g5_count {h w : ℕ → ℝ} {d g : ℝ} (hd : 0 < d)
    (hn : ∀ j < 13, 0 ≤ h (15+j))
    (hc : ∀ δ : ℝ, 0 < δ → δ ≤ 1/1000 → δ ≤ d →
      ∀ j < 13, h (15+j) ≤ wuImprovementLimit false δ (node (15+j)))
    (hw : ∀ j < 13, w j ≤ cellWeight j) (hg : g ≤ directedGain h w)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (fifthPairFlin+g-ε)*wuSingularSeries N*N/log N^(2 : ℕ) ≤
        (fifthPairCount N : ℝ) := by
  obtain ⟨T, hT, hcN⟩ := grid_count_below hd hn hc hε
  have hg' := hg.trans (directed_gain_le_grid hn hw)
  refine ⟨T, hT, fun N hN he => ?_⟩
  have hm := mul_le_mul_of_nonneg_right
    (show fifthPairFlin+g-ε ≤ fifthPairFlin+gridGain h-ε by linarith)
    (truncatedSixthClosure_scale_nonneg (hT.trans hN))
  have hm' : (fifthPairFlin+g-ε)*wuSingularSeries N*N/log N^(2 : ℕ) ≤
      (fifthPairFlin+gridGain h-ε)*wuSingularSeries N*N/log N^(2 : ℕ) := by
    simpa only [truncatedSixthMassScale, mul_div_assoc, mul_assoc] using hm
  exact hm'.trans (hcN N hN he)

end
end WuSource.SrcFifthGain
