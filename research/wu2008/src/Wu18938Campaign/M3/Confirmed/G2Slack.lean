import Wu18938Campaign.M3.Confirmed.G2

noncomputable section

namespace Wu18938Campaign.M3.Confirmed

open Real Set MeasureTheory Wu2008DoubleSieve WuSource.SrcSingle

theorem correctedG2_slack_node {δ η : ℝ}
    (hd : 0 < δ) (hh : δ ≤ 1 / 100) (hη : η ≤ 52233 / 10000000)
    (hh42 : (6440 / 10000000 : ℝ) - η ≤ wuImprovementLimit false δ (21 / 5))
    (hH32 : (52233 / 10000000 : ℝ) - η ≤ wuImprovementLimit true δ (16 / 5)) :
    correctedG2 - (41 / 5) * η ≤ 8 * wuImprovementLimit false δ (103 / 25) := by
  have hcross := wuImprovementLimit_lower_cross hd (by linarith : δ ≤ 1 / 10)
    (s := 103 / 25) (t := 21 / 5) (by norm_num) (by norm_num) (by norm_num)
  norm_num at hcross
  have hi := wuImprovementLimit_div_intervalIntegrable true hd
    (by linarith : δ < 1 / 2) (a := 78 / 25) (b := 16 / 5)
    (by norm_num) (by norm_num) (by norm_num)
  have hint := intervalIntegral.integral_mono_on
    (by norm_num : (78 / 25 : ℝ) ≤ 16 / 5)
    (intervalIntegrable_const (c := ((52233 / 10000000 : ℝ) - η) / (16 / 5))) hi
    (fun t ht => show ((52233 / 10000000 : ℝ) - η) / (16 / 5) ≤
        wuImprovementLimit true δ t / t from by
      have ht0 : 0 < t := by linarith [ht.1]
      have hm := wuImprovementLimit_upper_antitone hd (by linarith : δ ≤ 1 / 10)
        (show t ∈ Icc 1 10 by constructor <;> linarith [ht.1, ht.2])
        (show (16 / 5 : ℝ) ∈ Icc 1 10 by norm_num) ht.2
      exact (div_le_div_of_nonneg_left (by linarith) ht0 ht.2).trans
        (div_le_div_of_nonneg_right (hH32.trans hm) ht0.le))
  norm_num [intervalIntegral.integral_const] at hint
  unfold correctedG2
  linarith

theorem correctedG2_slack_source {δ η : ℝ}
    (hd : 0 < δ) (hh : δ ≤ 1 / 100) (hη : η ≤ 52233 / 10000000)
    (hh42 : (6440 / 10000000 : ℝ) - η ≤ wuImprovementLimit false δ (21 / 5))
    (hH32 : (52233 / 10000000 : ℝ) - η ≤ wuImprovementLimit true δ (16 / 5)) :
    correctedG2 - (41 / 5) * η ≤ secondSource δ := by
  have hnode := correctedG2_slack_node hd hh hη hh42 hH32
  have hs := second_moving_geometry hd hh
  have hm := wuImprovementLimit_lower_antitone hd (by linarith : δ ≤ 1 / 10)
    ⟨hs.1, hs.2.trans (by norm_num)⟩
    (show (103 / 25 : ℝ) ∈ Icc 2 10 by norm_num) hs.2
  have hn := wuImprovementLimit_nonneg false hd (by linarith : δ < 1 / 2)
    (by linarith : 1 ≤ (1 / 2 - δ) / truncatedSixthLowerBeta)
    (hs.2.trans (by norm_num))
  have hsmall : correctedG2 - (41 / 5) * η ≤
      8 * wuImprovementLimit false δ ((1 / 2 - δ) / truncatedSixthLowerBeta) :=
    hnode.trans (mul_le_mul_of_nonneg_left hm (by norm_num))
  have hmul := mul_le_mul_of_nonneg_right hsmall
    (by linarith : 0 ≤ (1 / 2 : ℝ) - δ)
  unfold secondSource
  apply (le_div_iff₀ (by linarith : 0 < (1 / 2 : ℝ) - δ)).mpr
  nlinarith only [hmul, mul_nonneg hd.le hn]

theorem correctedG2_eventual_second_count
    (hnodes : ∀ η : ℝ, 0 < η →
      ∃ ρ : ℝ, 0 < ρ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ ρ → δ ≤ 1 / 100 →
        (6440 / 10000000 : ℝ) - η ≤ wuImprovementLimit false δ (21 / 5) ∧
        (52233 / 10000000 : ℝ) - η ≤ wuImprovementLimit true δ (16 / 5))
    {ε : ℝ} (heps : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (Wu08TerminalAlignment.secondMain + correctedG2 - ε) * truncatedSixthMassScale N ≤
        (sieveCount N 1 N ((N : ℝ) ^ truncatedSixthLowerBeta) : ℝ) := by
  let η : ℝ := min (52233 / 10000000) (5 * ε / 82)
  have hη : 0 < η := lt_min (by norm_num) (by positivity)
  have hηmax : η ≤ 52233 / 10000000 := min_le_left _ _
  have hηeps : (41 / 5 : ℝ) * η ≤ ε / 2 := by
    have h := min_le_right (52233 / 10000000 : ℝ) (5 * ε / 82)
    change η ≤ 5 * ε / 82 at h
    linarith
  obtain ⟨ρ, hρ, hn⟩ := hnodes η hη
  have hsource : ∀ δ : ℝ, 0 < δ → δ ≤ ρ → δ ≤ 1 / 100 →
      8 * ((correctedG2 - (41 / 5) * η) / 8) ≤ secondSource δ := by
    intro δ hd hδ hh
    obtain ⟨h1, h2⟩ := hn δ hd hδ hh
    simpa only [mul_div_cancel₀ _ (by norm_num : (8 : ℝ) ≠ 0)] using
      correctedG2_slack_source hd hh hηmax h1 h2
  obtain ⟨T, hT, hc⟩ := second_original_count hρ hsource (half_pos heps)
  refine ⟨T, hT, fun N hN he => ?_⟩
  have hcoef : Wu08TerminalAlignment.secondMain + correctedG2 - ε ≤
      Wu08TerminalAlignment.secondMain + 8 * ((correctedG2 - (41 / 5) * η) / 8) -
        ε / 2 := by linarith only [hηeps]
  exact (mul_le_mul_of_nonneg_right hcoef
    (truncatedSixthClosure_scale_nonneg (hT.trans hN))).trans (hc N hN he)

end Wu18938Campaign.M3.Confirmed
