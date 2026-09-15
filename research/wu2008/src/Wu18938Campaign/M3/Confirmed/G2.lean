import WSrcSingleSecond
import Wu18938Campaign.M3.Confirmed.Numerics

noncomputable section

namespace Wu18938Campaign.M3.Confirmed

open Real Set MeasureTheory Wu2008DoubleSieve WuSource.SrcSingle

theorem correctedG2_actual_node {δ : ℝ} (hd : 0 < δ) (hh : δ ≤ 1 / 100)
    (hh42 : (6440 / 10000000 : ℝ) ≤ wuImprovementLimit false δ (21 / 5))
    (hH32 : (52233 / 10000000 : ℝ) ≤ wuImprovementLimit true δ (16 / 5)) :
    correctedG2 ≤ 8 * wuImprovementLimit false δ (103 / 25) := by
  have hcross := wuImprovementLimit_lower_cross hd (by linarith : δ ≤ 1 / 10)
    (s := 103 / 25) (t := 21 / 5) (by norm_num) (by norm_num) (by norm_num)
  norm_num at hcross
  have hi := wuImprovementLimit_div_intervalIntegrable true hd
    (by linarith : δ < 1 / 2) (a := 78 / 25) (b := 16 / 5)
    (by norm_num) (by norm_num) (by norm_num)
  have hint := intervalIntegral.integral_mono_on
    (by norm_num : (78 / 25 : ℝ) ≤ 16 / 5)
    (intervalIntegrable_const (c := (52233 / 10000000 : ℝ) / (16 / 5))) hi
    (fun t ht => show (52233 / 10000000 : ℝ) / (16 / 5) ≤
        wuImprovementLimit true δ t / t from by
      have ht0 : 0 < t := by linarith [ht.1]
      have hm := wuImprovementLimit_upper_antitone hd (by linarith : δ ≤ 1 / 10)
        (show t ∈ Icc 1 10 by constructor <;> linarith [ht.1, ht.2])
        (show (16 / 5 : ℝ) ∈ Icc 1 10 by norm_num) ht.2
      calc
        _ ≤ (52233 / 10000000 : ℝ) / t :=
          div_le_div_of_nonneg_left (by norm_num) ht0 ht.2
        _ ≤ _ := div_le_div_of_nonneg_right (hH32.trans hm) ht0.le)
  norm_num [intervalIntegral.integral_const] at hint
  unfold correctedG2
  linarith

theorem correctedG2_actual_source {δ : ℝ} (hd : 0 < δ) (hh : δ ≤ 1 / 100)
    (hh42 : (6440 / 10000000 : ℝ) ≤ wuImprovementLimit false δ (21 / 5))
    (hH32 : (52233 / 10000000 : ℝ) ≤ wuImprovementLimit true δ (16 / 5)) :
    correctedG2 ≤ secondSource δ := by
  have hnode := correctedG2_actual_node hd hh hh42 hH32
  have hs := second_moving_geometry hd hh
  have hm := wuImprovementLimit_lower_antitone hd (by linarith : δ ≤ 1 / 10)
    ⟨hs.1, hs.2.trans (by norm_num)⟩
    (show (103 / 25 : ℝ) ∈ Icc 2 10 by norm_num) hs.2
  have hg : 0 ≤ correctedG2 := by norm_num [correctedG2]
  unfold secondSource
  apply (le_div_iff₀ (by linarith : 0 < (1 / 2 : ℝ) - δ)).mpr
  nlinarith [mul_nonneg hg hd.le]

theorem correctedG2_actual_second_count {ρ ε : ℝ} (hρ : 0 < ρ)
    (hnodes : ∀ δ : ℝ, 0 < δ → δ ≤ ρ → δ ≤ 1 / 100 →
      (6440 / 10000000 : ℝ) ≤ wuImprovementLimit false δ (21 / 5) ∧
      (52233 / 10000000 : ℝ) ≤ wuImprovementLimit true δ (16 / 5))
    (heps : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (Wu08TerminalAlignment.secondMain + correctedG2 - ε) * truncatedSixthMassScale N ≤
        (sieveCount N 1 N ((N : ℝ) ^ truncatedSixthLowerBeta) : ℝ) := by
  have hsource : ∀ δ : ℝ, 0 < δ → δ ≤ ρ → δ ≤ 1 / 100 →
      8 * (correctedG2 / 8) ≤ secondSource δ := by
    intro δ hd hδρ hh
    obtain ⟨hh42, hH32⟩ := hnodes δ hd hδρ hh
    simpa only [mul_div_cancel₀ _ (by norm_num : (8 : ℝ) ≠ 0)] using
      correctedG2_actual_source hd hh hh42 hH32
  simpa only [mul_div_cancel₀ _ (by norm_num : (8 : ℝ) ≠ 0)] using
    second_original_count hρ hsource heps

end Wu18938Campaign.M3.Confirmed
