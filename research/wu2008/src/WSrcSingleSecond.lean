import PositiveSecondCount
import Wu08TerminalAlignment

noncomputable section
namespace WuSource.SrcSingle
open Wu2008DoubleSieve Real Set MeasureTheory
open scoped Interval
open BaseLowerCounts

def secondSource (δ : ℝ) : ℝ :=
  4 * wuImprovementLimit false δ ((1 / 2 - δ) / truncatedSixthLowerBeta) /
    (1 / 2 - δ)

def secondClassical (δ : ℝ) : ℝ :=
  4 * wuLowerCoefficient ((1 / 2 - δ) / truncatedSixthLowerBeta) / (1 / 2 - δ)

def secondTransfer (h22 : ℝ) (H : ℝ → ℝ) : ℝ :=
  h22 + ∫ t in (78 / 25 : ℝ)..(16 / 5), H t / t

theorem second_moving_geometry {δ : ℝ} (hd : 0 < δ) (hh : δ ≤ 1 / 100) :
    2 ≤ (1 / 2 - δ) / truncatedSixthLowerBeta ∧
      (1 / 2 - δ) / truncatedSixthLowerBeta ≤ (103 / 25 : ℝ) := by
  norm_num [truncatedSixthLowerBeta]
  constructor <;> linarith

theorem second_transfer_to_actual {δ h22 : ℝ} {H : ℝ → ℝ}
    (hd : 0 < δ) (hh : δ ≤ 1 / 100)
    (h22H : h22 ≤ wuImprovementLimit false δ (21 / 5))
    (hi : IntervalIntegrable (fun t => H t / t) volume (78 / 25) (16 / 5))
    (hH : ∀ t ∈ Icc (78 / 25 : ℝ) (16 / 5), H t ≤ wuImprovementLimit true δ t) :
    secondTransfer h22 H ≤
      wuImprovementLimit false δ ((1 / 2 - δ) / truncatedSixthLowerBeta) := by
  have hcross := wuImprovementLimit_lower_cross hd (by linarith : δ ≤ 1 / 10)
    (s := 103 / 25) (t := 21 / 5) (by norm_num) (by norm_num) (by norm_num)
  norm_num at hcross
  have hactual := wuImprovementLimit_div_intervalIntegrable true hd
    (by linarith : δ < 1 / 2) (a := 78 / 25) (b := 16 / 5)
    (by norm_num) (by norm_num) (by norm_num)
  have hint := intervalIntegral.integral_mono_on (by norm_num : (78 / 25 : ℝ) ≤ 16 / 5)
    hi hactual (fun t ht =>
      div_le_div_of_nonneg_right (hH t ht) (by linarith [ht.1]))
  have hs := second_moving_geometry hd hh
  have hmono := wuImprovementLimit_lower_antitone hd (by linarith : δ ≤ 1 / 10)
    ⟨hs.1, hs.2.trans (by norm_num)⟩
    (show (103 / 25 : ℝ) ∈ Icc 2 10 by norm_num) hs.2
  unfold secondTransfer
  linarith only [h22H, hint, hcross, hmono]

theorem second_transfer_to_source {δ h22 : ℝ} {H : ℝ → ℝ}
    (hd : 0 < δ) (hh : δ ≤ 1 / 100)
    (h22H : h22 ≤ wuImprovementLimit false δ (21 / 5))
    (hi : IntervalIntegrable (fun t => H t / t) volume (78 / 25) (16 / 5))
    (hH : ∀ t ∈ Icc (78 / 25 : ℝ) (16 / 5), H t ≤ wuImprovementLimit true δ t) :
    8 * secondTransfer h22 H ≤ secondSource δ := by
  have htrans := second_transfer_to_actual hd hh h22H hi hH
  have hs := second_moving_geometry hd hh
  have hn := wuImprovementLimit_nonneg false hd (by linarith : δ < 1 / 2)
    (by linarith : 1 ≤ (1 / 2 - δ) / truncatedSixthLowerBeta)
    (hs.2.trans (by norm_num))
  unfold secondSource
  apply (le_div_iff₀ (by linarith : 0 < (1 / 2 : ℝ) - δ)).mpr
  have hm := mul_le_mul_of_nonneg_right htrans
    (by linarith : 0 ≤ 8 * ((1 / 2 : ℝ) - δ))
  nlinarith only [hm, mul_nonneg hd.le hn]

theorem second_source_actual_count {δ ε : ℝ}
    (hd : 0 < δ) (hh : δ ≤ 1 / 100) (heps : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (secondClassical δ + secondSource δ - ε) * truncatedSixthMassScale N ≤
        (sieveCount N 1 N ((N : ℝ) ^ truncatedSixthLowerBeta) : ℝ) := by
  let A := secondClassical δ + secondSource δ
  by_cases hz : A - ε ≤ 0
  · refine ⟨4, le_rfl, fun N hN _ => ?_⟩
    exact (mul_nonpos_of_nonpos_of_nonneg hz
      (truncatedSixthClosure_scale_nonneg hN)).trans (by unfold sieveCount; positivity)
  · have hpos : 0 < A - ε := lt_of_not_ge hz
    have hc : 0 < (1 / 2 : ℝ) - δ := by linarith
    let η := ε * (1 / 2 - δ) / 8
    have hη : 0 < η := by dsimp [η]; positivity
    let b := wuLowerCoefficient ((1 / 2 - δ) / truncatedSixthLowerBeta) +
      wuImprovementLimit false δ ((1 / 2 - δ) / truncatedSixthLowerBeta) - η
    let B := 4 * b / (1 / 2 - δ)
    have hB : B = A - ε / 2 := by
      dsimp [B, b]
      rw [mul_sub, sub_div, mul_add, add_div]
      change A - 4 * η / (1 / 2 - δ) = A - ε / 2
      congr 1
      apply (div_eq_iff hc.ne').mpr
      dsimp [η]
      ring
    have hBpos : 0 < B := by linarith
    have hb : 0 ≤ b := by
      have hp := (lt_div_iff₀ hc).mp hBpos
      linarith
    have hs := second_moving_geometry hd hh
    obtain ⟨T, hT4, hT⟩ := fixed_delta_li_with_h hd
      (by linarith : δ < 1 / 2) (by linarith : 1 ≤ (1 / 2 - δ) / truncatedSixthLowerBeta)
      (hs.2.trans (by norm_num)) hη
    obtain ⟨M, hM⟩ := exists_nat_ge (4 * B / ε)
    refine ⟨max T M, hT4.trans (le_max_left _ _), fun N hN he => ?_⟩
    have hNT : T ≤ N := (le_max_left T M).trans hN
    have hN4 := hT4.trans hNT
    have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hMN : (M : ℝ) ≤ N := by exact_mod_cast ((le_max_right T M).trans hN)
    have hbudget := (div_le_iff₀ heps).mp (hM.trans hMN)
    have hsmall : B * (2 / (N : ℝ)) ≤ ε / 2 := by
      rw [← mul_div_assoc]
      apply (div_le_iff₀ hNr).mpr
      nlinarith
    have hcoef : A - ε ≤ B * (1 - 2 / (N : ℝ)) := by nlinarith
    have hmain := mul_le_mul_of_nonneg_right hcoef
      (truncatedSixthClosure_scale_nonneg hN4)
    have hli := normalized_li_lower hN4 hc hb
    have hcN := hT N hNT he
    change b * _ ≤ _ at hcN
    change _ ≤ B * (1 - 2 / (N : ℝ)) * truncatedSixthMassScale N at hmain
    have hli' : B * (1 - 2 / (N : ℝ)) * truncatedSixthMassScale N ≤
        b * (4 * AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418.logarithmicIntegral N *
          wuSingularSeries N / ((1 / 2 - δ) * log N)) := by
      simpa only [B, truncatedSixthMassScale, mul_div_assoc, mul_assoc] using hli
    exact hmain.trans (hli'.trans hcN)

theorem second_classical_continuous : ContinuousAt secondClassical 0 :=
  coefficient_continuous (by norm_num [truncatedSixthLowerBeta])

theorem second_classical_zero : secondClassical 0 = Wu08TerminalAlignment.secondMain := by
  unfold secondClassical Wu08TerminalAlignment.secondMain
  norm_num [truncatedSixthLowerBeta]
  ring

theorem second_original_count {ρ b ε : ℝ}
    (hρ : 0 < ρ)
    (hb : ∀ δ : ℝ, 0 < δ → δ ≤ ρ → δ ≤ 1 / 100 →
      8 * b ≤ secondSource δ)
    (heps : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (Wu08TerminalAlignment.secondMain + 8 * b - ε) * truncatedSixthMassScale N ≤
        (sieveCount N 1 N ((N : ℝ) ^ truncatedSixthLowerBeta) : ℝ) := by
  obtain ⟨r, hr, hnear⟩ := Metric.continuousAt_iff.mp second_classical_continuous
    (ε / 2) (half_pos heps)
  let δ := min (min r ρ) (1 / 100) / 2
  have hδ : 0 < δ := half_pos (lt_min (lt_min hr hρ) (by norm_num))
  have hlt : δ < min (min r ρ) (1 / 100) :=
    half_lt_self (lt_min (lt_min hr hρ) (by norm_num))
  have hδr := hlt.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hδρ := hlt.le.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hδhi := hlt.le.trans (min_le_right _ _)
  have hclose := hnear (show dist δ 0 < r by simpa [Real.dist_eq, abs_of_pos hδ])
  rw [Real.dist_eq, second_classical_zero, abs_lt] at hclose
  obtain ⟨T, hT, hc⟩ := second_source_actual_count hδ hδhi (half_pos heps)
  refine ⟨T, hT, fun N hN he => ?_⟩
  have hcoef : Wu08TerminalAlignment.secondMain + 8 * b - ε ≤
      secondClassical δ + secondSource δ - ε / 2 := by
    linarith only [hclose.1, hb δ hδ hδρ hδhi]
  exact (mul_le_mul_of_nonneg_right hcoef
    (truncatedSixthClosure_scale_nonneg (hT.trans hN))).trans (hc N hN he)

#check @second_transfer_to_actual
#check @second_original_count
#print axioms second_transfer_to_actual
#print axioms second_source_actual_count
#print axioms second_original_count
end WuSource.SrcSingle
