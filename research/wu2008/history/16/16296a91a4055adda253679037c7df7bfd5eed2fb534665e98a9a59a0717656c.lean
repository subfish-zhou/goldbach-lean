import SrcSingleSecond
import MathlibNt.Wu2008DoubleSieve.HighSixLowHJoin

noncomputable section
namespace WuSource.SrcSingle
open Wu2008DoubleSieve Real Set MeasureTheory
open scoped Interval BigOperators

def levelExponent (δ : ℝ) : ℝ := 1 / 2 - δ
def fourthLeft (δ : ℝ) : ℝ := levelExponent δ / (2 * truncatedSixthLowerAlpha)
def fourthRight (δ : ℝ) : ℝ := levelExponent δ / truncatedSixthLowerAlpha - 1
def fourthKernel (δ s : ℝ) : ℝ :=
  wuImprovementLimit true δ s / (s * (levelExponent δ - truncatedSixthLowerAlpha * s))
def fourthSource (δ : ℝ) : ℝ :=
  4 * ∫ s in fourthLeft δ..fourthRight δ, fourthKernel δ s

theorem fourth_geometry {δ : ℝ} (hd : 0 ≤ δ) (hh : δ ≤ 1 / 100) :
    3 ≤ fourthLeft δ ∧ fourthLeft δ ≤ (1327 / 400 : ℝ) ∧
      (49 / 10 : ℝ) ≤ fourthRight δ ∧ fourthRight δ ≤ 6 ∧
      0 < levelExponent δ := by
  norm_num [fourthLeft, fourthRight, levelExponent, truncatedSixthLowerAlpha]
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

theorem fourth_kernel_change (δ s : ℝ) :
    truncatedSixthLowerAlpha *
      SingleUpperHIntegral.kernel δ (levelExponent δ - truncatedSixthLowerAlpha * s) =
        fourthKernel δ s := by
  have ha : truncatedSixthLowerAlpha ≠ 0 := by norm_num [truncatedSixthLowerAlpha]
  have hs : (levelExponent δ - (levelExponent δ - truncatedSixthLowerAlpha * s)) /
      truncatedSixthLowerAlpha = s := by field_simp; ring
  change truncatedSixthLowerAlpha *
    (wuImprovementLimit true δ
      ((levelExponent δ - (levelExponent δ - truncatedSixthLowerAlpha * s)) /
        truncatedSixthLowerAlpha) /
      ((levelExponent δ - truncatedSixthLowerAlpha * s) *
        (levelExponent δ - (levelExponent δ - truncatedSixthLowerAlpha * s)))) = _
  rw [hs, show levelExponent δ -
      (levelExponent δ - truncatedSixthLowerAlpha * s) = truncatedSixthLowerAlpha * s by ring]
  unfold fourthKernel
  simp only [div_eq_mul_inv, mul_inv_rev]
  field_simp [ha]

theorem windowGain_eq_fourthSource (δ : ℝ) :
    SingleUpperHIntegral.windowGain δ = fourthSource δ := by
  have ha : truncatedSixthLowerAlpha ≠ 0 := by norm_num [truncatedSixthLowerAlpha]
  have hl : levelExponent δ - truncatedSixthLowerAlpha * fourthLeft δ =
      levelExponent δ / 2 := by unfold fourthLeft; field_simp; ring
  have hr : levelExponent δ - truncatedSixthLowerAlpha * fourthRight δ =
      truncatedSixthLowerAlpha := by unfold fourthRight; field_simp; ring
  have hchange := intervalIntegral.integral_comp_sub_mul
    (SingleUpperHIntegral.kernel δ) (a := fourthLeft δ) (b := fourthRight δ)
    ha (levelExponent δ)
  rw [hl, hr, smul_eq_mul] at hchange
  have hmul := congrArg (fun x : ℝ => truncatedSixthLowerAlpha * x) hchange
  rw [← intervalIntegral.integral_const_mul] at hmul
  simp_rw [fourth_kernel_change] at hmul
  have hcancel : truncatedSixthLowerAlpha *
      (truncatedSixthLowerAlpha⁻¹ *
        ∫ x in truncatedSixthLowerAlpha..levelExponent δ / 2, SingleUpperHIntegral.kernel δ x) =
      ∫ x in truncatedSixthLowerAlpha..levelExponent δ / 2, SingleUpperHIntegral.kernel δ x := by
    rw [← mul_assoc, mul_inv_cancel₀ ha, one_mul]
  rw [hcancel] at hmul
  unfold SingleUpperHIntegral.windowGain fourthSource
  rw [hmul]
  rfl

theorem fourth_kernel_integrable {δ a b : ℝ} (hd : 0 < δ) (hh : δ ≤ 1 / 100)
    (ha : fourthLeft δ ≤ a) (hab : a ≤ b) (hb : b ≤ fourthRight δ) :
    IntervalIntegrable (fourthKernel δ) volume a b := by
  have hg := fourth_geometry hd.le hh
  have hlo : 1 ≤ a := by linarith [hg.1]
  have hhi : b ≤ 10 := by linarith [hg.2.2.2.1]
  have hn : ∀ s ∈ uIcc a b, levelExponent δ - truncatedSixthLowerAlpha * s ≠ 0 := by
    intro s hs
    rw [uIcc_of_le hab] at hs
    have hsa := hs.2.trans hb
    have hp := mul_le_mul_of_nonneg_left hsa
      (by norm_num [truncatedSixthLowerAlpha] : 0 ≤ truncatedSixthLowerAlpha)
    have he : truncatedSixthLowerAlpha * fourthRight δ =
        levelExponent δ - truncatedSixthLowerAlpha := by
      unfold fourthRight
      field_simp
      ring
    rw [he] at hp
    have hapos : 0 < truncatedSixthLowerAlpha := by norm_num [truncatedSixthLowerAlpha]
    linarith
  have hc : ContinuousOn (fun s => (levelExponent δ - truncatedSixthLowerAlpha * s)⁻¹)
      (uIcc a b) := by
    exact ContinuousOn.inv₀ (by fun_prop) hn
  have hi := wuImprovementLimit_div_intervalIntegrable true hd
    (by linarith : δ < 1 / 2) hlo hab hhi
  convert hi.mul_continuousOn hc using 1
  ext s
  simp only [fourthKernel, div_eq_mul_inv, mul_inv_rev]
  ring

theorem fourth_kernel_nonneg {δ s : ℝ} (hd : 0 < δ) (hh : δ ≤ 1 / 100)
    (hs : s ∈ Icc (fourthLeft δ) (fourthRight δ)) : 0 ≤ fourthKernel δ s := by
  have hg := fourth_geometry hd.le hh
  have hs1 : 1 ≤ s := by linarith [hg.1, hs.1]
  have hs10 : s ≤ 10 := by linarith [hg.2.2.2.1, hs.2]
  have hp := mul_le_mul_of_nonneg_left hs.2
    (by norm_num [truncatedSixthLowerAlpha] : 0 ≤ truncatedSixthLowerAlpha)
  have he : truncatedSixthLowerAlpha * fourthRight δ =
      levelExponent δ - truncatedSixthLowerAlpha := by
    unfold fourthRight
    field_simp
    ring
  rw [he] at hp
  have ha : 0 < truncatedSixthLowerAlpha := by norm_num [truncatedSixthLowerAlpha]
  exact div_nonneg (wuImprovementLimit_nonneg true hd (by linarith) hs1 hs10)
    (mul_nonneg (by linarith) (by linarith))

theorem fourth_truncated_le_source {δ : ℝ} (hd : 0 < δ) (hh : δ ≤ 1 / 100) :
    4 * (∫ s in (1327 / 400 : ℝ)..(49 / 10), fourthKernel δ s) ≤ fourthSource δ := by
  have hg := fourth_geometry hd.le hh
  have hfi := fourth_kernel_integrable hd hh le_rfl
    (by linarith [hg.2.1, hg.2.2.1] : fourthLeft δ ≤ fourthRight δ) le_rfl
  have hnon : 0 ≤ᵐ[volume.restrict (Ioc (fourthLeft δ) (fourthRight δ))] fourthKernel δ :=
    (ae_restrict_mem measurableSet_Ioc).mono
      (fun _ hs => fourth_kernel_nonneg hd hh ⟨hs.1.le, hs.2⟩)
  have hmono := intervalIntegral.integral_mono_interval hg.2.1
    (by norm_num : (1327 / 400 : ℝ) ≤ 49 / 10) hg.2.2.1 hnon hfi
  exact mul_le_mul_of_nonneg_left hmono (by norm_num)

theorem pair_actual_with_full_H {δ ε : ℝ}
    (hd : 0 < δ) (hh : δ ≤ 1 / 100) (heps : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (SingleUpperCounts.U N (1 / 3) : ℝ) +
        (SingleUpperCounts.U N truncatedSixthLowerSigma : ℝ) ≤
        (SingleUpperClassicalLimit.Gdelta δ (1 / 3) +
          SingleUpperClassicalLimit.Gdelta δ truncatedSixthLowerSigma -
          (fourthSource δ + fourthSource δ) -
          4 * firstFunctionalGainPsi δ HighSix.s HighSix.S * HighSix.primeIntegral δ + ε) *
            truncatedSixthMassScale N := by
  simpa only [SingleUpperHIntegral.gainH34, windowGain_eq_fourthSource] using
    HighSixLowHJoin.actual_pair_integral_psi_upper hd hh heps

#check @windowGain_eq_fourthSource
#check @pair_actual_with_full_H
#print axioms windowGain_eq_fourthSource
#print axioms fourth_truncated_le_source
#print axioms pair_actual_with_full_H
end WuSource.SrcSingle
