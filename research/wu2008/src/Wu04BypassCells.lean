import RemainingHfRows
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

noncomputable section
namespace Wu04Bypass
open Real Set MeasureTheory NodeExtension ActualNineFeedback FirstFeedbackIntegrals
open scoped Interval BigOperators

/-- An elementary rational lower bound for one genuine E-kernel cell. -/
def cell (S a b : ℝ) : ℝ :=
  (b - a) * (a + b - 2 * (S - 2)) / (2 * b * (b + 1))

theorem log_lower {S t : ℝ} (hS : 3 ≤ S) (ht : S - 2 ≤ t) :
    (t - (S - 2)) / (t + 1) ≤ log ((t + 1) / (S - 1)) := by
  have hs : 0 < S - 1 := by linarith
  have ht1 : 0 < t + 1 := by linarith
  have h := Real.log_le_sub_one_of_pos (div_pos hs ht1)
  rw [Real.log_div hs.ne' ht1.ne'] at h
  rw [Real.log_div ht1.ne' hs.ne']
  have he : (t - (S - 2)) / (t + 1) = 1 - (S - 1) / (t + 1) := by
    field_simp
    ring
  rw [he]
  linarith only [h]

theorem cell_le_integral {S a b : ℝ} (hS : 3 ≤ S) (ha : S - 2 ≤ a) (hab : a ≤ b) :
    cell S a b ≤ ∫ t in a..b, log ((t + 1) / (S - 1)) / t := by
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := ha0.trans_le hab
  have hi : IntervalIntegrable (fun t : ℝ => (t - (S - 2)) / (b * (b + 1))) volume a b :=
    (by fun_prop : Continuous (fun t : ℝ => (t - (S - 2)) / (b * (b + 1)))).intervalIntegrable a b
  have hj : IntervalIntegrable (fun t : ℝ => log ((t + 1) / (S - 1)) / t) volume a b := by
    apply ContinuousOn.intervalIntegrable_of_Icc (h := hab)
    intro t ht
    have ht0 : 0 < t := ha0.trans_le ht.1
    have ht1 : 0 < t + 1 := by linarith
    have hs : 0 < S - 1 := by linarith
    fun_prop (disch := positivity)
  have he : (∫ t in a..b, (t - (S - 2)) / (b * (b + 1))) = cell S a b := by
    have hd (t : ℝ) : HasDerivAt
        (fun x : ℝ => (x ^ 2 / 2 - (S - 2) * x) / (b * (b + 1)))
        ((t - (S - 2)) / (b * (b + 1))) t := by
      convert ((((hasDerivAt_id t).pow 2).div_const (2 : ℝ)).sub
        ((hasDerivAt_id t).const_mul (S - 2))).div_const (b * (b + 1)) using 1 <;> norm_num <;> rfl
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) hi]
    unfold cell
    field_simp
    ring
  rw [← he]
  apply intervalIntegral.integral_mono_on hab hi hj
  intro t ht
  have ht0 : 0 < t := ha0.trans_le ht.1
  have ht1 : 0 < t + 1 := by linarith
  have hn : 0 ≤ t - (S - 2) := by linarith [ht.1]
  have hden : t * (t + 1) ≤ b * (b + 1) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr ht.2) (by linarith : 0 ≤ b + t + 1)]
  have hd := div_le_div_of_nonneg_left hn (mul_pos ht0 ht1) hden
  have hl := div_le_div_of_nonneg_right (log_lower hS (ha.trans ht.1)) ht0.le
  exact hd.trans (by simpa only [div_div, mul_comm] using hl)

def cells (z : Fin 9 → ℝ) (S : ℝ) : ℝ :=
  ∑ k : Fin 9, z k * cell S (cellLeft (S - 2) k) (upperNode k)

theorem cells_le_eProfile {z : Fin 9 → ℝ} (hz : ∀ k, 0 ≤ z k) {S : ℝ}
    (hS : 3 ≤ S) (hS2 : S - 2 ≤ upperNode 0) :
    cells z S ≤ eProfile (nineProfile z) S := by
  have hS5 : S ≤ 5 := by have h := (upperNode_bounds 0).2; linarith
  have hw : ContinuousOn (fun t => log ((t + 1) / (S - 1)) / t) (uIcc (S - 2) 3) := by
    apply ContinuousOn.div (log_weight_continuous hS hS5) continuousOn_id
    intro t ht
    rw [uIcc_of_le (by linarith : S - 2 ≤ 3)] at ht
    dsimp
    linarith [ht.1]
  have he := profile_integral_cells z (by linarith : 1 ≤ S - 2) hS2 hw
  have hm : cells z S ≤ ∫ t in (S - 2)..3, nineProfile z t * (log ((t + 1) / (S - 1)) / t) := by
    rw [he]
    exact Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_left
      (cell_le_integral hS (cell_bounds (by linarith : 1 ≤ S - 2) hS2 k).1
        (cell_bounds (by linarith : 1 ≤ S - 2) hS2 k).2.1) (hz k))
  have hp := (profiles_nonneg (fun t _ => nineProfile_nonneg hz t)).1
  have hl : 0 ≤ log (4 / (S - 1)) :=
    log_nonneg ((one_le_div (by linarith : 0 < S - 1)).mpr (by linarith))
  unfold eProfile
  have hn := mul_nonneg hp hl
  simpa only [div_mul_eq_mul_div, mul_div_assoc] using hm.trans (le_add_of_nonneg_left hn)

theorem cells_basis (S : ℝ) (k : Fin 9) :
    cells (nodeBasis k) S = cell S (cellLeft (S - 2) k) (upperNode k) := by
  classical
  simp [cells, nodeBasis]

end Wu04Bypass
