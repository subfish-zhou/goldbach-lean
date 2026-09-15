import Wu08OriginalFirstSteps

noncomputable section
open Real Set MeasureTheory
open scoped Interval
open Wu2008DoubleSieve ClassicalAnalyticLeaves
namespace Wu08OriginalFirstSteps

/-- The original threefold correction to A on its second range. -/
theorem upper_middle {s : ℝ} (hs : 5 ≤ s) (hs7 : s ≤ 7) :
    wuUpperCoefficient s = 1+B s+D s := by
  have ho : (4:ℝ) ≤ s-1 := by linarith
  have hk := k_continuous.intervalIntegrable (μ := volume) 4 (s-1)
  have hc := (div_continuous C_continuous).intervalIntegrable (μ := volume) 4 (s-1)
  have he : (∫ v in (4:ℝ)..(s-1), wuLowerCoefficient v/v) =
      (∫ v in (4:ℝ)..(s-1), k v)+D s := by
    unfold D
    rw [← intervalIntegral.integral_add hk hc]
    apply intervalIntegral.integral_congr
    intro v hv
    dsimp only
    rw [uIcc_of_le ho] at hv
    rw [lower_middle hv.1 (by linarith [hv.2]),k_literal (by linarith [hv.1]),
      max_eq_right (show (1:ℝ) ≤ v by linarith [hv.1])]
    ring
  have hr := wuUpperCoefficient_sub_eq_integral (by norm_num : (2:ℝ) ≤ 5) hs
  norm_num only [show (5:ℝ)-1=4 by norm_num,upper_initial (by norm_num : (3:ℝ) ≤ 5) le_rfl] at hr
  have hb := B_difference s
  linarith only [hr,he,hb]

/-- The author's full 6-to-8 formula, including its FOURFOLD positive term. -/
theorem lower_terminal {s : ℝ} (hs : 6 ≤ s) (hs8 : s ≤ 8) :
    wuLowerCoefficient s = log (s-1)+C s+E s := by
  have ho : (5:ℝ) ≤ s-1 := by linarith
  have hi := reciprocal_integrable (by norm_num : (0:ℝ)<5) ho
  have hb := (div_continuous B_continuous).intervalIntegrable (μ := volume) 5 (s-1)
  have hd := (div_continuous D_continuous).intervalIntegrable (μ := volume) 5 (s-1)
  have he : (∫ v in (5:ℝ)..(s-1), wuUpperCoefficient v/v) =
      (∫ v in (5:ℝ)..(s-1), 1/v)+
      (∫ v in (5:ℝ)..(s-1), B v/max 1 v)+E s := by
    unfold E
    rw [← intervalIntegral.integral_add hi hb,← intervalIntegral.integral_add (hi.add hb) hd]
    apply intervalIntegral.integral_congr
    intro v hv
    dsimp only
    rw [uIcc_of_le ho] at hv
    rw [upper_middle hv.1 (by linarith [hv.2]),max_eq_right (show (1:ℝ) ≤ v by linarith [hv.1])]
    ring
  have hr := wuLowerCoefficient_sub_eq_integral (by norm_num : (2:ℝ) ≤ 6) hs
  norm_num only [show (6:ℝ)-1=5 by norm_num,lower_middle (by norm_num : (4:ℝ) ≤ 6) le_rfl] at hr
  rw [integral_reciprocal (by norm_num) ho] at he
  have hc := C_difference s
  linarith only [hr,he,hc]

theorem B_literal {s : ℝ} (hs : 3 ≤ s) :
    B s = ∫ v in (2:ℝ)..(s-1), log (v-1)/v := by
  apply intervalIntegral.integral_congr
  intro v hv
  rw [uIcc_of_le (show (2:ℝ) ≤ s-1 by linarith)] at hv
  exact k_literal hv.1

theorem C_literal {s : ℝ} (hs : 4 ≤ s) :
    C s = ∫ t in (3:ℝ)..(s-1), (∫ u in (2:ℝ)..(t-1), log (u-1)/u)/t := by
  apply intervalIntegral.integral_congr
  intro t ht
  dsimp only
  rw [uIcc_of_le (show (3:ℝ) ≤ s-1 by linarith)] at ht
  rw [B_literal ht.1,max_eq_right (show (1:ℝ) ≤ t by linarith [ht.1])]

theorem D_literal {s : ℝ} (hs : 5 ≤ s) :
    D s = ∫ u in (4:ℝ)..(s-1),
      (∫ v in (3:ℝ)..(u-1), (∫ w in (2:ℝ)..(v-1), log (w-1)/w)/v)/u := by
  apply intervalIntegral.integral_congr
  intro u hu
  dsimp only
  rw [uIcc_of_le (show (4:ℝ) ≤ s-1 by linarith)] at hu
  rw [C_literal hu.1,max_eq_right (show (1:ℝ) ≤ u by linarith [hu.1])]

theorem E_literal {s : ℝ} (hs : 6 ≤ s) :
    E s = ∫ t in (5:ℝ)..(s-1), (∫ u in (4:ℝ)..(t-1),
      (∫ v in (3:ℝ)..(u-1), (∫ w in (2:ℝ)..(v-1), log (w-1)/w)/v)/u)/t := by
  apply intervalIntegral.integral_congr
  intro t ht
  dsimp only
  rw [uIcc_of_le (show (5:ℝ) ≤ s-1 by linarith)] at ht
  rw [D_literal ht.1,max_eq_right (show (1:ℝ) ≤ t by linarith [ht.1])]

/-- Source-faithful integral formula; the regularizations have disappeared. -/
theorem original_formula {s : ℝ} (hs : 6 ≤ s) (hs8 : s ≤ 8) :
    wuLowerCoefficient s = log (s-1)+
      (∫ t in (3:ℝ)..(s-1), (∫ u in (2:ℝ)..(t-1), log (u-1)/u)/t)+
      (∫ t in (5:ℝ)..(s-1), (∫ u in (4:ℝ)..(t-1),
        (∫ v in (3:ℝ)..(u-1), (∫ w in (2:ℝ)..(v-1), log (w-1)/w)/v)/u)/t) := by
  rw [lower_terminal hs hs8,C_literal (by linarith),E_literal hs]

/-- Nonnegativity is proved, not taken from a numerical table. -/
theorem B_nonneg {s : ℝ} (hs : 3 ≤ s) : 0 ≤ B s := by
  apply intervalIntegral.integral_nonneg (by linarith)
  intro v _hv
  exact div_nonneg (log_nonneg (le_max_left _ _))
    (le_trans (by norm_num : (0:ℝ) ≤ 1) (le_max_left _ _))

theorem C_nonneg {s : ℝ} (hs : 4 ≤ s) : 0 ≤ C s := by
  apply intervalIntegral.integral_nonneg (by linarith)
  intro v hv
  exact div_nonneg (B_nonneg hv.1)
    (le_trans (by norm_num : (0:ℝ) ≤ 1) (le_max_left _ _))

theorem D_nonneg {s : ℝ} (hs : 5 ≤ s) : 0 ≤ D s := by
  apply intervalIntegral.integral_nonneg (by linarith)
  intro v hv
  exact div_nonneg (C_nonneg hv.1)
    (le_trans (by norm_num : (0:ℝ) ≤ 1) (le_max_left _ _))

theorem E_nonneg {s : ℝ} (hs : 6 ≤ s) : 0 ≤ E s := by
  apply intervalIntegral.integral_nonneg (by linarith)
  intro v hv
  exact div_nonneg (D_nonneg hv.1)
    (le_trans (by norm_num : (0:ℝ) ≤ 1) (le_max_left _ _))

#print axioms original_formula
end Wu08OriginalFirstSteps
