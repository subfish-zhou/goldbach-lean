import QtwoWholeCertificate

/-! Exact method-of-steps recovery of Wu08 §5, not a numerical table premise. -/
noncomputable section
open Real Set MeasureTheory
open scoped Interval
open Wu2008DoubleSieve ClassicalAnalyticLeaves
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne
namespace Wu08OriginalFirstSteps

def k (v : ℝ) : ℝ := log (max 1 (v-1))/max 1 v
def B (s : ℝ) : ℝ := ∫ v in (2:ℝ)..(s-1), k v
def C (s : ℝ) : ℝ := ∫ v in (3:ℝ)..(s-1), B v/max 1 v
def D (s : ℝ) : ℝ := ∫ v in (4:ℝ)..(s-1), C v/max 1 v
def E (s : ℝ) : ℝ := ∫ v in (5:ℝ)..(s-1), D v/max 1 v

theorem k_continuous : Continuous k := by
  unfold k
  apply Continuous.div
  · apply Continuous.log (by fun_prop)
    intro x
    exact (lt_of_lt_of_le (by norm_num : (0:ℝ)<1) (le_max_left _ _)).ne'
  · fun_prop
  · intro x
    exact (lt_of_lt_of_le (by norm_num : (0:ℝ)<1) (le_max_left _ _)).ne'

theorem moving_continuous {f : ℝ → ℝ} (hf : Continuous f) (l : ℝ) :
    Continuous (fun s : ℝ => ∫ v in l..(s-1), f v) := by
  apply gamma5Gain_moving_integral (f := fun (_s v : ℝ) => f v)
  · exact hf.comp continuous_snd
  · fun_prop
  · fun_prop

theorem div_continuous {f : ℝ → ℝ} (hf : Continuous f) :
    Continuous (fun v : ℝ => f v/max 1 v) := by
  apply hf.div (by fun_prop)
  intro x
  exact (lt_of_lt_of_le (by norm_num : (0:ℝ)<1) (le_max_left _ _)).ne'

theorem B_continuous : Continuous B := moving_continuous k_continuous 2
theorem C_continuous : Continuous C := moving_continuous (div_continuous B_continuous) 3
theorem D_continuous : Continuous D := moving_continuous (div_continuous C_continuous) 4
theorem E_continuous : Continuous E := moving_continuous (div_continuous D_continuous) 5

theorem k_literal {v : ℝ} (hv : 2 ≤ v) : k v = log (v-1)/v := by
  simp only [k,max_eq_right (show (1:ℝ) ≤ v-1 by linarith),
    max_eq_right (show (1:ℝ) ≤ v by linarith)]

theorem reciprocal_integrable {l r : ℝ} (hl : 0 < l) (hlr : l ≤ r) :
    IntervalIntegrable (fun v : ℝ => 1/v) volume l r := by
  apply ContinuousOn.intervalIntegrable
  exact continuousOn_const.div continuousOn_id (fun v hv => by
    rw [uIcc_of_le hlr] at hv
    exact (hl.trans_le hv.1).ne')

/-- The author's A(s)=1+int_2^(s-1) log(v-1)/v on the full initial range. -/
theorem upper_initial {s : ℝ} (hs : 3 ≤ s) (hs5 : s ≤ 5) :
    wuUpperCoefficient s = 1+B s := by
  have hr := wuUpperCoefficient_sub_eq_integral (by norm_num : (2:ℝ) ≤ 3) hs
  have hi : wuUpperCoefficient 3 = 1 := jr1965F_normalized_initial (by norm_num) le_rfl
  have he : (∫ v in (2:ℝ)..(s-1), wuLowerCoefficient v/v) = B s := by
    unfold B
    apply intervalIntegral.integral_congr
    intro v hv
    dsimp only
    rw [uIcc_of_le (show (2:ℝ) ≤ s-1 by linarith)] at hv
    have hvinit : wuLowerCoefficient v = log (v-1) :=
      jr1965f_normalized_firstInterval hv.1 (by linarith [hv.2])
    rw [hvinit,k_literal hv.1]
  norm_num only [show (3:ℝ)-1=2 by norm_num,hi] at hr
  linarith only [hr,he]

/-- Exact twofold recurrence, not an extrapolation of the initial logarithm. -/
theorem lower_middle {s : ℝ} (hs : 4 ≤ s) (hs6 : s ≤ 6) :
    wuLowerCoefficient s = log (s-1)+C s := by
  have ho : (3:ℝ) ≤ s-1 := by linarith
  have hi := reciprocal_integrable (by norm_num : (0:ℝ)<3) ho
  have hb := (div_continuous B_continuous).intervalIntegrable (μ := volume) 3 (s-1)
  have he : (∫ v in (3:ℝ)..(s-1), wuUpperCoefficient v/v) =
      (∫ v in (3:ℝ)..(s-1), 1/v)+C s := by
    unfold C
    rw [← intervalIntegral.integral_add hi hb]
    apply intervalIntegral.integral_congr
    intro v hv
    dsimp only
    rw [uIcc_of_le ho] at hv
    rw [upper_initial hv.1 (by linarith [hv.2]),max_eq_right (show (1:ℝ) ≤ v by linarith [hv.1])]
    ring
  have hr := wuLowerCoefficient_sub_eq_integral (by norm_num : (2:ℝ) ≤ 4) hs
  norm_num only [show (4:ℝ)-1=3 by norm_num,BaseRecurrenceLower.lower_four_value] at hr
  rw [integral_reciprocal (by norm_num) ho] at he
  linarith only [hr,he]

/-- Integral differences with the actual moving endpoint, for the next two steps. -/
theorem B_difference (s : ℝ) :
    B s-B 5 = ∫ v in (4:ℝ)..(s-1), k v := by
  have h := intervalIntegral.integral_add_adjacent_intervals
    (k_continuous.intervalIntegrable (μ := volume) 2 4) (k_continuous.intervalIntegrable (μ := volume) 4 (s-1))
  norm_num [B] at *
  linarith only [h]

theorem C_difference (s : ℝ) :
    C s-C 6 = ∫ v in (5:ℝ)..(s-1), B v/max 1 v := by
  have h := intervalIntegral.integral_add_adjacent_intervals
    ((div_continuous B_continuous).intervalIntegrable (μ := volume) 3 5)
    ((div_continuous B_continuous).intervalIntegrable (μ := volume) 5 (s-1))
  norm_num [C] at *
  linarith only [h]

end Wu08OriginalFirstSteps
