import MathlibNt.Wu2008DoubleSieve.FourRoughMassBudget
import MathlibNt.Wu2008DoubleSieve.Gamma5GainRectangleIntegral

/-! The original classical fourfold integrals, without numerical evaluation. -/
namespace Wu2008DoubleSieve.FourRoughClosedMass
open Set Real MeasureTheory LiLiuPrereqBuchstab
noncomputable section

def I10 : ℝ := ∫ x in alpha..beta, ∫ y in x..beta, ∫ z in y..beta,
  ∫ t in z..beta, kernel x y z t
def I11 : ℝ := ∫ x in alpha..beta, ∫ y in x..beta, ∫ z in y..beta,
  ∫ t in beta..lam-z, kernel x y z t

def clip (x : ℝ) : ℝ := max alpha x
def regularKernel (x y z t : ℝ) : ℝ :=
  buchstab (max 2 (parameter (clip x) (clip y) (clip z) (clip t))) /
    (clip x * clip y ^ 2 * clip z * clip t)

theorem clip_pos (x : ℝ) : 0 < clip x := fixed_geometry.2.1.trans_le (le_max_left _ _)

theorem regularKernel_continuous :
    Continuous (fun q : ℝ × ℝ × ℝ × ℝ => regularKernel q.1 q.2.1 q.2.2.1 q.2.2.2) := by
  have hclip : Continuous clip := continuous_const.max continuous_id
  have hp : Continuous (fun q : ℝ × ℝ × ℝ × ℝ =>
      parameter (clip q.1) (clip q.2.1) (clip q.2.2.1) (clip q.2.2.2)) := by
    unfold parameter
    have hnum : Continuous (fun q : ℝ × ℝ × ℝ × ℝ =>
        1-clip q.1-clip q.2.1-clip q.2.2.1-clip q.2.2.2) := by fun_prop
    exact hnum.div (hclip.comp (by fun_prop)) (fun q => (clip_pos q.2.1).ne')
  have harg := (continuous_const (y := (2 : ℝ))).max hp
  have hb := continuousOn_buchstab.comp_continuous harg
    (fun q => show (1 : ℝ) ≤ max 2 (parameter (clip q.1) (clip q.2.1) (clip q.2.2.1) (clip q.2.2.2)) from
      le_trans (by norm_num) (le_max_left _ _))
  unfold regularKernel
  apply hb.div
  · fun_prop
  · intro q
    exact (mul_pos (mul_pos (mul_pos (clip_pos _) (sq_pos_of_pos (clip_pos _)))
      (clip_pos _)) (clip_pos _)).ne'

theorem regularKernel_eq_ten {x y z t : ℝ}
    (hx : alpha ≤ x) (hxy : x ≤ y) (hyz : y ≤ z) (hzt : z ≤ t) (ht : t ≤ beta) :
    regularKernel x y z t = kernel x y z t := by
  simp only [regularKernel, clip, max_eq_right hx, max_eq_right (hx.trans hxy),
    max_eq_right (hx.trans (hxy.trans hyz)), max_eq_right (hx.trans (hxy.trans (hyz.trans hzt))),
    max_eq_right (ten_parameter hx hxy hyz hzt ht), kernel]

theorem regularKernel_eq_eleven {x y z t : ℝ}
    (hx : alpha ≤ x) (hxy : x ≤ y) (hyz : y ≤ z) (hz : z ≤ beta)
    (hbt : beta ≤ t) (ht : t ≤ lam-z) : regularKernel x y z t = kernel x y z t := by
  simp only [regularKernel, clip, max_eq_right hx, max_eq_right (hx.trans hxy),
    max_eq_right (hx.trans (hxy.trans hyz)),
    max_eq_right (hx.trans (hxy.trans (hyz.trans (hz.trans hbt)))),
    max_eq_right (eleven_parameter hx hxy hyz hz ht), kernel]

def regularInner10 (x y z : ℝ) : ℝ := ∫ t in z..beta, regularKernel x y z t
def regularInner11 (x y z : ℝ) : ℝ := ∫ t in beta..lam-z, regularKernel x y z t
def regularMiddle10 (x y : ℝ) : ℝ := ∫ z in y..beta, regularInner10 x y z
def regularMiddle11 (x y : ℝ) : ℝ := ∫ z in y..beta, regularInner11 x y z
def regularOuter10 (x : ℝ) : ℝ := ∫ y in x..beta, regularMiddle10 x y
def regularOuter11 (x : ℝ) : ℝ := ∫ y in x..beta, regularMiddle11 x y

theorem regularInner10_continuous : Continuous (fun q : ℝ × ℝ × ℝ => regularInner10 q.1 q.2.1 q.2.2) := by
  unfold regularInner10
  apply gamma5Gain_moving_integral
    (f := fun (q : ℝ × ℝ × ℝ) t => regularKernel q.1 q.2.1 q.2.2 t)
  · have h := regularKernel_continuous.comp
      (show Continuous (fun q : (ℝ × ℝ × ℝ) × ℝ => (q.1.1,q.1.2.1,q.1.2.2,q.2)) by fun_prop)
    exact h
  · fun_prop
  · fun_prop

theorem regularInner11_continuous : Continuous (fun q : ℝ × ℝ × ℝ => regularInner11 q.1 q.2.1 q.2.2) := by
  unfold regularInner11
  apply gamma5Gain_moving_integral
    (f := fun (q : ℝ × ℝ × ℝ) t => regularKernel q.1 q.2.1 q.2.2 t)
  · have h := regularKernel_continuous.comp
      (show Continuous (fun q : (ℝ × ℝ × ℝ) × ℝ => (q.1.1,q.1.2.1,q.1.2.2,q.2)) by fun_prop)
    exact h
  · fun_prop
  · fun_prop

theorem regularMiddle10_continuous : Continuous (fun q : ℝ × ℝ => regularMiddle10 q.1 q.2) := by
  unfold regularMiddle10
  apply gamma5Gain_moving_integral
    (f := fun (q : ℝ × ℝ) z => regularInner10 q.1 q.2 z)
  · have h := regularInner10_continuous.comp
      (show Continuous (fun q : (ℝ × ℝ) × ℝ => (q.1.1,q.1.2,q.2)) by fun_prop)
    exact h
  · fun_prop
  · fun_prop

theorem regularMiddle11_continuous : Continuous (fun q : ℝ × ℝ => regularMiddle11 q.1 q.2) := by
  unfold regularMiddle11
  apply gamma5Gain_moving_integral
    (f := fun (q : ℝ × ℝ) z => regularInner11 q.1 q.2 z)
  · have h := regularInner11_continuous.comp
      (show Continuous (fun q : (ℝ × ℝ) × ℝ => (q.1.1,q.1.2,q.2)) by fun_prop)
    exact h
  · fun_prop
  · fun_prop

theorem regularOuter10_continuous : Continuous regularOuter10 := by
  apply gamma5Gain_moving_integral
  · exact regularMiddle10_continuous
  · fun_prop
  · fun_prop

theorem regularOuter11_continuous : Continuous regularOuter11 := by
  apply gamma5Gain_moving_integral
  · exact regularMiddle11_continuous
  · fun_prop
  · fun_prop

theorem inner10_eq {x y z : ℝ} (hx : alpha ≤ x) (hxy : x ≤ y)
    (hyz : y ≤ z) (hz : z ≤ beta) :
    regularInner10 x y z = ∫ t in z..beta, kernel x y z t := by
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le hz] at ht
  exact regularKernel_eq_ten hx hxy hyz ht.1 ht.2

theorem inner11_eq {x y z : ℝ} (hx : alpha ≤ x) (hxy : x ≤ y)
    (hyz : y ≤ z) (hz : z ≤ beta) :
    regularInner11 x y z = ∫ t in beta..lam-z, kernel x y z t := by
  have horder : beta ≤ lam-z := by linarith [fixed_geometry.2.2.2.2.2.2.1]
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le horder] at ht
  exact regularKernel_eq_eleven hx hxy hyz hz ht.1 ht.2

theorem middle10_eq {x y : ℝ} (hx : alpha ≤ x) (hxy : x ≤ y) (hy : y ≤ beta) :
    regularMiddle10 x y = ∫ z in y..beta, ∫ t in z..beta, kernel x y z t := by
  apply intervalIntegral.integral_congr
  intro z hz
  rw [uIcc_of_le hy] at hz
  exact inner10_eq hx hxy hz.1 hz.2

theorem middle11_eq {x y : ℝ} (hx : alpha ≤ x) (hxy : x ≤ y) (hy : y ≤ beta) :
    regularMiddle11 x y = ∫ z in y..beta, ∫ t in beta..lam-z, kernel x y z t := by
  apply intervalIntegral.integral_congr
  intro z hz
  rw [uIcc_of_le hy] at hz
  exact inner11_eq hx hxy hz.1 hz.2

theorem outer10_eq {x : ℝ} (hx : x ∈ Icc alpha beta) :
    regularOuter10 x = ∫ y in x..beta, ∫ z in y..beta, ∫ t in z..beta, kernel x y z t := by
  apply intervalIntegral.integral_congr
  intro y hy
  rw [uIcc_of_le hx.2] at hy
  exact middle10_eq hx.1 hy.1 hy.2

theorem outer11_eq {x : ℝ} (hx : x ∈ Icc alpha beta) :
    regularOuter11 x = ∫ y in x..beta, ∫ z in y..beta, ∫ t in beta..lam-z, kernel x y z t := by
  apply intervalIntegral.integral_congr
  intro y hy
  rw [uIcc_of_le hx.2] at hy
  exact middle11_eq hx.1 hy.1 hy.2

theorem I10_eq_regular : I10 = ∫ x in alpha..beta, regularOuter10 x := by
  apply intervalIntegral.integral_congr
  intro x hx
  rw [uIcc_of_le fixed_geometry.2.2.1] at hx
  exact (outer10_eq hx).symm

theorem I11_eq_regular : I11 = ∫ x in alpha..beta, regularOuter11 x := by
  apply intervalIntegral.integral_congr
  intro x hx
  rw [uIcc_of_le fixed_geometry.2.2.1] at hx
  exact (outer11_eq hx).symm

theorem I10_outer_integrable : IntervalIntegrable
    (fun x => ∫ y in x..beta, ∫ z in y..beta, ∫ t in z..beta, kernel x y z t)
    volume alpha beta := by
  apply ContinuousOn.intervalIntegrable
  apply regularOuter10_continuous.continuousOn.congr
  intro x hx
  rw [uIcc_of_le fixed_geometry.2.2.1] at hx
  exact (outer10_eq hx).symm

theorem I11_outer_integrable : IntervalIntegrable
    (fun x => ∫ y in x..beta, ∫ z in y..beta, ∫ t in beta..lam-z, kernel x y z t)
    volume alpha beta := by
  apply ContinuousOn.intervalIntegrable
  apply regularOuter11_continuous.continuousOn.congr
  intro x hx
  rw [uIcc_of_le fixed_geometry.2.2.1] at hx
  exact (outer11_eq hx).symm

theorem regularKernel_nonneg (x y z t : ℝ) : 0 ≤ regularKernel x y z t :=
  div_nonneg (buchstab_nonneg (le_trans (by norm_num) (le_max_left _ _)))
    (mul_nonneg (mul_nonneg (mul_nonneg (clip_pos _).le (sq_nonneg _)) (clip_pos _).le) (clip_pos _).le)

theorem integrals_nonneg : 0 ≤ I10 ∧ 0 ≤ I11 := by
  rw [I10_eq_regular, I11_eq_regular]
  constructor
  · apply intervalIntegral.integral_nonneg fixed_geometry.2.2.1
    intro x hx
    apply intervalIntegral.integral_nonneg hx.2
    intro y hy
    apply intervalIntegral.integral_nonneg hy.2
    intro z hz
    exact intervalIntegral.integral_nonneg_of_forall hz.2 (regularKernel_nonneg x y z)
  · apply intervalIntegral.integral_nonneg fixed_geometry.2.2.1
    intro x hx
    apply intervalIntegral.integral_nonneg hx.2
    intro y hy
    apply intervalIntegral.integral_nonneg hy.2
    intro z hz
    apply intervalIntegral.integral_nonneg_of_forall
      (by linarith [hz.2, fixed_geometry.2.2.2.2.2.2.1])
    exact regularKernel_nonneg x y z

end
end Wu2008DoubleSieve.FourRoughClosedMass
