import MathlibNt.Wu2008DoubleSieve.Gamma16Carriers
import MathlibNt.Wu2008DoubleSieve.PrimeOrderedQuadratureBuchstab

/-! # The clipped full-cube fourth-row Buchstab kernel -/

namespace Wu2008DoubleSieve

open Set Real LiLiuPrereqBuchstab

noncomputable def gamma16Kernel (φ t u v w : ℝ) : ℝ :=
  buchstab ((φ - t - u - v - w) / v) / v

noncomputable def gamma16Clip (x : ℝ) : ℝ := max gamma16Alpha (min gamma16Beta x)

noncomputable def gamma16ClippedKernel (φ w t u v : ℝ) : ℝ :=
  gamma16Kernel φ (gamma16Clip t) (gamma16Clip u) (gamma16Clip v) (gamma16Clip w)

theorem gamma16_constants :
    1 / 10 ≤ gamma16Alpha ∧ gamma16Alpha ≤ gamma16Beta ∧
      gamma16Beta ≤ 1 / 2 ∧ 5 * gamma16Beta = 2 := by
  norm_num [gamma16Alpha, gamma16Beta]

theorem gamma16_clip_mem (x : ℝ) : gamma16Clip x ∈ Icc gamma16Alpha gamma16Beta :=
  ⟨le_max_left _ _, max_le gamma16_constants.2.1 (min_le_left _ _)⟩

theorem gamma16_clip_eq {x : ℝ} (hx : x ∈ Icc gamma16Alpha gamma16Beta) :
    gamma16Clip x = x := by
  simp only [gamma16Clip, min_eq_right hx.2, max_eq_right hx.1]

theorem gamma16_clip_lipschitz (x y : ℝ) : |gamma16Clip x - gamma16Clip y| ≤ |x - y| := by
  have h : LipschitzWith 1 gamma16Clip :=
    (LipschitzWith.id.const_min gamma16Beta).const_max gamma16Alpha
  simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using h.dist_le_mul x y

theorem gamma16_argument_one {φ t u v w : ℝ} (hφ : 2 ≤ φ)
    (ht : t ∈ Icc gamma16Alpha gamma16Beta)
    (hu : u ∈ Icc gamma16Alpha gamma16Beta)
    (hv : v ∈ Icc gamma16Alpha gamma16Beta)
    (hw : w ∈ Icc gamma16Alpha gamma16Beta) :
    1 ≤ (φ - t - u - v - w) / v := by
  apply (le_div_iff₀ (by linarith [gamma16_constants.1, hv.1] : 0 < v)).mpr
  linarith [ht.2, hu.2, hv.2, hw.2, gamma16_constants.2.2.2]

theorem gamma16_kernel_nonneg {φ t u v w : ℝ} (hφ : 2 ≤ φ)
    (ht : t ∈ Icc gamma16Alpha gamma16Beta)
    (hu : u ∈ Icc gamma16Alpha gamma16Beta)
    (hv : v ∈ Icc gamma16Alpha gamma16Beta)
    (hw : w ∈ Icc gamma16Alpha gamma16Beta) :
    0 ≤ gamma16Kernel φ t u v w :=
  div_nonneg (buchstab_nonneg (gamma16_argument_one hφ ht hu hv hw))
    (by linarith [gamma16_constants.1, hv.1])

theorem gamma16_kernel_bound {φ t u v w : ℝ} (hφ : 2 ≤ φ)
    (ht : t ∈ Icc gamma16Alpha gamma16Beta)
    (hu : u ∈ Icc gamma16Alpha gamma16Beta)
    (hv : v ∈ Icc gamma16Alpha gamma16Beta)
    (hw : w ∈ Icc gamma16Alpha gamma16Beta) :
    |gamma16Kernel φ t u v w| ≤ 10 := by
  rw [abs_of_nonneg (gamma16_kernel_nonneg hφ ht hu hv hw)]
  unfold gamma16Kernel
  apply (div_le_div_of_nonneg_right
    (buchstab_le_one (gamma16_argument_one hφ ht hu hv hw))
    (by linarith [gamma16_constants.1, hv.1] : 0 ≤ v)).trans
  apply (div_le_iff₀ (by linarith [gamma16_constants.1, hv.1] : 0 < v)).mpr
  linarith [gamma16_constants.1, hv.1]

private theorem quotient_difference {x y b d T : ℝ}
    (hb : 1 / 10 ≤ b) (hd : 1 / 10 ≤ d) (hy : |y| ≤ T) :
    |x / b - y / d| ≤ 10 * |x - y| + 100 * T * |b - d| := by
  have hb0 : 0 < b := by linarith
  have hd0 : 0 < d := by linarith
  have hT : 0 ≤ T := (abs_nonneg y).trans hy
  have he : x / b - y / d = (x - y) / b + y * (d - b) / (b * d) := by
    field_simp
    ring
  rw [he]
  have h₁ : |x - y| / b ≤ 10 * |x - y| := by
    apply (div_le_iff₀ hb0).mpr
    nlinarith [abs_nonneg (x - y)]
  have hprod : 1 / 100 ≤ b * d := by nlinarith
  have h₂ : |y| * |d - b| / (b * d) ≤ 100 * T * |b - d| := by
    rw [abs_sub_comm d b]
    apply (div_le_iff₀ (mul_pos hb0 hd0)).mpr
    have hyy := mul_le_mul_of_nonneg_right hy (abs_nonneg (b - d))
    have hh := mul_le_mul_of_nonneg_left hprod
      (show 0 ≤ 100 * T * |b - d| by positivity)
    nlinarith
  have hh := abs_add_le ((x - y) / b) (y * (d - b) / (b * d))
  rw [abs_div, abs_of_pos hb0, abs_div, abs_mul, abs_of_pos (mul_pos hb0 hd0)] at hh
  linarith only [h₁, h₂, hh]

theorem gamma16_kernel_lipschitz {P φ t u v w t' u' v' w' : ℝ}
    (hφ : 2 ≤ φ) (hP : φ ≤ P)
    (ht : t ∈ Icc gamma16Alpha gamma16Beta)
    (hu : u ∈ Icc gamma16Alpha gamma16Beta)
    (hv : v ∈ Icc gamma16Alpha gamma16Beta)
    (hw : w ∈ Icc gamma16Alpha gamma16Beta)
    (ht' : t' ∈ Icc gamma16Alpha gamma16Beta)
    (hu' : u' ∈ Icc gamma16Alpha gamma16Beta)
    (hv' : v' ∈ Icc gamma16Alpha gamma16Beta)
    (hw' : w' ∈ Icc gamma16Alpha gamma16Beta) :
    |gamma16Kernel φ t u v w - gamma16Kernel φ t' u' v' w'| ≤
      (1000 * P + 200) * (|t - t'| + |u - u'| + |v - v'| + |w - w'|) := by
  have hP0 : 0 ≤ P := by linarith
  have harg := gamma16_argument_one hφ ht hu hv hw
  have harg' := gamma16_argument_one hφ ht' hu' hv' hw'
  have hnum : |φ - t' - u' - v' - w'| ≤ P := by
    rw [abs_of_nonneg (by linarith [ht'.2, hu'.2, hv'.2, hw'.2,
      gamma16_constants.2.2.2])]
    linarith [ht'.1, hu'.1, hv'.1, hw'.1, gamma16_constants.1]
  have hdiff : |(φ - t - u - v - w) - (φ - t' - u' - v' - w')| ≤
      |t - t'| + |u - u'| + |v - v'| + |w - w'| := by
    rw [show (φ - t - u - v - w) - (φ - t' - u' - v' - w') =
      -((t - t') + (u - u') + (v - v') + (w - w')) by ring, abs_neg]
    linarith [abs_add_le (t - t') (u - u'),
      abs_add_le ((t - t') + (u - u')) (v - v'),
      abs_add_le ((t - t') + (u - u') + (v - v')) (w - w')]
  have hq := quotient_difference (gamma16_constants.1.trans hv.1)
    (gamma16_constants.1.trans hv'.1) hnum (x := φ - t - u - v - w)
  have hω := (primeOrdered_buchstab_lipschitz harg harg').trans hq
  have hωbound : |buchstab ((φ - t' - u' - v' - w') / v')| ≤ 1 := by
    rw [abs_of_nonneg (buchstab_nonneg harg')]
    exact buchstab_le_one harg'
  have hfinal := quotient_difference (gamma16_constants.1.trans hv.1)
    (gamma16_constants.1.trans hv'.1) hωbound
    (x := buchstab ((φ - t - u - v - w) / v))
  dsimp only [gamma16Kernel]
  nlinarith [abs_nonneg (t - t'), abs_nonneg (u - u'), abs_nonneg (w - w'),
    mul_nonneg hP0 (abs_nonneg (t - t')), mul_nonneg hP0 (abs_nonneg (u - u')),
    mul_nonneg hP0 (abs_nonneg (w - w'))]

theorem gamma16_clipped_weight {P φ : ℝ} (hφ : 2 ≤ φ) (hP : φ ≤ P) (w : ℝ) :
    PrimeOrderedWeight 10 (1000 * P + 200) (gamma16ClippedKernel φ w) := by
  have hK : 0 ≤ 1000 * P + 200 := by linarith
  have h (t u v w t' u' v' w' : ℝ) := gamma16_kernel_lipschitz hφ hP
    (gamma16_clip_mem t) (gamma16_clip_mem u) (gamma16_clip_mem v) (gamma16_clip_mem w)
    (gamma16_clip_mem t') (gamma16_clip_mem u') (gamma16_clip_mem v') (gamma16_clip_mem w')
  constructor
  · intro t _ u _ v _
    exact gamma16_kernel_bound hφ (gamma16_clip_mem t) (gamma16_clip_mem u)
      (gamma16_clip_mem v) (gamma16_clip_mem w)
  · intro t _ t' _ u _ v _
    have hh := h t u v w t' u v w
    simp only [sub_self, abs_zero, add_zero] at hh
    exact hh.trans
      (mul_le_mul_of_nonneg_left (gamma16_clip_lipschitz t t') hK)
  · intro t _ u _ u' _ v _
    have hh := h t u v w t u' v w
    simp only [sub_self, abs_zero, add_zero, zero_add] at hh
    exact hh.trans
      (mul_le_mul_of_nonneg_left (gamma16_clip_lipschitz u u') hK)
  · intro t _ u _ v _ v' _
    have hh := h t u v w t u v' w
    simp only [sub_self, abs_zero, add_zero, zero_add] at hh
    exact hh.trans
      (mul_le_mul_of_nonneg_left (gamma16_clip_lipschitz v v') hK)

theorem gamma16_clipped_fourth {P φ : ℝ} (hφ : 2 ≤ φ) (hP : φ ≤ P)
    (t u v w w' : ℝ) :
    |gamma16ClippedKernel φ w t u v - gamma16ClippedKernel φ w' t u v| ≤
      (1000 * P + 200) * |w - w'| := by
  have h := gamma16_kernel_lipschitz hφ hP
    (gamma16_clip_mem t) (gamma16_clip_mem u) (gamma16_clip_mem v) (gamma16_clip_mem w)
    (gamma16_clip_mem t) (gamma16_clip_mem u) (gamma16_clip_mem v) (gamma16_clip_mem w')
  simp only [sub_self, abs_zero, zero_add] at h
  exact h.trans
    (mul_le_mul_of_nonneg_left (gamma16_clip_lipschitz w w') (by linarith))

end Wu2008DoubleSieve
