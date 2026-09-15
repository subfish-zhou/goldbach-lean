import MathlibNt.Wu2008DoubleSieve.NinthErrorPayment
import MathlibNt.Wu2008DoubleSieve.PrimeOrderedQuadratureIntegral

/-!
# The literal ninth main integral and compact kernel

Clipping only extends the first coordinate outside its actual interval.
On the entire ninth triangle the kernel remains exactly 1/(1-t-v).
-/

namespace Wu2008DoubleSieve

open Set Real MeasureTheory
open scoped Classical Topology Interval

noncomputable def ninthMainClip (t : ℝ) : ℝ := min t ninthProfileSigma
noncomputable def ninthMainTop (t : ℝ) : ℝ := (1 - ninthMainClip t) / 2
noncomputable def ninthMainKernel (t v : ℝ) : ℝ := 1 / (1 - ninthMainClip t - v)
noncomputable def ninthMainInner (t : ℝ) : ℝ :=
  ∫ v in ninthProfileSigma..ninthMainTop t, ninthMainKernel t v / v
noncomputable def J9 : ℝ :=
  ∫ t in ninthProfileK2..ninthProfileSigma,
    log ((1 - ninthProfileSigma - t) / ninthProfileSigma) / (t * (1 - t))

theorem ninthMain_parameters :
    (1 / 10 : ℝ) < ninthProfileK2 ∧ ninthProfileK2 < ninthProfileSigma ∧
      (1 / 10 : ℝ) < ninthProfileSigma ∧ ninthProfileSigma < 3 / 10 := by
  norm_num [ninthProfileK2, ninthProfileSigma, ninthProfileK1]

theorem ninthMainClip_bounds {t : ℝ} (ht : t ∈ Icc (1 / 10 : ℝ) (1 / 2)) :
    1 / 10 ≤ ninthMainClip t ∧ ninthMainClip t ≤ ninthProfileSigma := by
  exact ⟨le_min ht.1 ninthMain_parameters.2.2.1.le, min_le_right _ _⟩

theorem ninthMainClip_lipschitz (x y : ℝ) :
    |ninthMainClip x - ninthMainClip y| ≤ |x - y| := by
  unfold ninthMainClip
  by_cases hx : x ≤ ninthProfileSigma <;> by_cases hy : y ≤ ninthProfileSigma
  · simp only [min_eq_left hx, min_eq_left hy, le_refl]
  · rw [min_eq_left hx, min_eq_right (le_of_not_ge hy)]
    rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
    linarith
  · rw [min_eq_right (le_of_not_ge hx), min_eq_left hy]
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    linarith
  · simp only [min_eq_right (le_of_not_ge hx), min_eq_right (le_of_not_ge hy),
      sub_self, abs_zero, abs_nonneg]

theorem ninthMainTop_bounds {t : ℝ} (ht : t ∈ Icc (1 / 10 : ℝ) (1 / 2)) :
    ninthProfileSigma ≤ ninthMainTop t ∧ ninthMainTop t ∈ Icc (1 / 10 : ℝ) (1 / 2) := by
  have h := ninthMainClip_bounds ht
  have hs := ninthMain_parameters
  unfold ninthMainTop
  exact ⟨by linarith, by constructor <;> linarith⟩

theorem ninthMainKernel_den_pos {t v : ℝ}
    (ht : t ∈ Icc (1 / 10 : ℝ) (1 / 2)) (hv : v ∈ Icc (1 / 10 : ℝ) (1 / 2)) :
    1 / 5 ≤ 1 - ninthMainClip t - v := by
  have h := ninthMainClip_bounds ht
  have hs := ninthMain_parameters
  linarith [hv.2]

theorem ninthMainKernel_bound {t v : ℝ}
    (ht : t ∈ Icc (1 / 10 : ℝ) (1 / 2)) (hv : v ∈ Icc (1 / 10 : ℝ) (1 / 2)) :
    0 ≤ ninthMainKernel t v ∧ |ninthMainKernel t v| ≤ 5 := by
  have hd := ninthMainKernel_den_pos ht hv
  have hp : 0 ≤ ninthMainKernel t v := one_div_nonneg.mpr (by linarith)
  refine ⟨hp, ?_⟩
  rw [abs_of_nonneg hp]
  exact (div_le_iff₀ (by linarith : 0 < 1 - ninthMainClip t - v)).mpr (by linarith)

theorem ninthMain_inverse_lipschitz {d e : ℝ} (hd : 1 / 5 ≤ d) (he : 1 / 5 ≤ e) :
    |1 / d - 1 / e| ≤ 25 * |d - e| := by
  have hd0 : 0 < d := by linarith
  have he0 : 0 < e := by linarith
  have hde : 1 / 25 ≤ d * e := by nlinarith
  rw [div_sub_div _ _ hd0.ne' he0.ne']
  simp only [one_mul, mul_one, abs_div, abs_of_pos (mul_pos hd0 he0), abs_sub_comm e d]
  apply (div_le_iff₀ (mul_pos hd0 he0)).mpr
  nlinarith [abs_nonneg (d - e),
    mul_le_mul_of_nonneg_left hde (abs_nonneg (d - e))]

theorem ninthMainKernel_lipschitz_second {t x y : ℝ}
    (ht : t ∈ Icc (1 / 10 : ℝ) (1 / 2))
    (hx : x ∈ Icc (1 / 10 : ℝ) (1 / 2)) (hy : y ∈ Icc (1 / 10 : ℝ) (1 / 2)) :
    |ninthMainKernel t x - ninthMainKernel t y| ≤ 25 * |x - y| := by
  have h := ninthMain_inverse_lipschitz (ninthMainKernel_den_pos ht hx)
    (ninthMainKernel_den_pos ht hy)
  rw [show (1 - ninthMainClip t - x) - (1 - ninthMainClip t - y) = y - x by ring,
    abs_sub_comm y x] at h
  exact h

theorem ninthMainKernel_lipschitz_first {x y v : ℝ}
    (hx : x ∈ Icc (1 / 10 : ℝ) (1 / 2)) (hy : y ∈ Icc (1 / 10 : ℝ) (1 / 2))
    (hv : v ∈ Icc (1 / 10 : ℝ) (1 / 2)) :
    |ninthMainKernel x v - ninthMainKernel y v| ≤ 25 * |x - y| := by
  have h := ninthMain_inverse_lipschitz (ninthMainKernel_den_pos hx hv)
    (ninthMainKernel_den_pos hy hv)
  rw [show (1 - ninthMainClip x - v) - (1 - ninthMainClip y - v) =
    ninthMainClip y - ninthMainClip x by ring,
    abs_sub_comm (ninthMainClip y) (ninthMainClip x)] at h
  exact h.trans (mul_le_mul_of_nonneg_left (ninthMainClip_lipschitz x y) (by norm_num))

theorem ninthMainKernel_continuous {t : ℝ} (ht : t ∈ Icc (1 / 10 : ℝ) (1 / 2)) :
    ContinuousOn (ninthMainKernel t) (Icc (1 / 10 : ℝ) (1 / 2)) :=
  primeOrdered_continuous_of_lipschitz (fun _ hx _ hy => ninthMainKernel_lipschitz_second ht hx hy)

theorem ninthMainInner_regular :
    (∀ t ∈ Icc (1 / 10 : ℝ) (1 / 2), |ninthMainInner t| ≤ 20) ∧
    (∀ x ∈ Icc (1 / 10 : ℝ) (1 / 2), ∀ y ∈ Icc (1 / 10 : ℝ) (1 / 2),
      |ninthMainInner x - ninthMainInner y| ≤ 125 * |x - y|) := by
  have hs : ninthProfileSigma ∈ Icc (1 / 10 : ℝ) (1 / 2) := by
    have h := ninthMain_parameters
    constructor <;> linarith
  constructor
  · intro t ht
    simpa only [ninthMainInner, show (4 : ℝ) * 5 = 20 by norm_num] using
      primeOrdered_integral_norm_le_four hs (ninthMainTop_bounds ht).2 (by norm_num)
        (fun v hv => (ninthMainKernel_bound ht hv).2)
  · intro x hx y hy
    have h1 := primeOrdered_integral_sub_bound
      (ninthMainKernel_continuous hx) (ninthMainKernel_continuous hy)
      hs (ninthMainTop_bounds hx).2 (by positivity : 0 ≤ 25 * |x - y|)
      (fun v hv => ninthMainKernel_lipschitz_first hx hy hv)
    have h2 := primeOrdered_integral_norm_le (ninthMainTop_bounds hy).2
      (ninthMainTop_bounds hx).2 (fun v hv => (ninthMainKernel_bound hy hv).2)
    have hadd := intervalIntegral.integral_add_adjacent_intervals
      (primeOrdered_integrable (ninthMainKernel_continuous hy) hs (ninthMainTop_bounds hy).2)
      (primeOrdered_integrable (ninthMainKernel_continuous hy)
        (ninthMainTop_bounds hy).2 (ninthMainTop_bounds hx).2)
    have htop : |ninthMainTop x - ninthMainTop y| ≤ |x - y| / 2 := by
      unfold ninthMainTop
      rw [← sub_div, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      rw [show (1 - ninthMainClip x) - (1 - ninthMainClip y) =
        ninthMainClip y - ninthMainClip x by ring, abs_sub_comm]
      exact div_le_div_of_nonneg_right (ninthMainClip_lipschitz x y) (by norm_num)
    have htri := abs_sub_le
      (∫ v in ninthProfileSigma..ninthMainTop x, ninthMainKernel x v / v)
      (∫ v in ninthProfileSigma..ninthMainTop x, ninthMainKernel y v / v)
      (∫ v in ninthProfileSigma..ninthMainTop y, ninthMainKernel y v / v)
    have heq :
        (∫ v in ninthProfileSigma..ninthMainTop x, ninthMainKernel y v / v) -
        (∫ v in ninthProfileSigma..ninthMainTop y, ninthMainKernel y v / v) =
        ∫ v in ninthMainTop y..ninthMainTop x, ninthMainKernel y v / v := by linarith
    rw [heq] at htri
    change |ninthMainInner x - ninthMainInner y| ≤ _
    dsimp only [ninthMainInner]
    nlinarith

theorem ninthMainInner_continuous :
    ContinuousOn ninthMainInner (Icc (1 / 10 : ℝ) (1 / 2)) :=
  primeOrdered_continuous_of_lipschitz ninthMainInner_regular.2

/-- Exact evaluation of the inner triangle integral, not numerical integration. -/
theorem ninthMainInner_eq {t : ℝ} (ht : t ∈ Icc ninthProfileK2 ninthProfileSigma) :
    ninthMainInner t =
      log ((1 - ninthProfileSigma - t) / ninthProfileSigma) / (1 - t) := by
  have hp := ninthMain_parameters
  have htmem : t ∈ Icc (1 / 10 : ℝ) (1 / 2) := by constructor <;> linarith [ht.1, ht.2]
  have hs0 : 0 < ninthProfileSigma := by linarith
  have ht0 : 0 < 1 - t := by linarith [ht.2]
  have htop : ninthMainTop t = (1 - t) / 2 := by simp only [ninthMainTop, ninthMainClip, min_eq_left ht.2]
  have hlow : ninthProfileSigma ≤ (1 - t) / 2 := by linarith [ht.2]
  have hden : 0 < 1 - t - ninthProfileSigma := by linarith [ht.2]
  have hd : ∀ v ∈ uIcc ninthProfileSigma ((1 - t) / 2),
      HasDerivAt (fun v => (log v - log (1 - t - v)) / (1 - t))
        (1 / (1 - t - v) / v) v := by
    intro v hv
    rw [uIcc_of_le hlow] at hv
    have hv0 : 0 < v := hs0.trans_le hv.1
    have hvd : 0 < 1 - t - v := by linarith [hv.2]
    have h := ((hasDerivAt_log hv0.ne').sub
      (((hasDerivAt_const v (1 - t)).sub (hasDerivAt_id v)).log hvd.ne')).div_const (1 - t)
    dsimp only [Pi.sub_apply, id_eq] at h
    convert h using 1 <;> first | rfl | (field_simp; ring)
  have hi : IntervalIntegrable (fun v => 1 / (1 - t - v) / v) volume
      ninthProfileSigma ((1 - t) / 2) := by
    have h := primeOrdered_integrable (ninthMainKernel_continuous htmem)
      (show ninthProfileSigma ∈ Icc (1 / 10 : ℝ) (1 / 2) by constructor <;> linarith)
      (ninthMainTop_bounds htmem).2
    simpa only [ninthMainKernel, ninthMainClip, min_eq_left ht.2, htop] using h
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi
  unfold ninthMainInner
  simp only [ninthMainKernel, ninthMainClip, min_eq_left ht.2, htop]
  rw [he, show 1 - t - (1 - t) / 2 = (1 - t) / 2 by ring, sub_self, zero_div, zero_sub]
  rw [log_div (by linarith : 1 - ninthProfileSigma - t ≠ 0) hs0.ne']
  rw [show 1 - t - ninthProfileSigma = 1 - ninthProfileSigma - t by ring]
  ring

theorem J9_integrable :
    IntervalIntegrable
      (fun t => log ((1 - ninthProfileSigma - t) / ninthProfileSigma) / (t * (1 - t)))
      volume ninthProfileK2 ninthProfileSigma := by
  have hp := ninthMain_parameters
  have h := primeOrdered_integrable ninthMainInner_continuous
    (show ninthProfileK2 ∈ Icc (1 / 10 : ℝ) (1 / 2) by constructor <;> linarith)
    (show ninthProfileSigma ∈ Icc (1 / 10 : ℝ) (1 / 2) by constructor <;> linarith)
  apply h.congr
  intro t ht
  have ht := uIoc_subset_uIcc ht
  rw [uIcc_of_le hp.2.1.le] at ht
  dsimp only
  rw [ninthMainInner_eq ht]
  rw [div_div, mul_comm (1 - t) t]

theorem J9_eq_iterated :
    J9 = ∫ t in ninthProfileK2..ninthProfileSigma, ninthMainInner t / t := by
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le ninthMain_parameters.2.1.le] at ht
  dsimp only
  rw [ninthMainInner_eq ht]
  rw [div_div, mul_comm (1 - t) t]

theorem J9_eq_triangle_integral :
    J9 = ∫ t in ninthProfileK2..ninthProfileSigma,
      ∫ v in ninthProfileSigma..((1 - t) / 2), 1 / (t * v * (1 - t - v)) := by
  rw [J9_eq_iterated]
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le ninthMain_parameters.2.1.le] at ht
  dsimp only
  unfold ninthMainInner
  simp only [ninthMainTop, ninthMainKernel, ninthMainClip, min_eq_left ht.2]
  rw [← intervalIntegral.integral_div]
  apply intervalIntegral.integral_congr
  intro v _
  dsimp only
  simp only [div_div]
  congr 1
  ring

theorem J9_nonneg : 0 ≤ J9 := by
  apply intervalIntegral.integral_nonneg ninthMain_parameters.2.1.le
  intro t ht
  have hp := ninthMain_parameters
  have hs : 0 < ninthProfileSigma := by linarith
  have hratio : 1 ≤ (1 - ninthProfileSigma - t) / ninthProfileSigma := by
    apply (le_div_iff₀ hs).mpr
    linarith [ht.2]
  exact div_nonneg (log_nonneg hratio) (mul_nonneg (by linarith [ht.1]) (by linarith [ht.2]))

end Wu2008DoubleSieve
