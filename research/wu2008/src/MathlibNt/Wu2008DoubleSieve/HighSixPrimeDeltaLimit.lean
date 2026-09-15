import MathlibNt.Wu2008DoubleSieve.HighSixPsiActualCount

namespace Wu2008DoubleSieve.HighSixDeltaLimit
open Set Real Filter MeasureTheory
open scoped Topology

/-- A continuous extension of just the fixed-window rational prime kernel. -/
noncomputable def regularPrimeKernel (δ t : ℝ) : ℝ :=
  1 / (max (1/10 : ℝ) t * max (1/10 : ℝ) (1/2-δ-t))

 theorem regularPrimeKernel_continuous :
    Continuous (Function.uncurry regularPrimeKernel) := by
  apply Continuous.div continuous_const (by fun_prop)
  intro x
  exact (mul_pos (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1/10) (le_max_left _ _))
    (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1/10) (le_max_left _ _))).ne'

 theorem regularPrimeKernel_eq {δ t : ℝ} (hδ : δ ≤ 1/100)
    (ht : t ∈ Icc HighSix.left HighSix.right) :
    regularPrimeKernel δ t = 1/(t*(1/2-δ-t)) := by
  have h1 : (1/10 : ℝ) ≤ t := by norm_num [HighSix.left] at ht; linarith [ht.1]
  have h2 : (1/10 : ℝ) ≤ 1/2-δ-t := by
    norm_num [HighSix.right] at ht; linarith [ht.2]
  simp only [regularPrimeKernel, max_eq_right h1, max_eq_right h2]

 theorem prime_kernel_integrable {δ : ℝ} (hδ : δ ≤ 1/100) :
    IntervalIntegrable (fun t : ℝ => 1/(t*(1/2-δ-t))) volume
      HighSix.left HighSix.right := by
  have hc : Continuous (regularPrimeKernel δ) :=
    regularPrimeKernel_continuous.comp (continuous_const.prodMk continuous_id)
  apply (hc.intervalIntegrable HighSix.left HighSix.right).congr
  intro t ht
  rw [uIoc_of_le (by norm_num [HighSix.left, HighSix.right])] at ht
  exact regularPrimeKernel_eq hδ ⟨ht.1.le, ht.2⟩

noncomputable def primeExtension (δ : ℝ) : ℝ :=
  ∫ t in HighSix.left..HighSix.right, regularPrimeKernel δ t

 theorem primeExtension_continuous : Continuous primeExtension :=
  gamma5Gain_moving_integral regularPrimeKernel_continuous continuous_const continuous_const

 theorem primeExtension_eq {δ : ℝ} (hδ : δ ≤ 1/100) :
    primeExtension δ = HighSix.primeIntegral δ := by
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le (by norm_num [HighSix.left, HighSix.right])] at ht
  exact regularPrimeKernel_eq hδ ht

/-- The genuine original prime integral tends to its delta-zero value. -/
 theorem primeIntegral_right_limit :
    Tendsto HighSix.primeIntegral (𝓝[>] (0 : ℝ)) (𝓝 (HighSix.primeIntegral 0)) := by
  have h := primeExtension_continuous.continuousAt.tendsto (x := (0 : ℝ))
  rw [primeExtension_eq (by norm_num)] at h
  apply (h.mono_left nhdsWithin_le_nhds).congr'
  have he : ∀ᶠ δ : ℝ in 𝓝[>] 0, δ < 1/100 :=
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1/100)).filter_mono nhdsWithin_le_nhds
  filter_upwards [he] with δ hδ
  exact primeExtension_eq hδ.le

 theorem primeIntegral_close {ε : ℝ} (hε : 0 < ε) :
    ∃ a : ℝ, 0 < a ∧ a ≤ 1/100 ∧ ∀ δ : ℝ,
      0 < δ → δ < a → |HighSix.primeIntegral δ-HighSix.primeIntegral 0| < ε := by
  obtain ⟨a, ha, hb⟩ := Metric.tendsto_nhdsWithin_nhds.mp primeIntegral_right_limit ε hε
  refine ⟨min a (1/100), lt_min ha (by norm_num), min_le_right _ _, ?_⟩
  intro δ hδ hδa
  apply hb hδ
  simpa only [Real.dist_eq, sub_zero, abs_of_pos hδ] using
    hδa.trans_le (min_le_left a (1/100))

end Wu2008DoubleSieve.HighSixDeltaLimit
