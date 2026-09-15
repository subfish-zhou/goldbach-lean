import MathlibNt.Wu2008DoubleSieve.SingleUpperNormalization

namespace Wu2008DoubleSieve.SingleUpperClassicalLimit
open Set Real Filter MeasureTheory
open scoped Classical Topology

/-- The requested classical coefficient, with the full original t-window. -/
noncomputable def Gdelta (δ r : ℝ) : ℝ :=
  4 * ∫ t in truncatedSixthLowerAlpha..r,
    wuUpperCoefficient (((1/2-δ)-t)/truncatedSixthLowerAlpha) / (t*((1/2-δ)-t))

noncomputable def Glin (r : ℝ) : ℝ := Gdelta 0 r

/-- A global continuous extension used only to justify parameter integration.
It agrees pointwise on the original rectangle, including delta zero. -/
noncomputable def regularKernel (δ t : ℝ) : ℝ :=
  wuUpperCoefficient (max 1 (((1/2-δ)-t)/truncatedSixthLowerAlpha)) /
    (max (truncatedSixthLowerAlpha/2) t * max (1/10 : ℝ) ((1/2-δ)-t))

noncomputable def extension (δ r : ℝ) : ℝ :=
  4 * ∫ t in truncatedSixthLowerAlpha..r, regularKernel δ t

 theorem regular_continuous : Continuous (Function.uncurry regularKernel) := by
  have hA : Continuous (fun x : ℝ × ℝ =>
      wuUpperCoefficient (max 1 (((1/2-x.1)-x.2)/truncatedSixthLowerAlpha))) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    have ha : ContinuousAt wuUpperCoefficient
        (max 1 (((1/2-x.1)-x.2)/truncatedSixthLowerAlpha)) :=
      continuousOn_wuUpperCoefficient.continuousAt (isOpen_Ioi.mem_nhds
        (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_left _ _)))
    exact ha.comp (f := fun x : ℝ × ℝ => max 1 (((1/2-x.1)-x.2)/truncatedSixthLowerAlpha))
      (by fun_prop)
  have hd (x : ℝ × ℝ) :
      max (truncatedSixthLowerAlpha/2) x.2 * max (1/10 : ℝ) ((1/2-x.1)-x.2) ≠ 0 := by
    apply (mul_pos (lt_of_lt_of_le (by norm_num [truncatedSixthLowerAlpha] :
        0 < truncatedSixthLowerAlpha/2) (le_max_left _ _))
      (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1/10) (le_max_left _ _))).ne'
  exact hA.div (by fun_prop) hd

 theorem regular_eq {δ t : ℝ} (hδ : δ ≤ 1/100)
    (ht : t ∈ Icc truncatedSixthLowerAlpha (1/3 : ℝ)) :
    regularKernel δ t =
      wuUpperCoefficient (((1/2-δ)-t)/truncatedSixthLowerAlpha) / (t*((1/2-δ)-t)) := by
  have ha : 0 < truncatedSixthLowerAlpha := by norm_num [truncatedSixthLowerAlpha]
  have hs : 1 ≤ ((1/2-δ)-t)/truncatedSixthLowerAlpha := by
    apply (le_div_iff₀ ha).mpr
    norm_num [truncatedSixthLowerAlpha] at *
    linarith [ht.2]
  have ht0 : truncatedSixthLowerAlpha/2 ≤ t := by linarith [ht.1]
  have hc : (1/10 : ℝ) ≤ (1/2-δ)-t := by linarith [ht.2]
  simp only [regularKernel, max_eq_right hs, max_eq_right ht0, max_eq_right hc]

 theorem extension_eq {δ r : ℝ} (hδ : δ ≤ 1/100)
    (hr : truncatedSixthLowerAlpha ≤ r) (hrhi : r ≤ 1/3) :
    extension δ r = Gdelta δ r := by
  unfold extension Gdelta
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ Icc truncatedSixthLowerAlpha r := by
    simpa only [uIcc_of_le hr] using ht
  exact regular_eq hδ ⟨ht'.1, ht'.2.trans hrhi⟩

 theorem extension_continuous (r : ℝ) : Continuous (fun δ => extension δ r) := by
  exact (gamma5Gain_moving_integral regular_continuous continuous_const continuous_const).const_mul 4

/-- Classical delta-to-zero continuity uses only A, never an H-regularity premise. -/
theorem Gdelta_right_limit {r : ℝ}
    (hr : truncatedSixthLowerAlpha ≤ r) (hrhi : r ≤ 1/3) :
    Tendsto (fun δ => Gdelta δ r) (𝓝[>] (0 : ℝ)) (𝓝 (Glin r)) := by
  have ht := (extension_continuous r).continuousAt.tendsto (x := (0 : ℝ))
  rw [extension_eq (by norm_num) hr hrhi] at ht
  change Tendsto (fun δ => extension δ r) (𝓝 0) (𝓝 (Glin r)) at ht
  apply (ht.mono_left nhdsWithin_le_nhds).congr'
  have he : ∀ᶠ δ : ℝ in 𝓝[>] 0, δ < 1/100 :=
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1/100)).filter_mono nhdsWithin_le_nhds
  filter_upwards [he] with δ hδ
  exact extension_eq hδ.le hr hrhi

 theorem Gdelta_close {r ε : ℝ} (hr : truncatedSixthLowerAlpha ≤ r)
    (hrhi : r ≤ 1/3) (hε : 0 < ε) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1/100 ∧
      ∀ δ : ℝ, 0 < δ → δ < δ0 → |Gdelta δ r-Glin r| < ε := by
  obtain ⟨a, ha, hb⟩ := Metric.tendsto_nhdsWithin_nhds.mp (Gdelta_right_limit hr hrhi) ε hε
  refine ⟨min a (1/100), lt_min ha (by norm_num), min_le_right _ _, ?_⟩
  intro δ hδ hδ0
  have hd : dist δ 0 < a := by
    simpa only [Real.dist_eq, sub_zero, abs_of_pos hδ] using hδ0.trans_le (min_le_left _ _)
  exact hb hδ hd

/-- Both classical windows admit a single genuinely positive delta chosen
before the arithmetic threshold; overlapping integrals are added twice. -/
theorem choose_common_delta {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1/100 ∧
      Gdelta δ (1/3)+Gdelta δ truncatedSixthLowerSigma <
        Glin (1/3)+Glin truncatedSixthLowerSigma+ε := by
  have ha : truncatedSixthLowerAlpha ≤ (1/3 : ℝ) := by norm_num [truncatedSixthLowerAlpha]
  have hs : truncatedSixthLowerAlpha ≤ truncatedSixthLowerSigma := by
    norm_num [truncatedSixthLowerAlpha, truncatedSixthLowerSigma]
  have hs3 : truncatedSixthLowerSigma ≤ (1/3 : ℝ) := by
    norm_num [truncatedSixthLowerAlpha, truncatedSixthLowerSigma]
  obtain ⟨a, ha0, ha1, hA⟩ := Gdelta_close ha le_rfl (half_pos hε)
  obtain ⟨b, hb0, _, hB⟩ := Gdelta_close hs hs3 (half_pos hε)
  let δ := min a b/2
  have hδ : 0 < δ := half_pos (lt_min ha0 hb0)
  have hδa : δ < a := lt_of_lt_of_le (half_lt_self (lt_min ha0 hb0)) (min_le_left _ _)
  have hδb : δ < b := lt_of_lt_of_le (half_lt_self (lt_min ha0 hb0)) (min_le_right _ _)
  refine ⟨δ, hδ, hδa.le.trans ha1, ?_⟩
  have h1 := (abs_lt.mp (hA δ hδ hδa)).2
  have h2 := (abs_lt.mp (hB δ hδ hδb)).2
  linarith

end Wu2008DoubleSieve.SingleUpperClassicalLimit
