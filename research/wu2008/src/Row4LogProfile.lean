import MiddleCorrelatedActual

noncomputable section
open Real Set MeasureTheory Wu2008DoubleSieve
open SecondFunctionalParameters SecondFunctionalSignedCore SecondFunctionalRationalCost
open scoped Interval

namespace Row4LogProfile

/-- The complete already-proved positive-source expression, without rounding. -/
def positiveSource (a b : ℝ) : ℝ :=
  -(3-a)^2*(1/36+1/(3*(2*a-3)*(a-1))) +
    (2/a)*(1-2/(b-1)-(a-2)*((((b-1)/2)^2-1)/(2*((b-1)/2))))

/-- Both original positive sources, directed signed cost, and original delta endpoint. -/
def sourceD : ℝ := positiveSource row4.s row4.S +
  positiveSource row4.kappa3 row4.kappa1 -
  (3-row4.kappa2)^2/(2*(row4.kappa2-2)*(row4.kappa2-1)) -
  (2/(1-2*(1/1000)))*(31667784024997/755387500000000)

def H0 : ℝ := sourceD/5

theorem source_margin : (1/60 : ℝ) < sourceD := by
  norm_num [sourceD, positiveSource, row4]

theorem H0_margin : (1/300 : ℝ) < H0 := by
  unfold H0
  linarith only [source_margin]

theorem H0_pos : 0 < H0 := by linarith only [H0_margin]

theorem actual_D_lower {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/1000) :
    sourceD < D row4 δ := by
  have hd : 0 < 1-2*δ := by linarith
  have hS := positiveKernel_original_strict_lower (a := row4.s) (b := row4.S)
    (by norm_num [row4]) (by norm_num [row4])
    (by norm_num [row4]) (by norm_num [row4])
  have hk := positiveKernel_original_strict_lower (a := row4.kappa3) (b := row4.kappa1)
    (by norm_num [row4]) (by norm_num [row4])
    (by norm_num [row4]) (by norm_num [row4])
  have hl := directedL_upper (c := row4.kappa2)
    (by norm_num [row4]) (by norm_num [row4])
  have hp0 : 0 ≤ 2/(1-2*δ) := by positivity
  have hp1 : 2/(1-2*δ) ≤ (2 : ℝ)/(1-2*(1/1000)) := by
    apply div_le_div_of_nonneg_left (by norm_num) (by linarith) (by linarith)
  have hcost := (mul_le_mul_of_nonneg_left row4_cost_upper hp0).trans
    (mul_le_mul_of_nonneg_right hp1 (by norm_num : (0 : ℝ) ≤ 31667784024997/755387500000000))
  change positiveSource row4.s row4.S < _ at hS
  change positiveSource row4.kappa3 row4.kappa1 < _ at hk
  unfold sourceD D
  linarith only [hS,hk,hl,hcost]

theorem actual_H_lower {δ s : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/1000)
    (hs : 1 ≤ s) (ht : s ≤ 5/2) : H0 < wuImprovementLimit true δ s := by
  have h := SecondFunctionalStrictMargins.actual_core_lower (3 : Fin 4) hδ (by linarith)
  change D row4 δ/5 ≤ wuImprovementLimit true δ row4.s at h
  rw [(show row4.s = (5/2 : ℝ) by norm_num [row4])] at h
  have hm := wuImprovementLimit_upper_antitone_initial hδ (by linarith)
    (show s ∈ Icc 1 3 from ⟨hs, by linarith⟩)
    (show (5/2 : ℝ) ∈ Icc 1 3 by norm_num) ht
  unfold H0
  linarith only [h,hm,actual_D_lower hδ hδhi]

/-- This expression is only used on the actual s-domain [2,5]. -/
def profile (s : ℝ) : ℝ := max 0 (H0*log ((5/2)/(s-1)))

theorem profile_nonneg (s : ℝ) : 0 ≤ profile s := le_max_left _ _

/-- FTC on the entire original cross-integral domain, with no internal cut. -/
theorem original_ftc {s : ℝ} (hs : 2 ≤ s) (ht : s ≤ 7/2) :
    (∫ u in (s-1)..(5/2 : ℝ), H0/u) = H0*log ((5/2)/(s-1)) := by
  have hab : s-1 ≤ (5/2 : ℝ) := by linarith
  have hc : ContinuousOn (fun u : ℝ => H0/u) (Icc (s-1) (5/2)) :=
    continuousOn_const.div continuousOn_id (fun u hu => by change u ≠ 0; linarith [hu.1])
  have hd (u : ℝ) (hu : u ∈ uIcc (s-1) (5/2 : ℝ)) :
      HasDerivAt (fun u : ℝ => H0*log u) (H0/u) u := by
    rw [uIcc_of_le hab] at hu
    simpa only [div_eq_mul_inv] using
      (Real.hasDerivAt_log (show u ≠ 0 by linarith [hu.1])).const_mul H0
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hc.intervalIntegrable_of_Icc hab)]
  rw [Real.log_div (by norm_num : (5/2 : ℝ) ≠ 0) (by linarith : s-1 ≠ 0)]
  ring

theorem profile_lower {δ s : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/1000)
    (hs : 2 ≤ s) (ht : s ≤ 5) : profile s ≤ wuImprovementLimit false δ s := by
  apply max_le
  · exact wuImprovementLimit_nonneg false hδ (by linarith) (by linarith) (by linarith)
  · by_cases h : s ≤ 7/2
    · have hab : s-1 ≤ (5/2 : ℝ) := by linarith
      have hc : ContinuousOn (fun u : ℝ => H0/u) (Icc (s-1) (5/2)) :=
        continuousOn_const.div continuousOn_id (fun u hu => by change u ≠ 0; linarith [hu.1])
      have hi := intervalIntegral.integral_mono_on hab
        (hc.intervalIntegrable_of_Icc hab)
        (SecondFunctionalSmallDelta.actual_kernel_integrable hδ hδhi hs h)
        (fun u hu => div_le_div_of_nonneg_right
          (actual_H_lower hδ hδhi (by linarith [hu.1]) hu.2).le (by linarith [hu.1]))
      rw [original_ftc hs h] at hi
      have hn := wuImprovementLimit_nonneg false (δ := δ) (s := (7/2 : ℝ))
        hδ (by linarith) (by norm_num) (by norm_num)
      have hx := wuImprovementLimit_lower_cross (δ := δ) (s := s)
        (t := (7/2 : ℝ)) hδ (by linarith) hs h (by norm_num)
      norm_num only at hx
      linarith only [hi,hn,hx]
    · have hn := wuImprovementLimit_nonneg false (δ := δ) (s := s)
        hδ (by linarith) (by linarith) (by linarith)
      have hl : log ((5/2)/(s-1)) ≤ 0 := Real.log_nonpos
        (div_nonneg (by norm_num) (by linarith)) ((div_le_one (by linarith : 0 < s-1)).2 (by linarith))
      exact (mul_nonpos_of_nonneg_of_nonpos H0_pos.le hl).trans hn

theorem profile_antitone : AntitoneOn profile (Icc 2 5) := by
  intro s hs t ht hst
  apply max_le_max le_rfl
  apply mul_le_mul_of_nonneg_left _ H0_pos.le
  apply Real.log_le_log (div_pos (by norm_num) (by linarith [ht.1]) : 0 < (5/2 : ℝ)/(t-1))
  exact div_le_div_of_nonneg_left (by norm_num) (by linarith [hs.1]) (by linarith)

/-- Universal log inequality; no numerical log estimate or new Taylor order. -/
theorem log_affine_lower {s : ℝ} (hs : 2 ≤ s) :
    (7/2-s)/(5/2) ≤ log ((5/2)/(s-1)) := by
  have ha : 0 < (s-1)/(5/2 : ℝ) := div_pos (by linarith) (by norm_num)
  have hl := Real.log_le_sub_one_of_pos ha
  have he : (5/2 : ℝ)/(s-1) = ((s-1)/(5/2))⁻¹ := by rw [inv_div]
  rw [he,Real.log_inv]
  linarith only [hl]

/-- A strict source factor is retained uniformly, including the zero branch. -/
theorem scaled_seed_lower {s : ℝ} (hs : 2 ≤ s) :
    (300*H0)*FullAdmissibleSeed.seed s ≤ profile s := by
  by_cases h : 0 ≤ (7/2-s)/750
  · rw [FullAdmissibleSeed.seed,max_eq_right h]
    have hl := mul_le_mul_of_nonneg_left (log_affine_lower hs) H0_pos.le
    have he : (300*H0)*((7/2-s)/750) = H0*((7/2-s)/(5/2)) := by ring
    rw [he]
    exact hl.trans (le_max_right _ _)
  · rw [FullAdmissibleSeed.seed,max_eq_left (le_of_not_ge h),mul_zero]
    exact profile_nonneg s

theorem seed_lower {s : ℝ} (hs : 2 ≤ s) : FullAdmissibleSeed.seed s ≤ profile s := by
  have hf : 1 ≤ 300*H0 := by linarith only [H0_margin]
  exact (le_mul_of_one_le_left (FullAdmissibleSeed.seed_nonneg s) hf).trans (scaled_seed_lower hs)

theorem profile_measurable : Measurable profile := by
  unfold profile
  fun_prop

end Row4LogProfile
