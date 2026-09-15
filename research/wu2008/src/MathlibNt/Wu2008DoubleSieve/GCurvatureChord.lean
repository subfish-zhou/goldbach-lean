import MathlibNt.Wu2008DoubleSieve.GConvexChordIntegral

namespace Wu2008DoubleSieve.GCurvatureChord
open Real Set MeasureTheory SharpLogRecurrence
open VariableGIntegral (a s c)

/-- The fixed curvature is recovered from the actual delay derivative. -/
theorem curvature_lower {u : ℝ} (hu : u ∈ Icc (4 : ℝ) 5) :
    (1/72 : ℝ) ≤ (1+1/(u-2)-log (u-2))/(u-1)^2 := by
  have h2 : 0 < u-2 := by linarith [hu.1]
  have hl : log (u-2) ≤ (10/9 : ℝ) := by
    have h := log_upper (by norm_num : (1 : ℝ) ≤ 3)
    norm_num [upperLog] at h
    exact (log_le_log h2 (by linarith [hu.2])).trans h
  have hi : (1/3 : ℝ) ≤ 1/(u-2) := by
    apply (le_div_iff₀ h2).2
    linarith [hu.2]
  have hs : (u-1)^2 ≤ 16 := by nlinarith [hu.1,hu.2]
  apply (le_div_iff₀ (sq_pos_of_pos (show 0 < u-1 by linarith [hu.1]))).2
  linarith

noncomputable def correctedUpper (u : ℝ) : ℝ := wuUpperCoefficient u-u^2/144
noncomputable def correctedDensity (u : ℝ) : ℝ := GConvexChord.density u-u/72

theorem corrected_upper_derivative {u : ℝ} (hu : u ∈ Icc (4 : ℝ) 5) :
    HasDerivAt correctedUpper (correctedDensity u) u := by
  convert (GConvexChord.upper_derivative hu).sub
    (((hasDerivAt_id u).pow 2).div_const 144) using 1 <;>
    first | rfl | (dsimp [correctedDensity]; ring)

theorem corrected_density_derivative {u : ℝ} (hu : u ∈ Icc (4 : ℝ) 5) :
    HasDerivAt correctedDensity
      ((1+1/(u-2)-log (u-2))/(u-1)^2-1/72) u := by
  exact (GConvexChord.density_derivative hu).sub ((hasDerivAt_id u).div_const 72)

theorem corrected_density_monotone : MonotoneOn correctedDensity (Icc (4 : ℝ) 5) := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
  · intro u hu
    exact (corrected_density_derivative hu).continuousAt.continuousWithinAt
  · intro u hu
    exact (corrected_density_derivative (interior_subset hu)).differentiableAt.differentiableWithinAt
  · intro u hu
    rw [(corrected_density_derivative (interior_subset hu)).deriv]
    exact sub_nonneg.mpr (curvature_lower (interior_subset hu))

theorem corrected_upper_convex : ConvexOn ℝ (Icc (4 : ℝ) 5) correctedUpper := by
  apply MonotoneOn.convexOn_of_deriv (convex_Icc _ _)
  · intro u hu
    exact (corrected_upper_derivative hu).continuousAt.continuousWithinAt
  · intro u hu
    exact (corrected_upper_derivative (interior_subset hu)).differentiableAt.differentiableWithinAt
  · intro u hu v hv huv
    rw [(corrected_upper_derivative (interior_subset hu)).deriv,
      (corrected_upper_derivative (interior_subset hv)).deriv]
    exact corrected_density_monotone (interior_subset hu) (interior_subset hv) huv

/-- The original endpoints and rational chord, with the quadratic deficit. -/
theorem upper_quadratic_chord {u : ℝ} (hu : u ∈ Icc (4 : ℝ) 5) :
    wuUpperCoefficient u ≤ GConvexChord.m*u+GConvexChord.C-(u-4)*(5-u)/144 := by
  have h := corrected_upper_convex.2 (by norm_num : (4 : ℝ) ∈ Icc (4 : ℝ) 5)
    (by norm_num : (5 : ℝ) ∈ Icc (4 : ℝ) 5)
    (show 0 ≤ 5-u by linarith [hu.2]) (show 0 ≤ u-4 by linarith [hu.1])
    (show (5-u)+(u-4)=1 by ring)
  simp only [smul_eq_mul] at h
  rw [show (5-u)*4+(u-4)*5 = u by ring] at h
  have h4 : wuUpperCoefficient 4 ≤ GConvexChord.r4 := by
    dsimp [GConvexChord.r4]; linarith [upper_four_div]
  have h5 : wuUpperCoefficient 5 ≤ GConvexChord.r5 := by
    dsimp [GConvexChord.r5]; linarith [upper_five_div]
  have h4' := mul_le_mul_of_nonneg_left h4 (show 0 ≤ 5-u by linarith [hu.2])
  have h5' := mul_le_mul_of_nonneg_left h5 (show 0 ≤ u-4 by linarith [hu.1])
  dsimp [correctedUpper] at h
  dsimp [GConvexChord.m,GConvexChord.C]
  nlinarith

/-- Positivity is valid at both original closed endpoints. -/
theorem segment_domain {t : ℝ} (ht : t ∈ Icc (c 5) (c 4)) :
    0 < t ∧ 0 < 1/2-t ∧ (1/2-t)/a ∈ Icc (4 : ℝ) 5 := by
  have hg := GConvexChord.geometry
  refine ⟨hg.1.trans_le (hg.2.1.trans ht.1), ?_, ?_⟩
  · linarith [ht.2,hg.2.2.2.1,hg.2.2.2.2]
  · constructor
    · apply (le_div_iff₀ hg.1).2
      have hh : t ≤ 1/2-4*a := ht.2
      linarith
    · apply (div_le_iff₀ hg.1).2
      have hh : 1/2-5*a ≤ t := ht.1
      linarith

/-- Joint comparison is proved before weakening the denominator. -/
theorem pointwise_joint_exact {t : ℝ} (ht : t ∈ Icc (c 5) (c 4)) :
    ClassicalSingleBounds.g t+(c 4-t)*(t-c 5)/(144*a^2*t*(1/2-t)) ≤
      GConvexChord.majorant t := by
  obtain ⟨ht0,hd,hu⟩ := segment_domain ht
  have ha := GConvexChord.geometry.1.ne'
  have h := div_le_div_of_nonneg_right (upper_quadratic_chord hu) (mul_pos ht0 hd).le
  have hid : (GConvexChord.m*((1/2-t)/a)+GConvexChord.C-
      ((1/2-t)/a-4)*(5-(1/2-t)/a)/144)/(t*(1/2-t)) =
      GConvexChord.majorant t-(c 4-t)*(t-c 5)/(144*a^2*t*(1/2-t)) := by
    rw [show c 4 = 1/2-4*a from rfl, show c 5 = 1/2-5*a from rfl]
    dsimp [GConvexChord.majorant]
    have hd2 : 1-t*2 ≠ 0 := by intro hzero; apply hd.ne'; linarith
    field_simp [ha,ht0.ne',hd.ne',hd2]
    ring_nf
    field_simp [hd2]
    ring
  rw [hid] at h
  change wuUpperCoefficient ((1/2-t)/a)/(t*(1/2-t)) + _ ≤ _
  linarith only [h]

noncomputable def deficit (t : ℝ) : ℝ := (c 4-t)*(t-c 5)/(9*a^2)

theorem deficit_nonneg {t : ℝ} (ht : t ∈ Icc (c 5) (c 4)) : 0 ≤ deficit t := by
  exact div_nonneg (mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr ht.1))
    (mul_nonneg (by norm_num) (sq_nonneg a))

/-- The universal bound t(1/2-t) ≤ 1/16 yields a polynomial deficit. -/
theorem pointwise_joint {t : ℝ} (ht : t ∈ Icc (c 5) (c 4)) :
    ClassicalSingleBounds.g t+deficit t ≤ GConvexChord.majorant t := by
  obtain ⟨ht0,hd,_⟩ := segment_domain ht
  have ha := GConvexChord.geometry.1
  have hp : 0 ≤ (c 4-t)*(t-c 5) :=
    mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr ht.1)
  have hden : 0 < 144*a^2*t*(1/2-t) := by positivity
  have hquad : t*(1/2-t) ≤ (1/16 : ℝ) := by nlinarith [sq_nonneg (t-1/4)]
  have hscale := mul_le_mul_of_nonneg_left hquad (show 0 ≤ 144*a^2 by positivity)
  have hdle : 144*a^2*t*(1/2-t) ≤ 9*a^2 := by nlinarith only [hscale]
  have hgain : deficit t ≤ (c 4-t)*(t-c 5)/(144*a^2*t*(1/2-t)) :=
    div_le_div_of_nonneg_left hp hden hdle
  linarith only [hgain,pointwise_joint_exact ht]

end Wu2008DoubleSieve.GCurvatureChord
