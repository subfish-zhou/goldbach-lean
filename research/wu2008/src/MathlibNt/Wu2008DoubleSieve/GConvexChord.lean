import MathlibNt.Wu2008DoubleSieve.VariableGIntegral
import Mathlib.Analysis.Convex.Deriv

namespace Wu2008DoubleSieve.GConvexChord
open Real Set MeasureTheory SharpLogRecurrence
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne

noncomputable def r4 : ℝ := 311/270
noncomputable def r5 : ℝ := 42823/30375
noncomputable def m : ℝ := r5-r4
noncomputable def C : ℝ := 5*r4-4*r5
noncomputable def density (u : ℝ) : ℝ := log (u-2)/(u-1)

/-- Differentiate the actual normalized delay function, including the endpoints. -/
theorem upper_derivative {u : ℝ} (hu : u ∈ Icc (4 : ℝ) 5) :
    HasDerivAt wuUpperCoefficient (density u) u := by
  have h := (hasDerivAt_mul_jr1965F (show 2 < u by linarith [hu.1])).div_const
    (2*exp eulerMascheroniConstant)
  have he : wuLowerCoefficient (u-1) = log (u-2) := by
    simpa only [wuLowerCoefficient, show u-1-1 = u-2 by ring] using
      jr1965f_normalized_firstInterval (s := u-1) (by linarith [hu.1])
        (by linarith [hu.2])
  have hz : u-1 ≠ 0 := by linarith [hu.1]
  have he' : jr1965f (u-1)/(2*exp eulerMascheroniConstant) = density u := by
    unfold density
    rw [← he]
    unfold wuLowerCoefficient
    field_simp [hz]
  exact h.congr_deriv he'

theorem density_derivative {u : ℝ} (hu : u ∈ Icc (4 : ℝ) 5) :
    HasDerivAt density ((1+1/(u-2)-log (u-2))/(u-1)^2) u := by
  have h2 : u-2 ≠ 0 := by linarith [hu.1]
  have h1 : u-1 ≠ 0 := by linarith [hu.1]
  convert (((hasDerivAt_id u).sub_const 2).log h2).div
    ((hasDerivAt_id u).sub_const 1) h1 using 1 <;>
    first | rfl | (dsimp; field_simp; ring)

theorem density_derivative_pos {u : ℝ} (hu : u ∈ Icc (4 : ℝ) 5) :
    0 < (1+1/(u-2)-log (u-2))/(u-1)^2 := by
  have h2 : 0 < u-2 := by linarith [hu.1]
  have hl : log (u-2) ≤ (10/9 : ℝ) := by
    have h := log_upper (by norm_num : (1 : ℝ) ≤ 3)
    norm_num [upperLog] at h
    exact (log_le_log h2 (by linarith [hu.2])).trans h
  have hi : (1/3 : ℝ) ≤ 1/(u-2) := by
    apply (le_div_iff₀ h2).2
    linarith [hu.2]
  apply div_pos
  · linarith
  · exact sq_pos_of_pos (by linarith [hu.1])

theorem density_monotone : MonotoneOn density (Icc (4 : ℝ) 5) := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
  · intro u hu
    exact (density_derivative hu).continuousAt.continuousWithinAt
  · intro u hu
    exact (density_derivative (interior_subset hu)).differentiableAt.differentiableWithinAt
  · intro u hu
    rw [(density_derivative (interior_subset hu)).deriv]
    exact (density_derivative_pos (interior_subset hu)).le

/-- Convexity is produced, not carried as a hypothesis. -/
theorem upper_convex : ConvexOn ℝ (Icc (4 : ℝ) 5) wuUpperCoefficient := by
  apply MonotoneOn.convexOn_of_deriv (convex_Icc _ _)
  · intro u hu
    exact (upper_derivative hu).continuousAt.continuousWithinAt
  · intro u hu
    exact (upper_derivative (interior_subset hu)).differentiableAt.differentiableWithinAt
  · intro u hu v hv huv
    rw [(upper_derivative (interior_subset hu)).deriv,
      (upper_derivative (interior_subset hv)).deriv]
    exact density_monotone (interior_subset hu) (interior_subset hv) huv

theorem chord_positive : 0 < m ∧ 0 < C := by norm_num [m,C,r4,r5]

/-- The fixed rational chord is used only on its natural closed interval. -/
theorem upper_chord {u : ℝ} (hu : u ∈ Icc (4 : ℝ) 5) :
    wuUpperCoefficient u ≤ m*u+C := by
  have h := upper_convex.2 (by norm_num : (4 : ℝ) ∈ Icc (4 : ℝ) 5)
    (by norm_num : (5 : ℝ) ∈ Icc (4 : ℝ) 5)
    (show 0 ≤ 5-u by linarith [hu.2]) (show 0 ≤ u-4 by linarith [hu.1])
    (show (5-u)+(u-4)=1 by ring)
  simp only [smul_eq_mul] at h
  have he : (5-u)*4+(u-4)*5 = u := by ring
  rw [he] at h
  have h4 : wuUpperCoefficient 4 ≤ r4 := by
    dsimp [r4]; linarith [upper_four_div]
  have h5 : wuUpperCoefficient 5 ≤ r5 := by
    dsimp [r5]; linarith [upper_five_div]
  have h4' := mul_le_mul_of_nonneg_left h4 (show 0 ≤ 5-u by linarith [hu.2])
  have h5' := mul_le_mul_of_nonneg_left h5 (show 0 ≤ u-4 by linarith [hu.1])
  dsimp [m,C]
  nlinarith

end Wu2008DoubleSieve.GConvexChord
