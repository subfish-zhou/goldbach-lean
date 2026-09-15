import MathlibNt.Wu2008DoubleSieve.Omega3ElementaryFeedback
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalClassicalAlgebra

namespace Wu2008DoubleSieve.SecondFunctionalSignedCore
open Set MeasureTheory MotherPair SecondFunctionalPositive
open scoped Interval

/-- The clipped diagonal rectangle is the literal classical triangle. -/
theorem diagonal_rectangle {a b : ℝ} (hab : a ≤ b) :
    rectIntegral a b a b = ∫ t in a..b, ∫ u in t..b, gamma5MassKernel t u := by
  unfold rectIntegral
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le hab] at ht
  simp only [max_eq_right ht.1, min_eq_right ht.2, gamma5MassKernel]

/-- Three original adjacent slices, with all inner integrability supplied. -/
theorem adjacent_slices {p : SecondFunctionalParameters} (hp : AnalyticParameters p)
    {t : ℝ} (ht : t ∈ Icc (1/p.S) (1/p.kappa1)) :
    (∫ u in min (upperQ p .gammaSeven) (max (lowerQ p .gammaSeven) t)..
      upperQ p .gammaSeven, 1/(t*u*(1-t-u))) +
    (∫ u in min (upperQ p .gammaEight) (max (lowerQ p .gammaEight) t)..
      upperQ p .gammaEight, 1/(t*u*(1-t-u))) +
    (∫ u in min (upperQ p .gammaSix) (max (lowerQ p .gammaSix) t)..
      upperQ p .gammaSix, 1/(t*u*(1-t-u))) =
    ∫ u in t..(1/p.kappa3), gamma5MassKernel t u := by
  obtain ⟨_, _, hbc, hce, _, _⟩ := parameter_order hp
  have h7 := classical_inner_integrable hp .gammaSeven ht
  have h8 := classical_inner_integrable hp .gammaEight ht
  have h6 := classical_inner_integrable hp .gammaSix ht
  simp only [upperQ, lowerQ, max_eq_right ht.1, min_eq_right ht.2,
    max_eq_left ht.2, max_eq_left (ht.2.trans hbc.le), min_eq_right hbc.le,
    min_eq_right hce.le] at h7 h8 h6 ⊢
  rw [intervalIntegral.integral_add_adjacent_intervals h7 h8,
    intervalIntegral.integral_add_adjacent_intervals (h7.trans h8) h6]
  rfl

/-- Join the actual three rectangles before removing the upper triangle. -/
theorem classical_strip {p : SecondFunctionalParameters} (hp : AnalyticParameters p) :
    classicalIntegral p .gammaSeven + classicalIntegral p .gammaEight +
      classicalIntegral p .gammaSix =
    ∫ t in (1/p.S)..(1/p.kappa1), ∫ u in t..(1/p.kappa3), gamma5MassKernel t u := by
  have h7 := classical_outer_integrable hp .gammaSeven
  have h8 := classical_outer_integrable hp .gammaEight
  have h6 := classical_outer_integrable hp .gammaSix
  simp only [upperP] at h7 h8 h6
  rw [classicalIntegral_literal, classicalIntegral_literal, classicalIntegral_literal]
  simp only [upperP]
  rw [← intervalIntegral.integral_add h7 h8,
    ← intervalIntegral.integral_add (h7.add h8) h6]
  apply intervalIntegral.integral_congr
  intro t ht
  apply adjacent_slices hp
  simpa only [uIcc_of_le (parameter_order hp).2.1] using ht

/-- Actual four-rectangle producer; no mass or integrability premise. -/
theorem classical_eq_triangles {p : SecondFunctionalParameters} (hp : AnalyticParameters p) :
    SecondFunctionalCoupledFeedback.classical p =
      fourthRowClassicalTriangle p.S p.kappa2 + fourthRowClassicalTriangle p.S p.kappa3 -
        fourthRowClassicalTriangle p.kappa1 p.kappa3 := by
  obtain ⟨ha, hab, hbc, hce, hef, hf⟩ := parameter_order hp
  have hae := (hab.trans hbc.le).trans hce.le
  have hbe := hbc.le.trans hce.le
  have hi := (fourthRowClassical_triangle_fubini (by linarith : 0 < 1/p.S)
    hae (hef.trans_lt hf)).1
  have hi1 := hi.mono_set (show uIcc (1/p.S) (1/p.kappa1) ⊆
      uIcc (1/p.S) (1/p.kappa3) by
    rw [uIcc_of_le hab, uIcc_of_le hae]
    exact Icc_subset_Icc_right hbe)
  have hi2 := hi.mono_set (show uIcc (1/p.kappa1) (1/p.kappa3) ⊆
      uIcc (1/p.S) (1/p.kappa3) by
    rw [uIcc_of_le hbe, uIcc_of_le hae]
    exact Icc_subset_Icc_left hab)
  have hadd := intervalIntegral.integral_add_adjacent_intervals hi1 hi2
  have hstrip := classical_strip hp
  have h5 : classicalIntegral p .gammaFive = fourthRowClassicalTriangle p.S p.kappa2 :=
    diagonal_rectangle (hab.trans hbc.le)
  unfold SecondFunctionalCoupledFeedback.classical
  rw [h5]
  unfold fourthRowClassicalTriangle
  linarith only [hstrip, hadd]

theorem original_classical_eq_triangles (i : Fin 4) :
    SecondFunctionalCoupledFeedback.classical (parameters i) =
      fourthRowClassicalTriangle (parameters i).S (parameters i).kappa2 +
      fourthRowClassicalTriangle (parameters i).S (parameters i).kappa3 -
      fourthRowClassicalTriangle (parameters i).kappa1 (parameters i).kappa3 :=
  classical_eq_triangles (parameters_analytic i)

end Wu2008DoubleSieve.SecondFunctionalSignedCore
