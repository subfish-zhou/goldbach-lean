import MathlibNt.Wu2008DoubleSieve.MotherPairGainBounds
import MathlibNt.Wu2008DoubleSieve.FourthRowClassicalCoefficientLog

/-! Exact triangle reduction of the four original classical pair integrals. -/
namespace Wu2008DoubleSieve.SecondFunctionalSignedCore
open Set MeasureTheory MotherPair
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

end Wu2008DoubleSieve.SecondFunctionalSignedCore

namespace Wu2008DoubleSieve.MotherPair
open Set MeasureTheory Real
open scoped Interval

theorem classical_gammaFive_triangle {p : SecondFunctionalParameters}
    (h : AnalyticParameters p) :
    classicalIntegral p .gammaFive = fourthRowClassicalTriangle p.S p.kappa2 :=
  SecondFunctionalSignedCore.diagonal_rectangle
    ((parameter_order h).2.1.trans (parameter_order h).2.2.1.le)

theorem classical_gammaSixSevenEight_strip {p : SecondFunctionalParameters}
    (h : AnalyticParameters p) :
    classicalIntegral p .gammaSix + classicalIntegral p .gammaSeven +
      classicalIntegral p .gammaEight =
      ∫ t in (1/p.S)..(1/p.kappa1), ∫ u in t..(1/p.kappa3), gamma5MassKernel t u := by
  have hab := (parameter_order h).2.1
  have ho6 := classical_outer_integrable h .gammaSix
  have ho7 := classical_outer_integrable h .gammaSeven
  have ho8 := classical_outer_integrable h .gammaEight
  rw [show classicalIntegral p .gammaSix + classicalIntegral p .gammaSeven +
      classicalIntegral p .gammaEight =
      (classicalIntegral p .gammaSeven + classicalIntegral p .gammaEight) +
        classicalIntegral p .gammaSix by ring]
  simp only [classicalIntegral_literal,upperP] at ho6 ho7 ho8 ⊢
  rw [← intervalIntegral.integral_add ho7 ho8,
    ← intervalIntegral.integral_add (ho7.add ho8) ho6]
  apply intervalIntegral.integral_congr
  rw [uIcc_of_le hab]
  intro t ht
  dsimp only
  exact SecondFunctionalSignedCore.adjacent_slices h ht

theorem classical_gammaSixSevenEight_triangles {p : SecondFunctionalParameters}
    (h : AnalyticParameters p) :
    classicalIntegral p .gammaSix + classicalIntegral p .gammaSeven +
      classicalIntegral p .gammaEight =
      fourthRowClassicalTriangle p.S p.kappa3 -
        fourthRowClassicalTriangle p.kappa1 p.kappa3 := by
  obtain ⟨ha,hab,hbc,hce,hef,hf⟩ := parameter_order h
  have hbe := hbc.le.trans hce.le
  have hae := hab.trans hbe
  have hi := (fourthRowClassical_triangle_fubini (by linarith : 0 < 1/p.S)
    hae (hef.trans_lt hf)).1
  have hi1 := hi.mono_set (show uIcc (1/p.S) (1/p.kappa1) ⊆
      uIcc (1/p.S) (1/p.kappa3) by
    rw [uIcc_of_le hab,uIcc_of_le hae]
    exact Icc_subset_Icc_right hbe)
  have hi2 := hi.mono_set (show uIcc (1/p.kappa1) (1/p.kappa3) ⊆
      uIcc (1/p.S) (1/p.kappa3) by
    rw [uIcc_of_le hbe,uIcc_of_le hae]
    exact Icc_subset_Icc_left hab)
  have he := intervalIntegral.integral_add_adjacent_intervals hi1 hi2
  rw [classical_gammaSixSevenEight_strip h]
  unfold fourthRowClassicalTriangle
  linarith only [he]

/-- Four two-dimensional classical costs reduce to three J and three L integrals. -/
theorem classical_four_integrals_log {p : SecondFunctionalParameters}
    (h : AnalyticParameters p) :
    classicalIntegral p .gammaFive + classicalIntegral p .gammaSix +
      classicalIntegral p .gammaSeven + classicalIntegral p .gammaEight =
      fourthRowClassicalJ p.kappa2 p.S + fourthRowClassicalJ p.kappa3 p.S -
        fourthRowClassicalJ p.kappa3 p.kappa1 - 2*fourthRowClassicalL p.S +
        fourthRowClassicalL p.kappa2 + fourthRowClassicalL p.kappa1 := by
  have he : 2 < p.kappa3 := h.two_lt_s.trans_le h.mother.s_le_kappa3
  have hc : 2 < p.kappa2 := he.trans h.mother.kappa3_lt_kappa2
  have hcb := h.mother.kappa2_lt_kappa1.le
  have heb := h.mother.kappa3_lt_kappa2.le.trans hcb
  rw [show classicalIntegral p .gammaFive + classicalIntegral p .gammaSix +
      classicalIntegral p .gammaSeven + classicalIntegral p .gammaEight =
      classicalIntegral p .gammaFive + (classicalIntegral p .gammaSix +
        classicalIntegral p .gammaSeven + classicalIntegral p .gammaEight) by ring,
    classical_gammaFive_triangle h, classical_gammaSixSevenEight_triangles h,
    fourthRowClassical_triangle_eq_log (hcb.trans h.mother.kappa1_le_S) hc,
    fourthRowClassical_triangle_eq_log (heb.trans h.mother.kappa1_le_S) he,
    fourthRowClassical_triangle_eq_log heb he]
  ring

end Wu2008DoubleSieve.MotherPair
