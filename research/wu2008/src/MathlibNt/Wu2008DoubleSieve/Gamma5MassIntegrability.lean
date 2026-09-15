import MathlibNt.Wu2008DoubleSieve.Gamma5MassKernel

/-!
# Integrability of the literal rectangular and full-triangle coefficients

These statements concern the unclipped literal kernel itself, not just its
bounded extension used for prime quadrature.
-/

namespace Wu2008DoubleSieve

open Finset Set Real MeasureTheory
open scoped Classical Topology Interval

theorem gamma5Mass_literal_section_eq {C D t : ℝ}
    (ht : t ≤ gamma5ClassicalB) (hCD : C ≤ D) (hD : D ≤ gamma5ClassicalB) :
    (∫ u in gamma5MassSectionStart C D t..D, gamma5MassKernel t u) =
      gamma5MassSection C D t / t := by
  unfold gamma5MassSection
  rw [← intervalIntegral.integral_div]
  apply intervalIntegral.integral_congr
  intro u hu
  have hs := gamma5Mass_start_bounds hCD t
  have hu' : u ∈ Icc (gamma5MassSectionStart C D t) D := by
    simpa only [uIcc_of_le hs.2] using hu
  dsimp only
  rw [gamma5Mass_H_eq ht (hu'.2.trans hD)]
  simp only [gamma5MassKernel, div_eq_mul_inv, mul_inv]
  ring

theorem gamma5Mass_literal_inner_integrable {C D t : ℝ}
    (ht : t ∈ Icc gamma5MassA gamma5ClassicalB)
    (hC : gamma5MassA ≤ C) (hCD : C ≤ D) (hD : D ≤ gamma5ClassicalB) :
    IntervalIntegrable (gamma5MassKernel t) volume (gamma5MassSectionStart C D t) D := by
  have hs := gamma5Mass_start_bounds hCD t
  have ht0 : 0 < t := by have := gamma5Mass_constants.1; linarith [ht.1]
  have hc : 0 < C := by have := gamma5Mass_constants.1; linarith
  have hcont : ContinuousOn (gamma5MassKernel t) (uIcc (gamma5MassSectionStart C D t) D) := by
    apply continuousOn_const.div
      ((continuousOn_const.mul continuousOn_id).mul
        ((continuousOn_const.sub continuousOn_const).sub continuousOn_id))
    intro u hu
    have hu' : u ∈ Icc (gamma5MassSectionStart C D t) D := by
      simpa only [uIcc_of_le hs.2] using hu
    have hu0 : 0 < u := (hc.trans_le hs.1).trans_le hu'.1
    have hgap := gamma5Mass_constants.2.2.2
    have hden : 0 < 1 - t - u := by linarith [ht.2, hu'.2]
    exact ne_of_gt (mul_pos (mul_pos ht0 hu0) hden)
  exact hcont.intervalIntegrable

theorem gamma5Mass_literal_outer_integrable {A B C D : ℝ}
    (hA : gamma5MassA ≤ A) (hAB : A ≤ B) (hB : B ≤ gamma5ClassicalB)
    (hC : gamma5MassA ≤ C) (hCD : C ≤ D) (hD : D ≤ gamma5ClassicalB) :
    IntervalIntegrable
      (fun t => ∫ u in gamma5MassSectionStart C D t..D, gamma5MassKernel t u) volume A B := by
  have h := gamma5Mass_rectangle_integrable hA hAB hB hC hCD hD
  apply h.congr
  intro t ht
  have ht' : t ∈ Icc A B := by simpa only [uIcc_of_le hAB] using uIoc_subset_uIcc ht
  exact (gamma5Mass_literal_section_eq (ht'.2.trans hB) hCD hD).symm

theorem gamma5Mass_C5_integrable :
    (∀ t ∈ Icc gamma5MassA gamma5ClassicalB,
      IntervalIntegrable (gamma5MassKernel t) volume t gamma5ClassicalB) ∧
    IntervalIntegrable (fun t => ∫ u in t..gamma5ClassicalB, gamma5MassKernel t u)
      volume gamma5MassA gamma5ClassicalB := by
  have hab := gamma5Mass_constants.2.1.le
  constructor
  · intro t ht
    have h := gamma5Mass_literal_inner_integrable ht le_rfl hab le_rfl
    simpa only [gamma5MassSectionStart, max_eq_right ht.1, min_eq_right ht.2] using h
  · have h := gamma5Mass_literal_outer_integrable le_rfl hab le_rfl le_rfl hab le_rfl
    apply h.congr
    intro t ht
    have ht' : t ∈ Icc gamma5MassA gamma5ClassicalB := by
      simpa only [uIcc_of_le hab] using uIoc_subset_uIcc ht
    simp only [gamma5MassSectionStart, max_eq_right ht'.1, min_eq_right ht'.2]

end Wu2008DoubleSieve
