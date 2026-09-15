import MathlibNt.Wu2008DoubleSieve.Gamma5MassArithmetic
import MathlibNt.Wu2008DoubleSieve.PrimeOrderedQuadratureIntegral

/-!
# The literal triangle kernel and uniform rectangular sections

Clipping is used only to extend the one-dimensional weights to the larger
interval required by the existing quadrature API. On the actual source
square the kernel is exactly `1/(1-t-u)`.
-/

namespace Wu2008DoubleSieve

open Finset Set Real Filter MeasureTheory
open scoped Classical Topology Interval

noncomputable def gamma5MassA : ℝ := 1 / gamma5ClassicalS

noncomputable def gamma5MassClip (t : ℝ) : ℝ := min gamma5ClassicalB t

noncomputable def gamma5MassH (t u : ℝ) : ℝ :=
  1 / (1 - gamma5MassClip t - gamma5MassClip u)

noncomputable def gamma5MassKernel (t u : ℝ) : ℝ := 1 / (t * u * (1 - t - u))

noncomputable def gamma5MassSectionStart (C D t : ℝ) : ℝ := min D (max C t)

noncomputable def gamma5MassSection (C D t : ℝ) : ℝ :=
  ∫ u in gamma5MassSectionStart C D t..D, gamma5MassH t u / u

/-- The literal iterated integral over the triangle intersected with the
closed rectangle. A section above D has equal endpoints, hence is empty. -/
noncomputable def gamma5MassRectangleIntegral (A B C D : ℝ) : ℝ :=
  ∫ t in A..B, ∫ u in gamma5MassSectionStart C D t..D, gamma5MassKernel t u

noncomputable def gamma5MassC5 : ℝ :=
  ∫ t in gamma5MassA..gamma5ClassicalB,
    ∫ u in t..gamma5ClassicalB, gamma5MassKernel t u

theorem gamma5Mass_constants :
    1 / 10 ≤ gamma5MassA ∧ gamma5MassA < gamma5ClassicalB ∧
      gamma5ClassicalB ≤ 1 / 2 ∧ 1 / 4 ≤ 1 - 2 * gamma5ClassicalB := by
  norm_num [gamma5MassA, gamma5ClassicalS, gamma5ClassicalB]

theorem gamma5Mass_min_lipschitz (c x y : ℝ) :
    |min c x - min c y| ≤ |x - y| := by
  rcases le_total x c with hx | hx <;> rcases le_total y c with hy | hy
  · simp only [min_eq_right hx, min_eq_right hy, le_refl]
  · rw [min_eq_right hx, min_eq_left hy, abs_of_nonpos (by linarith),
      abs_of_nonpos (by linarith)]
    linarith
  · rw [min_eq_left hx, min_eq_right hy, abs_of_nonneg (by linarith),
      abs_of_nonneg (by linarith)]
    linarith
  · simp only [min_eq_left hx, min_eq_left hy, sub_self, abs_zero, abs_nonneg]

theorem gamma5Mass_max_lipschitz (c x y : ℝ) :
    |max c x - max c y| ≤ |x - y| := by
  have h := gamma5Mass_min_lipschitz (-c) (-x) (-y)
  simpa only [min_neg_neg, neg_sub_neg, abs_sub_comm] using h

theorem gamma5Mass_H_bounds (t u : ℝ) :
    0 < gamma5MassH t u ∧ gamma5MassH t u ≤ 4 := by
  have ht : gamma5MassClip t ≤ gamma5ClassicalB := min_le_left _ _
  have hu : gamma5MassClip u ≤ gamma5ClassicalB := min_le_left _ _
  have hgap := gamma5Mass_constants.2.2.2
  have hd : 0 < 1 - gamma5MassClip t - gamma5MassClip u := by linarith
  unfold gamma5MassH
  exact ⟨one_div_pos.mpr hd, (div_le_iff₀ hd).mpr (by linarith)⟩

theorem gamma5Mass_H_lipschitz (x y u : ℝ) :
    |gamma5MassH x u - gamma5MassH y u| ≤ 16 * |x - y| := by
  have hgap := gamma5Mass_constants.2.2.2
  have hx : gamma5MassClip x ≤ gamma5ClassicalB := min_le_left _ _
  have hy : gamma5MassClip y ≤ gamma5ClassicalB := min_le_left _ _
  have hu : gamma5MassClip u ≤ gamma5ClassicalB := min_le_left _ _
  have hdx : 0 < 1 - gamma5MassClip x - gamma5MassClip u := by linarith
  have hdy : 0 < 1 - gamma5MassClip y - gamma5MassClip u := by linarith
  have hd : 1 / 16 ≤ (1 - gamma5MassClip x - gamma5MassClip u) *
      (1 - gamma5MassClip y - gamma5MassClip u) := by nlinarith
  have he : gamma5MassH x u - gamma5MassH y u =
      (gamma5MassClip x - gamma5MassClip y) /
        ((1 - gamma5MassClip x - gamma5MassClip u) *
          (1 - gamma5MassClip y - gamma5MassClip u)) := by
    unfold gamma5MassH
    field_simp
    ring
  rw [he, abs_div, abs_of_pos (mul_pos hdx hdy)]
  apply (div_le_iff₀ (mul_pos hdx hdy)).mpr
  have hl := gamma5Mass_min_lipschitz gamma5ClassicalB x y
  change |gamma5MassClip x - gamma5MassClip y| ≤ |x - y| at hl
  nlinarith [abs_nonneg (x - y)]

theorem gamma5Mass_H_comm (t u : ℝ) : gamma5MassH t u = gamma5MassH u t := by
  unfold gamma5MassH
  congr 1
  ring

theorem gamma5Mass_H_second_lipschitz (t x y : ℝ) :
    |gamma5MassH t x - gamma5MassH t y| ≤ 16 * |x - y| := by
  rw [gamma5Mass_H_comm t x, gamma5Mass_H_comm t y]
  exact gamma5Mass_H_lipschitz x y t

theorem gamma5Mass_H_continuous (t : ℝ) :
    ContinuousOn (gamma5MassH t) (Icc (1 / 10 : ℝ) (1 / 2)) :=
  primeOrdered_continuous_of_lipschitz (fun x _ y _ => gamma5Mass_H_second_lipschitz t x y)

theorem gamma5Mass_H_eq {t u : ℝ} (ht : t ≤ gamma5ClassicalB)
    (hu : u ≤ gamma5ClassicalB) :
    gamma5MassH t u = 1 / (1 - t - u) := by
  simp only [gamma5MassH, gamma5MassClip, min_eq_right ht, min_eq_right hu]

theorem gamma5Mass_start_bounds {C D : ℝ} (hCD : C ≤ D) (t : ℝ) :
    C ≤ gamma5MassSectionStart C D t ∧ gamma5MassSectionStart C D t ≤ D :=
  ⟨le_min hCD (le_max_left _ _), min_le_left _ _⟩

theorem gamma5Mass_start_lipschitz (C D x y : ℝ) :
    |gamma5MassSectionStart C D x - gamma5MassSectionStart C D y| ≤ |x - y| :=
  (gamma5Mass_min_lipschitz D (max C x) (max C y)).trans
    (gamma5Mass_max_lipschitz C x y)

theorem gamma5Mass_section_regular {C D : ℝ}
    (hC : 1 / 10 ≤ C) (hCD : C ≤ D) (hD : D ≤ 1 / 2) :
    (∀ t : ℝ, |gamma5MassSection C D t| ≤ 16) ∧
      (∀ x y : ℝ, |gamma5MassSection C D x - gamma5MassSection C D y| ≤
        104 * |x - y|) := by
  have hDm : D ∈ Icc (1 / 10 : ℝ) (1 / 2) := ⟨hC.trans hCD, hD⟩
  have hm (t : ℝ) : gamma5MassSectionStart C D t ∈ Icc (1 / 10 : ℝ) (1 / 2) :=
    ⟨hC.trans (gamma5Mass_start_bounds hCD t).1,
      (gamma5Mass_start_bounds hCD t).2.trans hD⟩
  have hb (t u : ℝ) : |gamma5MassH t u| ≤ 4 := by
    rw [abs_of_pos (gamma5Mass_H_bounds t u).1]
    exact (gamma5Mass_H_bounds t u).2
  constructor
  · intro t
    simpa only [show (4 : ℝ) * 4 = 16 by norm_num] using
      primeOrdered_integral_norm_le_four (hm t) hDm (by norm_num) (fun u _ => hb t u)
  · intro x y
    have h1 := primeOrdered_integral_sub_bound
      (gamma5Mass_H_continuous x) (gamma5Mass_H_continuous y) (hm x) hDm
      (show 0 ≤ 16 * |x - y| by positivity) (fun u _ => gamma5Mass_H_lipschitz x y u)
    have h2 := primeOrdered_integral_norm_le (hm x) (hm y) (fun u _ => hb y u)
    have ha := intervalIntegral.integral_add_adjacent_intervals
      (primeOrdered_integrable (gamma5Mass_H_continuous y) (hm x) (hm y))
      (primeOrdered_integrable (gamma5Mass_H_continuous y) (hm y) hDm)
    have he : (∫ u in gamma5MassSectionStart C D x..D, gamma5MassH y u / u) -
        (∫ u in gamma5MassSectionStart C D y..D, gamma5MassH y u / u) =
        ∫ u in gamma5MassSectionStart C D x..gamma5MassSectionStart C D y,
          gamma5MassH y u / u := by linarith only [ha]
    have ht := abs_sub_le (gamma5MassSection C D x)
      (∫ u in gamma5MassSectionStart C D x..D, gamma5MassH y u / u)
      (gamma5MassSection C D y)
    dsimp only [gamma5MassSection] at ht ⊢
    rw [he] at ht
    rw [abs_sub_comm (gamma5MassSectionStart C D y)] at h2
    have hl := gamma5Mass_start_lipschitz C D x y
    linarith

theorem gamma5Mass_rectangle_eq {A B C D : ℝ}
    (hA : gamma5MassA ≤ A) (hAB : A ≤ B) (hB : B ≤ gamma5ClassicalB)
    (hC : gamma5MassA ≤ C) (hCD : C ≤ D) (hD : D ≤ gamma5ClassicalB) :
    gamma5MassRectangleIntegral A B C D =
      ∫ t in A..B, gamma5MassSection C D t / t := by
  unfold gamma5MassRectangleIntegral gamma5MassSection
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ Icc A B := by simpa only [uIcc_of_le hAB] using ht
  dsimp only
  rw [← intervalIntegral.integral_div]
  apply intervalIntegral.integral_congr
  intro u hu
  have hstart := gamma5Mass_start_bounds hCD t
  have hu' : u ∈ Icc (gamma5MassSectionStart C D t) D := by
    simpa only [uIcc_of_le hstart.2] using hu
  rw [gamma5Mass_H_eq (ht'.2.trans hB) (hu'.2.trans hD)]
  unfold gamma5MassKernel
  ring

theorem gamma5Mass_rectangle_bounds {A B C D : ℝ}
    (hA : gamma5MassA ≤ A) (hAB : A ≤ B) (hB : B ≤ gamma5ClassicalB)
    (hC : gamma5MassA ≤ C) (hCD : C ≤ D) (hD : D ≤ gamma5ClassicalB) :
    0 ≤ gamma5MassRectangleIntegral A B C D ∧
      gamma5MassRectangleIntegral A B C D ≤ 64 := by
  have ha := gamma5Mass_constants.1.trans hA
  have hb := hB.trans gamma5Mass_constants.2.2.1
  have hc := gamma5Mass_constants.1.trans hC
  have hd := hD.trans gamma5Mass_constants.2.2.1
  rw [gamma5Mass_rectangle_eq hA hAB hB hC hCD hD]
  constructor
  · apply intervalIntegral.integral_nonneg hAB
    intro t ht
    have ht0 : 0 ≤ t := by linarith [ht.1]
    apply div_nonneg _ ht0
    apply intervalIntegral.integral_nonneg (gamma5Mass_start_bounds hCD t).2
    intro u hu
    apply div_nonneg (gamma5Mass_H_bounds t u).1.le
    have hs := (gamma5Mass_start_bounds hCD t).1
    linarith [hu.1]
  · have hh := (le_abs_self _).trans
      (primeOrdered_integral_norm_le_four ⟨ha, hAB.trans hb⟩ ⟨ha.trans hAB, hb⟩
        (by norm_num : (0 : ℝ) ≤ 16) (fun t _ => (gamma5Mass_section_regular hc hCD hd).1 t))
    simpa only [show (4 : ℝ) * 16 = 64 by norm_num] using hh

theorem gamma5Mass_rectangle_integrable {A B C D : ℝ}
    (hA : gamma5MassA ≤ A) (hAB : A ≤ B) (hB : B ≤ gamma5ClassicalB)
    (hC : gamma5MassA ≤ C) (hCD : C ≤ D) (hD : D ≤ gamma5ClassicalB) :
    IntervalIntegrable (fun t => gamma5MassSection C D t / t) volume A B := by
  have hr := gamma5Mass_section_regular (gamma5Mass_constants.1.trans hC) hCD
    (hD.trans gamma5Mass_constants.2.2.1)
  exact primeOrdered_integrable
    (primeOrdered_continuous_of_lipschitz (fun x _ y _ => hr.2 x y))
    ⟨gamma5Mass_constants.1.trans hA, (hAB.trans hB).trans gamma5Mass_constants.2.2.1⟩
    ⟨(gamma5Mass_constants.1.trans hA).trans hAB, hB.trans gamma5Mass_constants.2.2.1⟩

theorem gamma5Mass_full_integral_eq :
    gamma5MassRectangleIntegral gamma5MassA gamma5ClassicalB gamma5MassA gamma5ClassicalB =
      gamma5MassC5 := by
  unfold gamma5MassRectangleIntegral gamma5MassC5
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ Icc gamma5MassA gamma5ClassicalB := by
    simpa only [uIcc_of_le gamma5Mass_constants.2.1.le] using ht
  simp only [gamma5MassSectionStart, max_eq_right ht'.1, min_eq_right ht'.2]

theorem gamma5Mass_C5_bounds : 0 ≤ gamma5MassC5 ∧ gamma5MassC5 ≤ 64 := by
  rw [← gamma5Mass_full_integral_eq]
  exact gamma5Mass_rectangle_bounds le_rfl gamma5Mass_constants.2.1.le le_rfl
    le_rfl gamma5Mass_constants.2.1.le le_rfl

end Wu2008DoubleSieve
