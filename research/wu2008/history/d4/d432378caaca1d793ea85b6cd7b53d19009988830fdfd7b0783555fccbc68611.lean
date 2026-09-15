import MathlibNt.Wu2008DoubleSieve.Gamma6BaseFinite

/-! # The narrow asymmetric Gamma6 mass kernel -/

namespace Wu2008DoubleSieve

open Finset Set Real Filter MeasureTheory
open scoped Classical Topology Interval

noncomputable def gamma6BaseH (t u : ℝ) : ℝ :=
  1 / (1 - min gamma6BaseB t - min gamma6BaseF u)

noncomputable def gamma6BaseSection (C D t : ℝ) : ℝ :=
  ∫ u in C..D, gamma6BaseH t u / u

noncomputable def gamma6BaseIntegral (A B C D : ℝ) : ℝ :=
  ∫ t in A..B, ∫ u in C..D, gamma5MassKernel t u

noncomputable def gamma6BaseC6 : ℝ :=
  gamma6BaseIntegral gamma5MassA gamma6BaseB gamma6BaseC gamma6BaseF

theorem gamma6Base_denominator (t u : ℝ) :
    1 / 4 ≤ 1 - min gamma6BaseB t - min gamma6BaseF u := by
  have ht := min_le_left gamma6BaseB t
  have hu := min_le_left gamma6BaseF u
  have hgap := gamma6Base_constants.2.2.2.2.2.1
  linarith

theorem gamma6Base_H_bounds (t u : ℝ) : 0 < gamma6BaseH t u ∧ gamma6BaseH t u ≤ 4 := by
  have hd := gamma6Base_denominator t u
  have hp : 0 < 1 - min gamma6BaseB t - min gamma6BaseF u := by linarith
  exact ⟨div_pos (by norm_num) hp, (div_le_iff₀ hp).mpr (by linarith)⟩

theorem gamma6Base_inverse_difference {a b : ℝ} (ha : 1 / 4 ≤ a) (hb : 1 / 4 ≤ b) :
    |1 / a - 1 / b| ≤ 16 * |b - a| := by
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have he : 1 / a - 1 / b = (b - a) / (a * b) := by field_simp
  rw [he, abs_div, abs_of_pos (mul_pos ha0 hb0)]
  apply (div_le_iff₀ (mul_pos ha0 hb0)).mpr
  nlinarith [mul_le_mul ha hb (by norm_num) ha0.le, abs_nonneg (b - a)]

theorem gamma6Base_H_first (x y u : ℝ) :
    |gamma6BaseH x u - gamma6BaseH y u| ≤ 16 * |x - y| := by
  have h := gamma6Base_inverse_difference (gamma6Base_denominator x u) (gamma6Base_denominator y u)
  have he : (1 - min gamma6BaseB y - min gamma6BaseF u) -
      (1 - min gamma6BaseB x - min gamma6BaseF u) =
      min gamma6BaseB x - min gamma6BaseB y := by ring
  rw [he] at h
  exact h.trans (mul_le_mul_of_nonneg_left (gamma5Mass_min_lipschitz gamma6BaseB x y) (by norm_num))

theorem gamma6Base_H_second (t x y : ℝ) :
    |gamma6BaseH t x - gamma6BaseH t y| ≤ 16 * |x - y| := by
  have h := gamma6Base_inverse_difference (gamma6Base_denominator t x) (gamma6Base_denominator t y)
  have he : (1 - min gamma6BaseB t - min gamma6BaseF y) -
      (1 - min gamma6BaseB t - min gamma6BaseF x) =
      min gamma6BaseF x - min gamma6BaseF y := by ring
  rw [he] at h
  exact h.trans (mul_le_mul_of_nonneg_left (gamma5Mass_min_lipschitz gamma6BaseF x y) (by norm_num))

theorem gamma6Base_H_continuous (t : ℝ) :
    ContinuousOn (gamma6BaseH t) (Icc (1 / 10 : ℝ) (1 / 2)) :=
  primeOrdered_continuous_of_lipschitz (fun x _ y _ => gamma6Base_H_second t x y)

theorem gamma6Base_H_eq {t u : ℝ} (ht : t ≤ gamma6BaseB) (hu : u ≤ gamma6BaseF) :
    gamma6BaseH t u = 1 / (1 - t - u) := by
  simp only [gamma6BaseH, min_eq_right ht, min_eq_right hu]

theorem gamma6Base_section_regular {C D : ℝ}
    (hC : 1 / 10 ≤ C) (hCD : C ≤ D) (hD : D ≤ 1 / 2) :
    (∀ t, |gamma6BaseSection C D t| ≤ 16) ∧
      (∀ x y, |gamma6BaseSection C D x - gamma6BaseSection C D y| ≤ 64 * |x - y|) := by
  have hc : C ∈ Icc (1 / 10 : ℝ) (1 / 2) := ⟨hC, hCD.trans hD⟩
  have hd : D ∈ Icc (1 / 10 : ℝ) (1 / 2) := ⟨hC.trans hCD, hD⟩
  constructor
  · intro t
    exact primeOrdered_integral_norm_le_four hc hd (by norm_num)
      (fun u _ => by rw [abs_of_pos (gamma6Base_H_bounds t u).1]; exact (gamma6Base_H_bounds t u).2)
  · intro x y
    have h := primeOrdered_integral_sub_bound
      (gamma6Base_H_continuous x) (gamma6Base_H_continuous y) hc hd
      (show 0 ≤ 16 * |x - y| by positivity) (fun u _ => gamma6Base_H_first x y u)
    convert h using 1 <;> ring

theorem gamma6Base_integral_eq {A B C D : ℝ}
    (hAB : A ≤ B) (hB : B ≤ gamma6BaseB) (hCD : C ≤ D) (hD : D ≤ gamma6BaseF) :
    gamma6BaseIntegral A B C D = ∫ t in A..B, gamma6BaseSection C D t / t := by
  unfold gamma6BaseIntegral gamma6BaseSection
  apply intervalIntegral.integral_congr
  rw [uIcc_of_le hAB]
  intro t ht
  dsimp only
  rw [← intervalIntegral.integral_div]
  apply intervalIntegral.integral_congr
  rw [uIcc_of_le hCD]
  intro u hu
  dsimp only
  rw [gamma6Base_H_eq (ht.2.trans hB) (hu.2.trans hD)]
  simp only [gamma5MassKernel, div_eq_mul_inv, mul_inv]
  ring

theorem gamma6Base_integral_bounds {A B C D : ℝ}
    (hA : gamma5MassA ≤ A) (hAB : A ≤ B) (hB : B ≤ gamma6BaseB)
    (hC : gamma6BaseC ≤ C) (hCD : C ≤ D) (hD : D ≤ gamma6BaseF) :
    0 ≤ gamma6BaseIntegral A B C D ∧ gamma6BaseIntegral A B C D ≤ 64 := by
  have hAa : 1 / 10 ≤ A := gamma6Base_constants.1.trans hA
  have hBb : B ≤ 1 / 2 := hB.trans (by norm_num [gamma6BaseB])
  have hCc : 1 / 10 ≤ C := (by norm_num [gamma6BaseC] : (1 / 10 : ℝ) ≤ gamma6BaseC).trans hC
  have hDd : D ≤ 1 / 2 := hD.trans gamma6Base_constants.2.2.2.2.1
  rw [gamma6Base_integral_eq hAB hB hCD hD]
  have hr := gamma6Base_section_regular hCc hCD hDd
  constructor
  · apply intervalIntegral.integral_nonneg hAB
    intro t ht
    apply div_nonneg _ (by linarith [ht.1])
    apply intervalIntegral.integral_nonneg hCD
    intro u hu
    exact div_nonneg (gamma6Base_H_bounds t u).1.le (by linarith [hu.1])
  · exact (le_abs_self _).trans
      (primeOrdered_integral_norm_le_four ⟨hAa, hAB.trans hBb⟩ ⟨hAa.trans hAB, hBb⟩
        (by norm_num) (fun t _ => hr.1 t))

theorem gamma6Base_inner_integrable {t C D : ℝ}
    (ht : gamma5MassA ≤ t) (htb : t ≤ gamma6BaseB)
    (hC : gamma6BaseC ≤ C) (hCD : C ≤ D) (hD : D ≤ gamma6BaseF) :
    IntervalIntegrable (gamma5MassKernel t) volume C D := by
  have hCc : 1 / 10 ≤ C := (by norm_num [gamma6BaseC] : (1 / 10 : ℝ) ≤ gamma6BaseC).trans hC
  have hDd : D ≤ 1 / 2 := hD.trans gamma6Base_constants.2.2.2.2.1
  have hi := (primeOrdered_integrable (gamma6Base_H_continuous t)
    ⟨hCc, hCD.trans hDd⟩ ⟨hCc.trans hCD, hDd⟩).div_const t
  apply hi.congr
  intro u hu
  have hu' : u ∈ Icc C D := by simpa only [uIcc_of_le hCD] using uIoc_subset_uIcc hu
  dsimp only
  rw [gamma6Base_H_eq htb (hu'.2.trans hD)]
  simp only [gamma5MassKernel, div_eq_mul_inv, mul_inv]
  ring

theorem gamma6Base_outer_integrable {A B C D : ℝ}
    (hA : gamma5MassA ≤ A) (hAB : A ≤ B) (hB : B ≤ gamma6BaseB)
    (hC : gamma6BaseC ≤ C) (hCD : C ≤ D) (hD : D ≤ gamma6BaseF) :
    IntervalIntegrable (fun t => ∫ u in C..D, gamma5MassKernel t u) volume A B := by
  have hAa := gamma6Base_constants.1.trans hA
  have hBb : B ≤ 1 / 2 := hB.trans (by norm_num [gamma6BaseB])
  have hCc : 1 / 10 ≤ C := (by norm_num [gamma6BaseC] : (1 / 10 : ℝ) ≤ gamma6BaseC).trans hC
  have hDd := hD.trans gamma6Base_constants.2.2.2.2.1
  have hr := gamma6Base_section_regular hCc hCD hDd
  have hi := primeOrdered_integrable
    (primeOrdered_continuous_of_lipschitz (fun x _ y _ => hr.2 x y))
    ⟨hAa, hAB.trans hBb⟩ ⟨hAa.trans hAB, hBb⟩
  apply hi.congr
  intro t ht
  have ht' : t ∈ Icc A B := by simpa only [uIcc_of_le hAB] using uIoc_subset_uIcc ht
  dsimp only
  unfold gamma6BaseSection
  rw [← intervalIntegral.integral_div]
  apply intervalIntegral.integral_congr
  rw [uIcc_of_le hCD]
  intro u hu
  dsimp only
  rw [gamma6Base_H_eq (ht'.2.trans hB) (hu.2.trans hD)]
  simp only [gamma5MassKernel, div_eq_mul_inv, mul_inv]
  ring

end Wu2008DoubleSieve
