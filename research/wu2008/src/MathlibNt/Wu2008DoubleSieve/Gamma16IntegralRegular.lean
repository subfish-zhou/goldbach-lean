import MathlibNt.Wu2008DoubleSieve.Gamma16Kernel

/-! # Regularity of the three moving faces before outer prime quadrature -/

namespace Wu2008DoubleSieve

open Set Real MeasureTheory
open scoped Interval

theorem gamma16_upper_integral_regular
    {H : ℝ → ℝ → ℝ} {A M K : ℝ}
    (hA : A ∈ Icc (1 / 10 : ℝ) (1 / 2)) (hM : 0 ≤ M) (hK : 0 ≤ K)
    (hc : ∀ x ∈ Icc (1 / 10 : ℝ) (1 / 2),
      ContinuousOn (H x) (Icc (1 / 10 : ℝ) (1 / 2)))
    (hb : ∀ x ∈ Icc (1 / 10 : ℝ) (1 / 2),
      ∀ t ∈ Icc (1 / 10 : ℝ) (1 / 2), |H x t| ≤ M)
    (hl : ∀ x ∈ Icc (1 / 10 : ℝ) (1 / 2),
      ∀ y ∈ Icc (1 / 10 : ℝ) (1 / 2),
      ∀ t ∈ Icc (1 / 10 : ℝ) (1 / 2), |H x t - H y t| ≤ K * |x - y|) :
    (∀ x ∈ Icc (1 / 10 : ℝ) (1 / 2), |∫ t in A..x, H x t / t| ≤ 4 * M) ∧
    (∀ x ∈ Icc (1 / 10 : ℝ) (1 / 2),
      ∀ y ∈ Icc (1 / 10 : ℝ) (1 / 2),
      |(∫ t in A..x, H x t / t) - ∫ t in A..y, H y t / t| ≤
        (4 * K + 10 * M) * |x - y|) := by
  obtain ⟨h₁, h₂⟩ := primeOrdered_moving_integral_lipschitz hA hM hK hc hb hl
  constructor
  · intro x hx
    rw [intervalIntegral.integral_symm x A, abs_neg]
    exact h₁ x hx
  · intro x hx y hy
    rw [intervalIntegral.integral_symm x A, intervalIntegral.integral_symm y A,
      neg_sub_neg, abs_sub_comm]
    exact h₂ x hx y hy

noncomputable def gamma16OuterWeight (φ w : ℝ) : ℝ :=
  primeOrderedTripleIntegral gamma16Alpha w (gamma16ClippedKernel φ w)

theorem gamma16_outer_regular {P φ : ℝ} (hφ : 2 ≤ φ) (hP : φ ≤ P) :
    (∀ w ∈ Icc (1 / 10 : ℝ) (1 / 2), |gamma16OuterWeight φ w| ≤ 640) ∧
    (∀ w ∈ Icc (1 / 10 : ℝ) (1 / 2),
      ∀ w' ∈ Icc (1 / 10 : ℝ) (1 / 2),
      |gamma16OuterWeight φ w - gamma16OuterWeight φ w'| ≤
        (64 * (1000 * P + 200) + 4800) * |w - w'|) := by
  let K := 1000 * P + 200
  have hK : 0 ≤ K := by dsimp [K]; linarith
  have hf (w : ℝ) := gamma16_clipped_weight hφ hP w
  have hi (t : ℝ) (ht : t ∈ Icc (1 / 10 : ℝ) (1 / 2))
      (u : ℝ) (hu : u ∈ Icc (1 / 10 : ℝ) (1 / 2)) :=
    gamma16_upper_integral_regular (H := fun w v => gamma16ClippedKernel φ w t u v)
      hu (by norm_num : (0 : ℝ) ≤ 10) hK
      (fun w _ => primeOrdered_continuous_of_lipschitz ((hf w).third t ht u hu))
      (fun w _ v hv => (hf w).bound t ht u hu v hv)
      (fun w _ w' _ v _ => gamma16_clipped_fourth hφ hP t u v w w')
  have hm (t : ℝ) (ht : t ∈ Icc (1 / 10 : ℝ) (1 / 2)) :=
    gamma16_upper_integral_regular
      (H := fun w u => primeOrderedInnerIntegral w (gamma16ClippedKernel φ w) t u)
      ht (by norm_num : (0 : ℝ) ≤ 40) (show 0 ≤ 4 * K + 100 by positivity)
      (fun w hw => primeOrdered_continuous_of_lipschitz
        ((primeOrdered_inner_regular (hf w) (by norm_num) hK hw).2.2 t ht))
      (fun w hw u hu => by simpa only [primeOrderedInnerIntegral,
        show (4 : ℝ) * 10 = 40 by norm_num] using (hi t ht u hu).1 w hw)
      (fun w hw w' hw' u hu => by simpa only [primeOrderedInnerIntegral,
        show (10 : ℝ) * 10 = 100 by norm_num] using (hi t ht u hu).2 w hw w' hw')
  have ha : gamma16Alpha ∈ Icc (1 / 10 : ℝ) (1 / 2) :=
    ⟨gamma16_constants.1, gamma16_constants.2.1.trans gamma16_constants.2.2.1⟩
  have ho := gamma16_upper_integral_regular
    (H := fun w t => primeOrderedMiddleIntegral w (gamma16ClippedKernel φ w) t)
    ha (by norm_num : (0 : ℝ) ≤ 160)
    (show 0 ≤ 4 * (4 * K + 100) + 400 by positivity)
    (fun w hw => primeOrdered_continuous_of_lipschitz
      ((primeOrdered_middle_regular (hf w) (by norm_num) hK hw).2))
    (fun w hw t ht => by simpa only [primeOrderedMiddleIntegral,
      show (4 : ℝ) * 40 = 160 by norm_num] using (hm t ht).1 w hw)
    (fun w hw w' hw' t ht => by simpa only [primeOrderedMiddleIntegral,
      show (10 : ℝ) * 40 = 400 by norm_num] using (hm t ht).2 w hw w' hw')
  simpa only [gamma16OuterWeight, primeOrderedTripleIntegral,
    show (4 : ℝ) * 160 = 640 by norm_num,
    show 4 * (4 * (4 * K + 100) + 400) + 10 * 160 = 64 * K + 4800 by ring] using ho

theorem gamma16_outer_integrable {φ : ℝ} (hφ : 2 ≤ φ) :
    IntervalIntegrable (fun w => gamma16OuterWeight φ w / w)
      volume gamma16Alpha gamma16Beta := by
  have h := gamma16_outer_regular hφ (le_refl φ)
  exact primeOrdered_integrable (primeOrdered_continuous_of_lipschitz h.2)
    ⟨gamma16_constants.1, gamma16_constants.2.1.trans gamma16_constants.2.2.1⟩
    ⟨gamma16_constants.1.trans gamma16_constants.2.1, gamma16_constants.2.2.1⟩

end Wu2008DoubleSieve
