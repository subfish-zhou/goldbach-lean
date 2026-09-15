import MathlibNt.Wu2008DoubleSieve.SeventhEighthClassicalIntegral
import MathlibNt.Wu2008DoubleSieve.SeventhEighthClassicalQuadrature
import MathlibNt.Wu2008DoubleSieve.SeventhEighthClassicalMass

namespace Wu2008DoubleSieve.SeventhEighth
open Finset Set Real Filter MeasureTheory LiLiuPrereqBuchstab
open scoped Classical Topology Interval

noncomputable def pairTop (t : ℝ) : ℝ := (1 - t) / 2
/-- Upper clipping is enough: the denominator is positive even below the lower face. -/
noncomputable def pairKernel (t v : ℝ) : ℝ := 1 / (1 - t - min v (pairTop t))
noncomputable def pairLower7 (t : ℝ) : ℝ := max t (1 / 10)
noncomputable def pairLower8 (_t : ℝ) : ℝ := 1 / 3
noncomputable def pairInner (l : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ v in l t..pairTop t, pairKernel t v / v

theorem pair_min_lipschitz (c x y : ℝ) : |min x c - min y c| ≤ |x - y| := by
  by_cases hx : x ≤ c <;> by_cases hy : y ≤ c
  · simp only [min_eq_left hx, min_eq_left hy, le_refl]
  · rw [min_eq_left hx, min_eq_right (le_of_not_ge hy)]
    rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
    linarith
  · rw [min_eq_right (le_of_not_ge hx), min_eq_left hy]
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    linarith
  · simp only [min_eq_right (le_of_not_ge hx), min_eq_right (le_of_not_ge hy),
      sub_self, abs_zero, abs_nonneg]

theorem pairTop_bounds {t : ℝ} (ht : t ∈ Icc (1 / 15 : ℝ) (1 / 3)) :
    pairTop t ∈ Icc (1 / 10 : ℝ) (1 / 2) := by
  dsimp [pairTop]
  constructor <;> linarith [ht.1, ht.2]

theorem pairTop_lipschitz (x y : ℝ) : |pairTop x - pairTop y| = |x - y| / 2 := by
  unfold pairTop
  rw [← sub_div, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  rw [show (1 - x) - (1 - y) = -(x - y) by ring, abs_neg]

theorem pairLower7_bounds {t : ℝ} (ht : t ∈ Icc (1 / 15 : ℝ) (1 / 3)) :
    pairLower7 t ∈ Icc (1 / 10 : ℝ) (1 / 2) ∧ pairLower7 t ≤ pairTop t := by
  dsimp [pairLower7, pairTop]
  exact ⟨⟨le_max_right _ _, max_le (by linarith [ht.2]) (by norm_num)⟩,
    max_le (by linarith [ht.2]) (by linarith [ht.2])⟩

theorem pairLower7_lipschitz (x y : ℝ) : |pairLower7 x - pairLower7 y| ≤ |x - y| := by
  have h := pair_min_lipschitz (- (1 / 10)) (-x) (-y)
  simpa only [pairLower7, min_neg_neg, neg_sub_neg, abs_sub_comm] using h

theorem pairLower8_bounds {t : ℝ} (ht : t ∈ Icc (1 / 15 : ℝ) (1 / 3)) :
    pairLower8 t ∈ Icc (1 / 10 : ℝ) (1 / 2) ∧ pairLower8 t ≤ pairTop t := by
  dsimp [pairLower8, pairTop]
  exact ⟨⟨by norm_num, by norm_num⟩, by linarith [ht.2]⟩

theorem pairLower8_lipschitz (x y : ℝ) : |pairLower8 x - pairLower8 y| ≤ |x - y| := by
  simp only [pairLower8, sub_self, abs_zero, abs_nonneg]

theorem pairKernel_den {t v : ℝ} (ht : t ∈ Icc (1 / 15 : ℝ) (1 / 3)) :
    1 / 5 ≤ 1 - t - min v (pairTop t) := by
  have h := min_le_right v (pairTop t)
  dsimp [pairTop] at h ⊢
  linarith [ht.2]

theorem pairKernel_bound {t : ℝ} (ht : t ∈ Icc (1 / 15 : ℝ) (1 / 3)) (v : ℝ) :
    0 ≤ pairKernel t v ∧ |pairKernel t v| ≤ 5 := by
  have hd := pairKernel_den (v := v) ht
  have hp : 0 ≤ pairKernel t v := one_div_nonneg.mpr (by linarith)
  refine ⟨hp, ?_⟩
  rw [abs_of_nonneg hp]
  exact (div_le_iff₀ (by linarith : 0 < 1 - t - min v (pairTop t))).mpr (by linarith)

theorem pairKernel_lipschitz_second {t : ℝ}
    (ht : t ∈ Icc (1 / 15 : ℝ) (1 / 3)) (x y : ℝ) :
    |pairKernel t x - pairKernel t y| ≤ 25 * |x - y| := by
  have h := ninthMain_inverse_lipschitz (pairKernel_den (v := x) ht)
    (pairKernel_den (v := y) ht)
  rw [show (1 - t - min x (pairTop t)) - (1 - t - min y (pairTop t)) =
    min y (pairTop t) - min x (pairTop t) by ring, abs_sub_comm (min y (pairTop t))] at h
  exact h.trans (mul_le_mul_of_nonneg_left (pair_min_lipschitz _ x y) (by norm_num))

theorem pairKernel_lipschitz_first {x y : ℝ}
    (hx : x ∈ Icc (1 / 15 : ℝ) (1 / 3)) (hy : y ∈ Icc (1 / 15 : ℝ) (1 / 3)) (v : ℝ) :
    |pairKernel x v - pairKernel y v| ≤ 50 * |x - y| := by
  have h := ninthMain_inverse_lipschitz (pairKernel_den (v := v) hx)
    (pairKernel_den (v := v) hy)
  have hc := pair_min_lipschitz v (pairTop x) (pairTop y)
  rw [min_comm (pairTop x) v, min_comm (pairTop y) v, pairTop_lipschitz] at hc
  have htri := abs_add_le (y - x) (min v (pairTop y) - min v (pairTop x))
  rw [abs_sub_comm y x, abs_sub_comm (min v (pairTop y))] at htri
  rw [show (1 - x - min v (pairTop x)) - (1 - y - min v (pairTop y)) =
    (y - x) + (min v (pairTop y) - min v (pairTop x)) by ring] at h
  change |pairKernel x v - pairKernel y v| ≤ _ at h
  nlinarith [abs_nonneg (x-y)]

theorem pairKernel_continuous {t : ℝ} (ht : t ∈ Icc (1 / 15 : ℝ) (1 / 3)) :
    ContinuousOn (pairKernel t) (Icc (1 / 10 : ℝ) (1 / 2)) :=
  primeOrdered_continuous_of_lipschitz (fun x _ y _ => pairKernel_lipschitz_second ht x y)

theorem pairInner_regular (l : ℝ → ℝ)
    (hb : ∀ t ∈ Icc (1 / 15 : ℝ) (1 / 3), l t ∈ Icc (1 / 10 : ℝ) (1 / 2))
    (hl : ∀ x ∈ Icc (1 / 15 : ℝ) (1 / 3), ∀ y ∈ Icc (1 / 15 : ℝ) (1 / 3),
      |l x - l y| ≤ |x - y|) :
    (∀ t ∈ Icc (1 / 15 : ℝ) (1 / 3), |pairInner l t| ≤ 20) ∧
    (∀ x ∈ Icc (1 / 15 : ℝ) (1 / 3), ∀ y ∈ Icc (1 / 15 : ℝ) (1 / 3),
      |pairInner l x - pairInner l y| ≤ 300 * |x - y|) := by
  constructor
  · intro t ht
    simpa only [pairInner, show (4 : ℝ) * 5 = 20 by norm_num] using
      primeOrdered_integral_norm_le_four (hb t ht) (pairTop_bounds ht) (by norm_num)
        (fun v _ => (pairKernel_bound ht v).2)
  · intro x hx y hy
    have hc := pairKernel_continuous hy
    have hi (a b : ℝ) (ha : a ∈ Icc (1 / 10 : ℝ) (1 / 2))
        (hb' : b ∈ Icc (1 / 10 : ℝ) (1 / 2)) := primeOrdered_integrable hc ha hb'
    have h1 := primeOrdered_integral_sub_bound (pairKernel_continuous hx) hc
      (hb x hx) (pairTop_bounds hx) (by positivity : 0 ≤ 50 * |x-y|)
      (fun v _ => pairKernel_lipschitz_first hx hy v)
    have h2 := primeOrdered_integral_norm_le (hb y hy) (hb x hx)
      (fun v _ => (pairKernel_bound hy v).2)
    have h3 := primeOrdered_integral_norm_le (pairTop_bounds hy) (pairTop_bounds hx)
      (fun v _ => (pairKernel_bound hy v).2)
    have hadd1 := intervalIntegral.integral_add_adjacent_intervals
      (hi _ _ (hb y hy) (hb x hx)) (hi _ _ (hb x hx) (pairTop_bounds hx))
    have hadd2 := intervalIntegral.integral_add_adjacent_intervals
      (hi _ _ (hb y hy) (pairTop_bounds hy))
      (hi _ _ (pairTop_bounds hy) (pairTop_bounds hx))
    have heq : (∫ v in l x..pairTop x, pairKernel y v / v) -
        (∫ v in l y..pairTop y, pairKernel y v / v) =
        (∫ v in pairTop y..pairTop x, pairKernel y v / v) -
        (∫ v in l y..l x, pairKernel y v / v) := by linarith
    have htri := abs_sub_le
      (∫ v in l x..pairTop x, pairKernel x v / v)
      (∫ v in l x..pairTop x, pairKernel y v / v)
      (∫ v in l y..pairTop y, pairKernel y v / v)
    rw [heq] at htri
    have htri2 := abs_sub_le (∫ v in pairTop y..pairTop x, pairKernel y v / v) 0
      (∫ v in l y..l x, pairKernel y v / v)
    simp only [sub_zero, zero_sub, abs_neg] at htri2
    rw [pairTop_lipschitz] at h3
    have hll := hl x hx y hy
    change |pairInner l x - pairInner l y| ≤ _
    dsimp only [pairInner]
    nlinarith [abs_nonneg (x-y)]

theorem pairInner_continuous (l : ℝ → ℝ)
    (hb : ∀ t ∈ Icc (1 / 15 : ℝ) (1 / 3), l t ∈ Icc (1 / 10 : ℝ) (1 / 2))
    (hl : ∀ x ∈ Icc (1 / 15 : ℝ) (1 / 3), ∀ y ∈ Icc (1 / 15 : ℝ) (1 / 3),
      |l x - l y| ≤ |x - y|) :
    ContinuousOn (pairInner l) (Icc (1 / 15 : ℝ) (1 / 3)) := by
  apply (LipschitzOnWith.of_dist_le_mul (K := (300 : NNReal)) ?_).continuousOn
  simpa only [Real.dist_eq, NNReal.coe_ofNat] using (pairInner_regular l hb hl).2

/-- On each genuine slice, clipping is exactly the identity, including zero width. -/
theorem pairInner_div_eq_slice (l : ℝ → ℝ) (t : ℝ) (h : l t ≤ pairTop t) :
    pairInner l t / t = ∫ v in l t..pairTop t, classicalKernel t v := by
  unfold pairInner
  rw [← intervalIntegral.integral_div]
  apply intervalIntegral.integral_congr
  intro v hv
  rw [uIcc_of_le h] at hv
  simp only [pairKernel, min_eq_left hv.2, classicalKernel, div_div]
  congr 1
  ring

theorem J7_eq_pairInner : J7 = ∫ t in sigma..(1 / 3), pairInner pairLower7 t / t := by
  rw [J7_eq_triangle_integral]
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le classical_parameters.2.2.le] at ht
  have hlow : pairLower7 t = t := max_eq_left (by have := ht.1; norm_num [sigma, alpha] at this ⊢; linarith)
  have h := pairInner_div_eq_slice pairLower7 t (by rw [hlow]; dsimp [pairTop]; linarith [ht.2])
  rw [hlow] at h
  exact h.symm

theorem J8_eq_pairInner : J8 = ∫ t in alpha..(1 / 3), pairInner pairLower8 t / t := by
  rw [J8_eq_triangle_integral]
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le (classical_parameters.2.1.le.trans classical_parameters.2.2.le)] at ht
  exact (pairInner_div_eq_slice pairLower8 t (by dsimp [pairLower8, pairTop]; linarith [ht.2])).symm

/-- The regular extension used by outer quadrature is the original seventh
logarithmic weight on its actual interval. -/
theorem pairInner7_eq_log {t : ℝ} (ht : t ∈ Icc sigma (1 / 3 : ℝ)) :
    pairInner pairLower7 t = log ((1 - 2 * t) / t) / (1 - t) := by
  have ht0 : 0 < t := (classical_parameters.1.trans classical_parameters.2.1).trans_le ht.1
  have hlow : pairLower7 t = t := max_eq_left (by
    have hs : (1 / 10 : ℝ) ≤ sigma := by norm_num [sigma, alpha]
    exact hs.trans ht.1)
  have he := pairInner_div_eq_slice pairLower7 t
    (by rw [hlow]; dsimp [pairTop]; linarith [ht.2])
  rw [hlow] at he
  change pairInner pairLower7 t / t =
    ∫ v in t..((1-t)/2), classicalKernel t v at he
  rw [seventh_slice ht] at he
  have halg : log ((1 - 2 * t) / t) / (t * (1 - t)) =
      (log ((1 - 2 * t) / t) / (1 - t)) / t := by
    rw [div_div, mul_comm (1-t) t]
  rw [halg] at he
  exact (div_left_inj' ht0.ne').mp he

/-- The eighth extension likewise agrees with its literal logarithmic weight. -/
theorem pairInner8_eq_log {t : ℝ} (ht : t ∈ Icc alpha (1 / 3 : ℝ)) :
    pairInner pairLower8 t = log (2 - 3 * t) / (1 - t) := by
  have ht0 : 0 < t := classical_parameters.1.trans_le ht.1
  have he := pairInner_div_eq_slice pairLower8 t
    (by dsimp [pairLower8, pairTop]; linarith [ht.2])
  change pairInner pairLower8 t / t =
    ∫ v in (1 / 3 : ℝ)..((1-t)/2), classicalKernel t v at he
  rw [eighth_slice ht] at he
  have halg : log (2 - 3 * t) / (t * (1 - t)) =
      (log (2 - 3 * t) / (1 - t)) / t := by
    rw [div_div, mul_comm (1-t) t]
  rw [halg] at he
  exact (div_left_inj' ht0.ne').mp he

end Wu2008DoubleSieve.SeventhEighth
