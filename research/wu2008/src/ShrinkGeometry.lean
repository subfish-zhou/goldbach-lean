import Wu08StaircaseIntegral

open Set MeasureTheory QuarterTrim

namespace StaircaseShrink

noncomputable def upper (t x : ℝ) : ℝ :=
  min ((1 / 2 - t) / 2) (1 / 2 - t - 2 * alpha - x)

def domain (t : ℝ) : Set (ℝ × ℝ) :=
  {v | v.1 ∈ Icc alpha beta ∧ v.2 ∈ Icc beta (upper t v.1)}

noncomputable def shiftedU (delta x y : ℝ) : ℝ :=
  (1 / 2 - delta - x - y) / alpha

noncomputable def bound : ℝ := q / (2 * alpha ^ 2 * beta)

theorem fixed_bounds : 0 < beta ∧ alpha < beta ∧ beta < 2 * alpha := by
  norm_num [alpha, beta]

theorem bound_pos : 0 < bound := by
  unfold bound
  exact div_pos q_pos (mul_pos (mul_pos (by norm_num) (sq_pos_of_pos alpha_pos)) fixed_bounds.1)

theorem upper_ge {t x : ℝ} (ht : t ≤ 1 / 1000) (hx : x ≤ beta) :
    beta ≤ upper t x := by
  apply le_min
  · norm_num [beta] at *
    linarith
  · norm_num [alpha, beta] at *
    linarith

theorem upper_mono {t x : ℝ} (ht : 0 ≤ t) : upper t x ≤ upper 0 x := by
  apply min_le_min <;> linarith

theorem upper_loss {t x : ℝ} (ht : 0 ≤ t) :
    0 ≤ upper 0 x - upper t x ∧ upper 0 x - upper t x ≤ t := by
  refine ⟨sub_nonneg.mpr (upper_mono ht), ?_⟩
  have h₁ := min_le_left ((1 / 2 - (0 : ℝ)) / 2) (1 / 2 - 0 - 2 * alpha - x)
  have h₂ := min_le_right ((1 / 2 - (0 : ℝ)) / 2) (1 / 2 - 0 - 2 * alpha - x)
  have h : upper 0 x - t ≤ upper t x := by
    apply le_min <;> dsimp [upper] at * <;> linarith
  linarith

theorem domain_iff (t x y : ℝ) : (x, y) ∈ domain t ↔
    alpha ≤ x ∧ x ≤ beta ∧ beta ≤ y ∧ y ≤ (1 / 2 - t) / 2 ∧
      x + y ≤ 1 / 2 - t - 2 * alpha := by
  simp only [domain, mem_ofPred_eq, mem_Icc, upper, le_min_iff]
  constructor
  · rintro ⟨⟨ha,hb⟩, hc, hd, he⟩
    exact ⟨ha,hb,hc,hd,by linarith⟩
  · rintro ⟨ha,hb,hc,hd,he⟩
    exact ⟨⟨ha,hb⟩,hc,hd,by linarith⟩

theorem domain_zero : domain 0 = goodP := by
  ext v
  rcases v with ⟨x,y⟩
  rw [domain_iff]
  simp only [goodP, originalP_eq_clippedP, clippedP, mem_inter_iff, mem_ofPred_eq]
  constructor
  · rintro ⟨ha,hb,hc,hd,he⟩
    exact ⟨⟨ha,hb,hc,by linarith⟩,by linarith⟩
  · rintro ⟨⟨ha,hb,hc,he⟩,hd⟩
    exact ⟨ha,hb,hc,by linarith,by linarith⟩

theorem domain_subset {t : ℝ} (ht : 0 ≤ t) : domain t ⊆ domain 0 := by
  intro v hv
  exact ⟨hv.1,hv.2.1,hv.2.2.trans (upper_mono ht)⟩

/-- Strict exponent budgets on the unchanged retained domain. -/
theorem source_budgets {t delta x y : ℝ} (_ht : 0 < t)
    (hd : 0 < delta) (hdt : delta ≤ t / 2) (h : (x,y) ∈ domain t) :
    x ≤ y ∧ 2 * y ≤ 1 / 2 - t ∧ 2 * y < 1 / 2 - delta ∧
    2 * x + y ≤ 1 / 2 - t - 2 * alpha + beta ∧
    2 * x + y < 1 / 2 - delta ∧
    x + y + alpha ≤ 1 / 2 - t - alpha ∧
    2 ≤ shiftedU delta x y ∧ shiftedU delta x y ≤ u x y := by
  obtain ⟨ha,hb,hc,hd',he⟩ := (domain_iff t x y).1 h
  have hab := fixed_bounds.2.2
  refine ⟨hb.trans hc, by linarith, by linarith, by linarith,
    by linarith, by linarith, ?_, ?_⟩
  · apply (le_div_iff₀ alpha_pos).2
    linarith
  · apply (div_le_div_iff_of_pos_right alpha_pos).2
    linarith

/-- Uniform majorant on the actual zero-parameter retained domain. -/
theorem kernel_bounds {x y : ℝ} (h : (x,y) ∈ domain 0) :
    0 ≤ kernel Wu08Staircase.profile x y ∧
      kernel Wu08Staircase.profile x y ≤ bound := by
  obtain ⟨ha,hb,hc,hd,he⟩ := (domain_iff 0 x y).1 h
  have hx0 := lt_of_lt_of_le alpha_pos ha
  have hy0 := lt_of_lt_of_le fixed_bounds.1 hc
  have hz : 2 * alpha ≤ 1 / 2 - x - y := by linarith
  have hz0 : 0 < 1 / 2 - x - y := lt_of_lt_of_le (mul_pos (by norm_num) alpha_pos) hz
  have hden0 : 0 < x * y * (1 / 2 - x - y) := mul_pos (mul_pos hx0 hy0) hz0
  have hxy : alpha * beta ≤ x * y := mul_le_mul ha hc (le_of_lt fixed_bounds.1) (le_of_lt hx0)
  have hden : 2 * alpha ^ 2 * beta ≤ x * y * (1 / 2 - x - y) := by
    have hm := mul_le_mul hxy hz (le_of_lt (mul_pos (by norm_num) alpha_pos))
      (le_of_lt (mul_pos hx0 hy0))
    nlinarith
  have hp := Wu08Staircase.profile_bounds (u x y)
  refine ⟨div_nonneg hp.1 (le_of_lt hden0), ?_⟩
  apply (div_le_iff₀ hden0).2
  have heq : bound * (2 * alpha ^ 2 * beta) = q := by
    unfold bound
    exact div_mul_cancel₀ _ (ne_of_gt (mul_pos (mul_pos (by norm_num)
      (sq_pos_of_pos alpha_pos)) fixed_bounds.1))
  exact hp.2.trans (heq ▸ mul_le_mul_of_nonneg_left hden (le_of_lt bound_pos))

end StaircaseShrink
