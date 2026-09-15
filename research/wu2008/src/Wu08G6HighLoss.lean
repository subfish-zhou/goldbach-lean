import Wu08G6HighSplit

/-! A proved explicit loss for the same finite staircase, not the difference of
unrelated upper and lower Q estimates. No numerical integration or table input. -/
namespace Wu08G6High
open Set MeasureTheory QuarterTrim DirectFiniteF6 Wu08G6TableGeometryRecovery
open scoped Classical
noncomputable section

/-- A finite, exactly defined height cap; no table values enter it. -/
def heightCap (w : Fin 21 → ℝ) : ℝ :=
  max 0 (Finset.univ.sup' Finset.univ_nonempty (fun j => |w j|))

theorem heightCap_nonneg (w : Fin 21 → ℝ) : 0 ≤ heightCap w := le_max_left _ _

theorem le_heightCap (w : Fin 21 → ℝ) (j : Fin 21) : |w j| ≤ heightCap w :=
  (Finset.le_sup' (f := fun j => |w j|) (Finset.mem_univ j)).trans (le_max_right _ _)

theorem profile_le_heightCap (w : Fin 21 → ℝ) (s : ℝ) : profile w s ≤ heightCap w :=
  (le_abs_self _).trans (eval_map_bounds _ (heightCap_nonneg w) (le_heightCap w) s)

theorem closed_high_in_published {x y : ℝ}
    (hx : x ∈ Icc alpha (1/4-2*alpha))
    (hy : y ∈ Icc (1/4) (1/2-2*alpha-x)) : (x,y) ∈ publishedReducedDomain := by
  have ha : 1/4-2*alpha ≤ beta := by norm_num [alpha,beta]
  have hb : beta ≤ (1:ℝ)/4 := by norm_num [beta]
  exact ⟨hx.1, hx.2.trans ha, hb.trans hy.1, by linarith [hy.2]⟩

/-- The denominator is uniformly positive also on the closed triangle. -/
theorem high_denominator {x y : ℝ}
    (hx : x ∈ Icc alpha (1/4-2*alpha))
    (hy : y ∈ Icc (1/4) (1/2-2*alpha-x)) :
    alpha^2/2 ≤ x*y*(1/2-x-y) := by
  have hz : 2*alpha ≤ 1/2-x-y := by linarith [hy.2]
  have hp : 0 ≤ x := alpha_pos.le.trans hx.1
  have hq : 0 ≤ y := by linarith [hy.1]
  have hxy := mul_le_mul hx.1 hy.1 (by norm_num : (0:ℝ) ≤ 1/4) hp
  have hh := mul_le_mul hxy hz (by have := alpha_pos; positivity : 0 ≤ 2*alpha)
    (mul_nonneg hp hq)
  nlinarith only [hh]

theorem high_kernel_upper {w : Fin 21 → ℝ} {K x y : ℝ} (hK : 0 ≤ K)
    (hw : profile w (u x y) ≤ K)
    (hx : x ∈ Icc alpha (1/4-2*alpha))
    (hy : y ∈ Icc (1/4) (1/2-2*alpha-x)) :
    kernel (profile w) x y ≤ 2*K/alpha^2 := by
  have hp := (published_denominator (closed_high_in_published hx hy)).1
  have hb := high_denominator hx hy
  change profile w (u x y) / (x*y*(1/2-x-y)) ≤ _
  apply (div_le_iff₀ hp).mpr
  have hc : 0 ≤ 2*K/alpha^2 := by positivity
  have hh := mul_le_mul_of_nonneg_left hb hc
  have he : (2*K/alpha^2)*(alpha^2/2) = K := by
    field_simp [alpha_pos.ne']
  rw [he] at hh
  exact hw.trans hh

theorem high_segment_integrable (w : Fin 21 → ℝ) {x : ℝ}
    (hx : x ∈ Icc alpha (1/4-2*alpha)) :
    IntervalIntegrable (kernel (profile w) x) volume (1/4) (1/2-2*alpha-x) := by
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith [hx.2])).mpr
  apply Measure.integrableOn_of_bounded (M := bound w) measure_Icc_lt_top.ne
    ((measurable_kernel w).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
  rw [Real.norm_eq_abs]
  exact published_kernel_abs w (closed_high_in_published hx hy)

theorem high_fibre_integrable (w : Fin 21 → ℝ) :
    IntervalIntegrable (highFibre w) volume alpha (1/4-2*alpha) := by
  have hi := (high_integrable w).integral_prod_left.intervalIntegrable
    (a := alpha) (b := 1/4-2*alpha)
  apply hi.congr
  intro x hx
  rw [uIoc_of_le high_x_bounds] at hx
  exact inner_high_eq w ⟨hx.1.le,hx.2⟩

theorem high_fibre_upper {w : Fin 21 → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hw : ∀ x ∈ Icc alpha (1/4-2*alpha), ∀ y ∈ Icc (1/4) (1/2-2*alpha-x),
      profile w (u x y) ≤ K) {x : ℝ} (hx : x ∈ Icc alpha (1/4-2*alpha)) :
    highFibre w x ≤ (1/4-2*alpha-x)*(2*K/alpha^2) := by
  have hi := intervalIntegral.integral_mono_on (by linarith [hx.2])
    (high_segment_integrable w hx) (intervalIntegrable_const (c := 2*K/alpha^2))
    (fun y hy => high_kernel_upper hK (hw x hx y hy) hx hy)
  change (∫ y in (1/4)..(1/2-2*alpha-x), kernel (profile w) x y) ≤ _
  rw [intervalIntegral.integral_const, smul_eq_mul] at hi
  convert hi using 1
  ring

/-- Exact triangle area, proved by polynomial FTC rather than sampled integration. -/
theorem triangle_area :
    (∫ x in alpha..(1/4-2*alpha), (1/4-2*alpha-x)) = (1/4-3*alpha)^2/2 := by
  have hi : IntervalIntegrable (fun x : ℝ => x) volume alpha (1/4-2*alpha) :=
    continuous_id.intervalIntegrable _ _
  rw [intervalIntegral.integral_sub intervalIntegrable_const hi,
    intervalIntegral.integral_const, integral_id, smul_eq_mul]
  ring

/-- A fully supplied loss bound. The only optional K is a pointwise height cap
of the very same profile on the missing triangle. -/
theorem highLoss_le {w : Fin 21 → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hw : ∀ x ∈ Icc alpha (1/4-2*alpha), ∀ y ∈ Icc (1/4) (1/2-2*alpha-x),
      profile w (u x y) ≤ K) :
    highLoss w ≤ (16129:ℝ)/40000*K := by
  rw [high_eq_fibres]
  have hi := intervalIntegral.integral_mono_on high_x_bounds
    (high_fibre_integrable w)
    (((continuous_const.sub continuous_id).mul continuous_const).intervalIntegrable
      (a := alpha) (b := 1/4-2*alpha))
    (fun x hx => high_fibre_upper hK hw hx)
  have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0:ℝ) ≤ 4)
  change 4*(∫ x in alpha..(1/4-2*alpha), highFibre w x) ≤
    4*(∫ x in alpha..(1/4-2*alpha), (1/4-2*alpha-x)*(2*K/alpha^2)) at h
  rw [intervalIntegral.integral_mul_const, triangle_area] at h
  convert h using 1
  norm_num [alpha]
  ring

theorem highLoss_le_heightCap (w : Fin 21 → ℝ) :
    highLoss w ≤ (16129:ℝ)/40000*heightCap w :=
  highLoss_le (heightCap_nonneg w) (fun x _ y _ => profile_le_heightCap w (u x y))

theorem legal_lower (w : Fin 21 → ℝ) :
    published w - (16129:ℝ)/40000*heightCap w ≤ Gamma w 0 := by
  have hs := published_eq_legal_add_high w
  have hl := highLoss_le_heightCap w
  linarith only [hs,hl]

#print axioms highLoss_le
#print axioms legal_lower
end
end Wu08G6High
