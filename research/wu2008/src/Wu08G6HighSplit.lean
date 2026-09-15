import Wu08G6TableGeometryRecovery

/-! Exact same-profile decomposition of the full published reduced G6 domain.
The counting source is NOT enlarged. The high part is a debit, not a producer. -/
namespace Wu08G6High
open Set MeasureTheory QuarterTrim DirectFiniteF6 Wu08G6TableGeometryRecovery
open scoped Classical
noncomputable section

def highDomain : Set (ℝ × ℝ) := publishedReducedDomain ∩ {v | 1/4 < v.2}

def masked (S : Set (ℝ × ℝ)) (w : Fin 21 → ℝ) (v : ℝ × ℝ) : ℝ :=
  if v ∈ S then kernel (profile w) v.1 v.2 else 0

def published (w : Fin 21 → ℝ) : ℝ := 4 * ∫ v, masked publishedReducedDomain w v

def highLoss (w : Fin 21 → ℝ) : ℝ := 4 * ∫ v, masked highDomain w v

theorem published_measurable : MeasurableSet publishedReducedDomain := by
  exact (measurableSet_le measurable_const measurable_fst).inter
    ((measurableSet_le measurable_fst measurable_const).inter
    ((measurableSet_le measurable_const measurable_snd).inter
    (measurableSet_le (measurable_fst.add measurable_snd) measurable_const)))

theorem high_measurable : MeasurableSet highDomain :=
  published_measurable.inter (measurableSet_lt measurable_const measurable_snd)

theorem published_denominator {x y : ℝ} (h : (x,y) ∈ publishedReducedDomain) :
    0 < x*y*(1/2-x-y) ∧ 2*alpha^2*beta ≤ x*y*(1/2-x-y) := by
  obtain ⟨ha, _, hc, he⟩ := h
  have hx : 0 < x := alpha_pos.trans_le ha
  have hy : 0 < y := StaircaseShrink.fixed_bounds.1.trans_le hc
  have hz : 2*alpha ≤ 1/2-x-y := by linarith
  have hxy := mul_le_mul ha hc StaircaseShrink.fixed_bounds.1.le hx.le
  have hm := mul_le_mul hxy hz (by have := alpha_pos; positivity : 0 ≤ 2*alpha)
    (mul_nonneg hx.le hy.le)
  exact ⟨mul_pos (mul_pos hx hy) (by linarith [alpha_pos]), by nlinarith only [hm]⟩

theorem published_kernel_abs (w : Fin 21 → ℝ) {x y : ℝ}
    (h : (x,y) ∈ publishedReducedDomain) : |kernel (profile w) x y| ≤ bound w := by
  obtain ⟨hp,hb⟩ := published_denominator h
  change |profile w (u x y) / (x*y*(1/2-x-y))| ≤ _
  rw [abs_div, abs_of_pos hp]
  exact div_le_div₀ (mass_nonneg w) (profile_abs w _)
    (by have := alpha_pos; have := StaircaseShrink.fixed_bounds.1; positivity) hb

theorem masked_integrable (w : Fin 21 → ℝ) {S : Set (ℝ × ℝ)}
    (hS : MeasurableSet S) (hsub : S ⊆ publishedReducedDomain) :
    Integrable (masked S w) := by
  have hr : S ⊆ Icc alpha beta ×ˢ Icc beta (1/2) := by
    intro v hv
    obtain ⟨ha,hb,hc,hd⟩ := hsub hv
    exact ⟨⟨ha,hb⟩,hc,by linarith [alpha_pos]⟩
  apply (integrable_indicator_iff hS).mpr
  apply Measure.integrableOn_of_bounded (M := bound w)
    (ne_of_lt (lt_of_le_of_lt (measure_mono hr) (isCompact_Icc.prod isCompact_Icc).measure_lt_top))
    (measurable_kernel w).aestronglyMeasurable
  filter_upwards [ae_restrict_mem hS] with v hv
  exact (Real.norm_eq_abs _).symm ▸ published_kernel_abs w (hsub hv)

theorem published_integrable (w : Fin 21 → ℝ) : Integrable (masked publishedReducedDomain w) :=
  masked_integrable w published_measurable Subset.rfl

theorem high_integrable (w : Fin 21 → ℝ) : Integrable (masked highDomain w) :=
  masked_integrable w high_measurable inter_subset_left

theorem split_pointwise (w : Fin 21 → ℝ) (v : ℝ × ℝ) :
    masked publishedReducedDomain w v = uniform w 0 v + masked highDomain w v := by
  rw [uniform, actual_domain_eq_quarter_cut]
  by_cases hp : v ∈ publishedReducedDomain
  · simp only [masked, highDomain, mem_inter_iff, mem_ofPred_eq, hp, true_and, if_true]
    by_cases hy : v.2 ≤ 1/4
    · rw [if_pos hy, if_neg (not_lt.mpr hy), add_zero]
    · rw [if_neg hy, if_pos (lt_of_not_ge hy), zero_add]
  · simp only [masked, highDomain, mem_inter_iff, mem_ofPred_eq, hp, false_and, if_false, add_zero]

/-- Genuine Bochner integral equality; all three integrability obligations are proved. -/
theorem published_eq_legal_add_high (w : Fin 21 → ℝ) :
    published w = Gamma w 0 + highLoss w := by
  unfold published Gamma highLoss
  simp_rw [split_pointwise]
  rw [integral_add (uniform_integrable w le_rfl) (high_integrable w)]
  ring

theorem high_nonneg {w : Fin 21 → ℝ} (hw : ∀ j, 0 ≤ w j) : 0 ≤ highLoss w := by
  apply mul_nonneg (by norm_num)
  apply integral_nonneg
  intro v
  unfold masked
  split_ifs with hv
  · exact div_nonneg (profile_nonneg hw _) (published_denominator hv.1).1.le
  · exact le_rfl

/-- No endpoint discard: the high y fibre is literally Ioc, preserving y>1/4. -/
theorem high_iff (x y : ℝ) : (x,y) ∈ highDomain ↔
    x ∈ Icc alpha (1/4-2*alpha) ∧ y ∈ Ioc (1/4) (1/2-2*alpha-x) := by
  have hab : 1/4-2*alpha ≤ beta := by norm_num [alpha,beta]
  have hb : beta ≤ (1:ℝ)/4 := by norm_num [beta]
  simp only [highDomain, publishedReducedDomain, mem_inter_iff, mem_ofPred_eq, mem_Icc, mem_Ioc]
  constructor
  · rintro ⟨⟨ha,_,_,hd⟩,hy⟩
    exact ⟨⟨ha,by linarith⟩,hy,by linarith⟩
  · rintro ⟨⟨ha,hx⟩,hy,hd⟩
    exact ⟨⟨ha,hx.trans hab,hb.trans hy.le,by linarith⟩,hy⟩

theorem high_x_bounds : alpha ≤ 1/4-2*alpha := by norm_num [alpha]

def highFibre (w : Fin 21 → ℝ) (x : ℝ) : ℝ :=
  ∫ y in (1/4)..(1/2-2*alpha-x), kernel (profile w) x y

theorem inner_high_eq (w : Fin 21 → ℝ) {x : ℝ}
    (hx : x ∈ Icc alpha (1/4-2*alpha)) :
    (∫ y, masked highDomain w (x,y)) = highFibre w x := by
  have he : (fun y => masked highDomain w (x,y)) =
      (Ioc (1/4) (1/2-2*alpha-x)).indicator (kernel (profile w) x) := by
    funext y
    simp only [masked, high_iff, hx, true_and, indicator]
    split_ifs <;> rfl
  rw [he, integral_indicator measurableSet_Ioc]
  exact (intervalIntegral.integral_of_le (by linarith [hx.2])).symm

/-- Full two-dimensional weighted Fubini on precisely the missing triangle. -/
theorem high_eq_fibres (w : Fin 21 → ℝ) :
    highLoss w = 4 * ∫ x in alpha..(1/4-2*alpha), highFibre w x := by
  unfold highLoss
  rw [show (∫ v : ℝ × ℝ, masked highDomain w v) =
    ∫ x, ∫ y, masked highDomain w (x,y) from integral_prod _ (high_integrable w)]
  have hs : Function.support (fun x => ∫ y, masked highDomain w (x,y)) ⊆
      Icc alpha (1/4-2*alpha) := by
    intro x hx
    by_contra hn
    apply hx
    have he : (fun y => masked highDomain w (x,y)) = 0 := by
      funext y
      have hv : (x,y) ∉ highDomain := fun hv => hn ((high_iff x y).mp hv).1
      simp only [masked, if_neg hv, Pi.zero_apply]
    change (∫ y, masked highDomain w (x,y)) = 0
    rw [he]
    simp
  rw [Wu2008DoubleSieve.truncatedSixthMass_integral_eq_interval high_x_bounds hs]
  congr 1
  apply intervalIntegral.integral_congr
  intro x hx
  rw [uIcc_of_le high_x_bounds] at hx
  exact inner_high_eq w hx

#print axioms published_eq_legal_add_high
#print axioms high_eq_fibres
end
end Wu08G6High
