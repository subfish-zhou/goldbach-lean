import ShrinkIntegral
import ShrinkNodeTransfer
import MathlibNt.Wu2008DoubleSieve.TruncatedSixthZeroDeltaEndpoint
import MathlibNt.Wu2008DoubleSieve.ImprovementCrossUpper

open Set MeasureTheory QuarterTrim Wu2008DoubleSieve
open scoped Classical

namespace StaircaseActual
noncomputable section

/-- Only the original 21 finite node inequalities; no integral or count input. -/
def NodeCertificate (δ : ℝ) : Prop :=
  ∀ r ∈ Wu08Staircase.table, r.2.2 ≤ wuImprovementLimit false δ r.2.1

/-- An explicit entry point exposes every currently unsupplied Table 2 inequality. -/
theorem nodeCertificate_of_21 {δ : ℝ}
    (node01 : (211041 / 10000000 : ℝ) ≤ wuImprovementLimit false δ (21/10))
    (node02 : (191556 / 10000000 : ℝ) ≤ wuImprovementLimit false δ (22/10))
    (node03 : (173631 / 10000000 : ℝ) ≤ wuImprovementLimit false δ (23/10))
    (node04 : (157035 / 10000000 : ℝ) ≤ wuImprovementLimit false δ (24/10))
    (node05 : (141585 / 10000000 : ℝ) ≤ wuImprovementLimit false δ (25/10))
    (node06 : (127132 / 10000000 : ℝ) ≤ wuImprovementLimit false δ (26/10))
    (node07 : (113556 / 10000000 : ℝ) ≤ wuImprovementLimit false δ (27/10))
    (node08 : (100756 / 10000000 : ℝ) ≤ wuImprovementLimit false δ (28/10))
    (node09 : (88648 / 10000000 : ℝ) ≤ wuImprovementLimit false δ (29/10))
    (node10 : (77162 / 10000000 : ℝ) ≤ wuImprovementLimit false δ (30/10))
    (node11 : (66236 / 10000000 : ℝ) ≤ wuImprovementLimit false δ (31/10))
    (node12 : (55818 / 10000000 : ℝ) ≤ wuImprovementLimit false δ (32/10))
    (node13 : (46164 / 10000000 : ℝ) ≤ wuImprovementLimit false δ (33/10))
    (node14 : (37529 / 10000000 : ℝ) ≤ wuImprovementLimit false δ (34/10))
    (node15 : (30123 / 10000000 : ℝ) ≤ wuImprovementLimit false δ (35/10))
    (node16 : (23901 / 10000000 : ℝ) ≤ wuImprovementLimit false δ (36/10))
    (node17 : (18997 / 10000000 : ℝ) ≤ wuImprovementLimit false δ (37/10))
    (node18 : (15336 / 10000000 : ℝ) ≤ wuImprovementLimit false δ (38/10))
    (node19 : (12593 / 10000000 : ℝ) ≤ wuImprovementLimit false δ (39/10))
    (node20 : (10120 / 10000000 : ℝ) ≤ wuImprovementLimit false δ (40/10))
    (node21 : (8099 / 10000000 : ℝ) ≤ wuImprovementLimit false δ (41/10))
    : NodeCertificate δ := by
  intro r hr
  simp only [Wu08Staircase.table, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals subst r; first
    | exact node01
    | exact node02
    | exact node03
    | exact node04
    | exact node05
    | exact node06
    | exact node07
    | exact node08
    | exact node09
    | exact node10
    | exact node11
    | exact node12
    | exact node13
    | exact node14
    | exact node15
    | exact node16
    | exact node17
    | exact node18
    | exact node19
    | exact node20
    | exact node21

/-- The two literal retained domains coincide, including all boundary faces. -/
theorem domain_eq {t : ℝ} (ht : 0 ≤ t) : StaircaseShrink.domain t =
    {v : ℝ × ℝ | truncatedSixthLowerAdmissibleRegion t v.1 v.2} := by
  ext v
  rcases v with ⟨x,y⟩
  rw [StaircaseShrink.domain_iff]
  change (alpha ≤ x ∧ x ≤ beta ∧ beta ≤ y ∧ y ≤ (1/2-t)/2 ∧
    x+y ≤ 1/2-t-2*alpha) ↔
    (alpha ≤ x ∧ x ≤ beta ∧ beta ≤ y ∧ y ≤ 1/2-3*alpha ∧
      x+y ≤ 1/2-t-2*alpha) ∧ y ≤ (1/2-t)/2
  constructor
  · rintro ⟨ha,hb,hc,hd,he⟩
    exact ⟨⟨ha,hb,hc,by linarith,he⟩,hd⟩
  · rintro ⟨⟨ha,hb,hc,_,he⟩,hd⟩
    exact ⟨ha,hb,hc,hd,he⟩

theorem region_mono {δ t x y : ℝ} (h : δ ≤ t)
    (hv : truncatedSixthLowerAdmissibleRegion t x y) :
    truncatedSixthLowerAdmissibleRegion δ x y := by
  rcases hv with ⟨⟨ha,hb,hc,he,hf⟩,hg⟩
  refine ⟨⟨ha,hb,hc,he,?_⟩,?_⟩ <;>
    unfold truncatedSixthLowerC at * <;> linarith

theorem denominator_pos {δ x y : ℝ} (hδ : 0 ≤ δ)
    (hv : truncatedSixthLowerAdmissibleRegion δ x y) :
    0 < x*y*(truncatedSixthLowerC δ-x-y) := by
  have hb := truncatedSixthLower_region_bounds hδ hv.1
  have ha := truncatedSixthLower_parameters.1
  exact mul_pos (mul_pos hb.1 hb.2.1) (by linarith [hb.2.2.1])

/-- Frozen zero-shift kernel on the true retained domain. -/
def uniformKernel (t : ℝ) (v : ℝ × ℝ) : ℝ :=
  if v ∈ StaircaseShrink.domain t then kernel Wu08Staircase.profile v.1 v.2 else 0

theorem uniform_nonneg {t : ℝ} (ht : 0 ≤ t) (v : ℝ × ℝ) :
    0 ≤ uniformKernel t v := by
  unfold uniformKernel
  split_ifs with hv
  · exact (StaircaseShrink.kernel_bounds (StaircaseShrink.domain_subset ht hv)).1
  · exact le_rfl

theorem uniform_measurable {t : ℝ} (ht : 0 ≤ t) : Measurable (uniformKernel t) := by
  exact Wu08Staircase.measurable_kernel.ite
    (by rw [domain_eq ht]; exact (truncatedSixthMass_regions_measurable t).2) measurable_const

/-- Actual h monotonicity is proved upstream; the only supplied facts are finite nodes. -/
theorem profile_lower {δ t x y : ℝ} (ht : 0 < t) (ht' : t ≤ 1/1000)
    (hδ : 0 < δ) (hδt : δ ≤ t/2) (hn : NodeCertificate δ)
    (hv : (x,y) ∈ StaircaseShrink.domain t) :
    Wu08Staircase.profile (u x y) ≤ wuImprovementLimit false δ (truncatedSixthLowerS δ x y) := by
  have hm : AntitoneOn (wuImprovementLimit false δ) (Icc 2 (41/10)) := by
    apply (wuImprovementLimit_lower_antitone hδ (by linarith)).mono
    intro s hs
    exact ⟨hs.1,by linarith [hs.2]⟩
  exact StaircaseShrink.profile_le_shifted_h (wuImprovementLimit false δ) hm
    (fun s hs => wuImprovementLimit_nonneg false hδ (by linarith)
      (by linarith [hs.1]) (by linarith [hs.2])) hn ht hδ hδt hv

/-- Pointwise comparison pays both the argument shift and the smaller denominator. -/
theorem uniform_le_actual {δ t : ℝ} (ht : 0 < t) (ht' : t ≤ 1/1000)
    (hδ : 0 < δ) (hδt : δ ≤ t/2) (hn : NodeCertificate δ) (v : ℝ × ℝ) :
    uniformKernel t v ≤ truncatedSixthMassHKernel δ v := by
  by_cases hv : v ∈ StaircaseShrink.domain t
  · have hvt : truncatedSixthLowerAdmissibleRegion t v.1 v.2 := by
      have he := congrArg (fun S : Set (ℝ × ℝ) => v ∈ S) (domain_eq ht.le)
      exact he.mp hv
    have hvδ := region_mono (show δ ≤ t by linarith) hvt
    rw [uniformKernel, if_pos hv, truncatedSixthMassHKernel, if_pos hvδ]
    have hb := truncatedSixthLower_region_bounds hδ.le hvδ.1
    have hz : v.1*v.2*(truncatedSixthLowerC δ-v.1-v.2) ≤
        v.1*v.2*(1/2-v.1-v.2) := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hb.1.le hb.2.1.le)
      unfold truncatedSixthLowerC
      linarith
    exact div_le_div₀ (wuImprovementLimit_nonneg false hδ (by linarith)
      (by linarith [hb.2.2.2.1]) (by linarith [hb.2.2.2.2]))
      (profile_lower ht ht' hδ hδt hn hv) (denominator_pos hδ.le hvδ) hz
  · rw [uniformKernel, if_neg hv]
    exact (truncatedSixthMass_kernels_bounds hδ (by linarith) v).2.1

theorem uniform_integrable {t : ℝ} (ht : 0 ≤ t) :
    Integrable (uniformKernel t) := by
  have hs : MeasurableSet (StaircaseShrink.domain t) := by
    rw [domain_eq ht]
    exact (truncatedSixthMass_regions_measurable t).2
  have hsub : StaircaseShrink.domain t ⊆ (Icc alpha beta) ×ˢ (Icc beta (1/4)) := by
    intro v hv
    have hh := (StaircaseShrink.domain_iff t v.1 v.2).1 hv
    exact ⟨hv.1,hh.2.2.1,by linarith [hh.2.2.2.1]⟩
  have hi : IntegrableOn (fun v : ℝ × ℝ => kernel Wu08Staircase.profile v.1 v.2)
      (StaircaseShrink.domain t) volume := by
    apply Measure.integrableOn_of_bounded (M := StaircaseShrink.bound)
      (ne_of_lt (lt_of_le_of_lt (measure_mono hsub)
        (isCompact_Icc.prod isCompact_Icc).measure_lt_top))
      Wu08Staircase.measurable_kernel.aestronglyMeasurable
    filter_upwards [ae_restrict_mem hs] with v hv
    have hb := StaircaseShrink.kernel_bounds (StaircaseShrink.domain_subset ht hv)
    rw [Real.norm_eq_abs,abs_of_nonneg hb.1]
    exact hb.2
  exact (integrable_indicator_iff hs).2 hi

end
end StaircaseActual
