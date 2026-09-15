import MathlibNt.Wu2008DoubleSieve.TruncatedSixthMassCount
import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.BoxIntegral.UnitPartition

/-!
# Almost-everywhere continuity for the actual polygon integrands

The discontinuities of the effective coefficient are countable.
Each vertical affine pullback is injective, so Fubini makes their
two-dimensional inverse image null. Polygon frontiers are null by
the existing convex-set theorem.
-/

namespace Wu2008DoubleSieve

open Set Real Filter MeasureTheory
open scoped Classical Topology

noncomputable def truncatedSixthMassDenominator (δ : ℝ) (v : ℝ × ℝ) : ℝ :=
  max truncatedSixthLowerAlpha v.1 * max truncatedSixthLowerBeta v.2 *
    max (2 * truncatedSixthLowerAlpha) (truncatedSixthLowerC δ - v.1 - v.2)

theorem truncatedSixthMass_denominator_pos (δ : ℝ) (v : ℝ × ℝ) :
    0 < truncatedSixthMassDenominator δ v := by
  have hα := truncatedSixthLower_parameters.1
  have hβ := hα.trans truncatedSixthLower_parameters.2.1
  exact mul_pos (mul_pos (hα.trans_le (le_max_left _ _)) (hβ.trans_le (le_max_left _ _)))
    ((mul_pos (by norm_num : (0 : ℝ) < 2) hα).trans_le (le_max_left _ _))

theorem truncatedSixthMass_denominator_eq {δ : ℝ} {v : ℝ × ℝ}
    (hδ : 0 ≤ δ) (hv : truncatedSixthLowerRegion δ v.1 v.2) :
    truncatedSixthMassDenominator δ v =
      v.1 * v.2 * (truncatedSixthLowerC δ - v.1 - v.2) := by
  simp only [truncatedSixthMassDenominator, max_eq_right hv.1,
    max_eq_right hv.2.2.1,
    max_eq_right (truncatedSixthLower_region_bounds hδ hv).2.2.1]

theorem truncatedSixthMass_regions_convex (δ : ℝ) :
    Convex ℝ {v : ℝ × ℝ | truncatedSixthLowerRegion δ v.1 v.2} ∧
      Convex ℝ {v : ℝ × ℝ | truncatedSixthLowerAdmissibleRegion δ v.1 v.2} := by
  have hR : Convex ℝ {v : ℝ × ℝ | truncatedSixthLowerRegion δ v.1 v.2} := by
    intro v hv w hw A B hA hB hsum
    have hlo {l x y : ℝ} (hx : l ≤ x) (hy : l ≤ y) : l ≤ A * x + B * y := by
      calc
        l = A * l + B * l := by rw [← add_mul, hsum, one_mul]
        _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hx hA) (mul_le_mul_of_nonneg_left hy hB)
    have hhi {u x y : ℝ} (hx : x ≤ u) (hy : y ≤ u) : A * x + B * y ≤ u := by
      calc
        _ ≤ A * u + B * u :=
          add_le_add (mul_le_mul_of_nonneg_left hx hA) (mul_le_mul_of_nonneg_left hy hB)
        _ = u := by rw [← add_mul, hsum, one_mul]
    change truncatedSixthLowerRegion δ (A * v.1 + B * w.1) (A * v.2 + B * w.2)
    refine ⟨hlo hv.1 hw.1, hhi hv.2.1 hw.2.1, hlo hv.2.2.1 hw.2.2.1,
      hhi hv.2.2.2.1 hw.2.2.2.1, ?_⟩
    nlinarith [hhi hv.2.2.2.2 hw.2.2.2.2]
  refine ⟨hR, ?_⟩
  intro v hv w hw A B hA hB hsum
  refine ⟨hR hv.1 hw.1 hA hB hsum, ?_⟩
  change A * v.2 + B * w.2 ≤ truncatedSixthLowerC δ / 2
  calc
    _ ≤ A * (truncatedSixthLowerC δ / 2) + B * (truncatedSixthLowerC δ / 2) :=
      add_le_add (mul_le_mul_of_nonneg_left hv.2 hA) (mul_le_mul_of_nonneg_left hw.2 hB)
    _ = _ := by rw [← add_mul, hsum, one_mul]

theorem truncatedSixthMass_monotone_affine_ae {g : ℝ → ℝ} (hg : Monotone g)
    (c α : ℝ) (hα : α ≠ 0) :
    ∀ᵐ v : ℝ × ℝ, ContinuousAt g ((c - v.1 - v.2) / α) := by
  have hcount : {s : ℝ | ¬ ContinuousAt g s}.Countable := hg.countable_not_continuousAt
  have hs : Measurable (fun v : ℝ × ℝ => (c - v.1 - v.2) / α) := by
    fun_prop
  have hm : MeasurableSet {v : ℝ × ℝ |
      ContinuousAt g ((c - v.1 - v.2) / α)} :=
    (measurableSet_of_continuousAt g).preimage hs
  change ∀ᵐ v : ℝ × ℝ ∂(volume.prod volume),
    ContinuousAt g ((c - v.1 - v.2) / α)
  rw [Measure.ae_prod_iff_ae_ae hm]
  apply Eventually.of_forall
  intro x
  have hinj : Function.Injective (fun y : ℝ => (c - x - y) / α) := by
    intro u v huv
    have h := (div_left_inj' hα).mp huv
    linarith
  have hc : {y : ℝ | ¬ ContinuousAt g ((c - x - y) / α)}.Countable :=
    hcount.preimage (f := fun y : ℝ => (c - x - y) / α) hinj
  exact ae_iff.mpr (hc.measure_zero volume)

theorem truncatedSixthMass_effective_pullback_ae {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 100) :
    ∀ᵐ v : ℝ × ℝ,
      ContinuousAt (truncatedSixthMassEffective δ) (truncatedSixthLowerS δ v.1 v.2) :=
  truncatedSixthMass_monotone_affine_ae (truncatedSixthMass_effective_monotone hδ hδhi)
    _ _ truncatedSixthLower_parameters.1.ne'

theorem truncatedSixthMass_indicator_continuousAt {f : (ℝ × ℝ) → ℝ}
    {S : Set (ℝ × ℝ)} {v : ℝ × ℝ}
    (hf : ContinuousAt f v) (hv : v ∉ frontier S) :
    ContinuousAt (S.indicator f) v := by
  by_cases hcl : v ∈ closure S
  · have hin : v ∈ interior S := by
      by_contra h
      exact hv ⟨hcl, h⟩
    apply hf.congr
    filter_upwards [isOpen_interior.mem_nhds hin] with w hw
    exact (indicator_of_mem (interior_subset hw) f).symm
  · apply (continuousAt_const : ContinuousAt (fun _ : ℝ × ℝ => (0 : ℝ)) v).congr
    filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hcl] with w hw
    exact (indicator_of_notMem (fun h => hw (subset_closure h)) f).symm

theorem truncatedSixthMass_kernels_ae_continuous {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 100) :
    (∀ᵐ v : ℝ × ℝ, ContinuousAt (truncatedSixthMassAKernel δ) v) ∧
      (∀ᵐ v : ℝ × ℝ, ContinuousAt (truncatedSixthMassAdmissibleKernel δ) v) := by
  let A := fun v : ℝ × ℝ =>
    wuLowerCoefficient (truncatedSixthMassClip (truncatedSixthLowerS δ v.1 v.2)) /
      truncatedSixthMassDenominator δ v
  let E := fun v : ℝ × ℝ =>
    truncatedSixthMassEffective δ (truncatedSixthLowerS δ v.1 v.2) /
      truncatedSixthMassDenominator δ v
  have hs : Continuous (fun v : ℝ × ℝ => truncatedSixthLowerS δ v.1 v.2) := by
    unfold truncatedSixthLowerS
    fun_prop
  have hd : Continuous (truncatedSixthMassDenominator δ) := by
    unfold truncatedSixthMassDenominator
    fun_prop
  have hA : Continuous A :=
    (truncatedSixthMass_clipped_classical_continuous.comp hs).div hd
      (fun v => (truncatedSixthMass_denominator_pos δ v).ne')
  have hAE : ∀ᵐ v : ℝ × ℝ, ContinuousAt E v := by
    filter_upwards [truncatedSixthMass_effective_pullback_ae hδ hδhi] with v hv
    exact (hv.comp (f := fun w : ℝ × ℝ => truncatedSixthLowerS δ w.1 w.2)
      hs.continuousAt).div hd.continuousAt
      (truncatedSixthMass_denominator_pos δ v).ne'
  have hAid : truncatedSixthMassAKernel δ =
      {v | truncatedSixthLowerRegion δ v.1 v.2}.indicator A := by
    funext v
    by_cases hv : truncatedSixthLowerRegion δ v.1 v.2
    · simp only [Set.indicator_apply, mem_ofPred_eq, if_pos hv,
        truncatedSixthMassAKernel, A,
        truncatedSixthMass_clip_eq (truncatedSixthLower_region_bounds hδ.le hv).2.2.2,
        truncatedSixthMass_denominator_eq hδ.le hv]
    · simp [truncatedSixthMassAKernel, hv]
  have hEid : truncatedSixthMassAdmissibleKernel δ =
      {v | truncatedSixthLowerAdmissibleRegion δ v.1 v.2}.indicator E := by
    funext v
    by_cases hv : truncatedSixthLowerAdmissibleRegion δ v.1 v.2
    · simp only [truncatedSixthMassAdmissibleKernel, Set.indicator_apply, mem_ofPred_eq,
        truncatedSixthMassAKernel, if_pos hv.1, truncatedSixthMassHKernel, if_pos hv,
        E, truncatedSixthMassEffective,
        truncatedSixthMass_clip_eq (truncatedSixthLower_region_bounds hδ.le hv.1).2.2.2,
        truncatedSixthMass_denominator_eq hδ.le hv.1, add_div]
    · simp [truncatedSixthMassAdmissibleKernel, hv]
  have hR := compl_mem_ae_iff.mpr ((truncatedSixthMass_regions_convex δ).1.addHaar_frontier volume)
  have hD := compl_mem_ae_iff.mpr ((truncatedSixthMass_regions_convex δ).2.addHaar_frontier volume)
  constructor
  · rw [hAid]
    filter_upwards [hR] with v hv
    exact truncatedSixthMass_indicator_continuousAt hA.continuousAt hv
  · rw [hEid]
    filter_upwards [hD, hAE] with v hv he
    exact truncatedSixthMass_indicator_continuousAt he hv

theorem truncatedSixthMass_other_kernels_ae_continuous {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 100) :
    (∀ᵐ v : ℝ × ℝ, ContinuousAt (truncatedSixthMassWedgeKernel δ) v) ∧
      (∀ᵐ v : ℝ × ℝ, ContinuousAt (truncatedSixthMassHKernel δ) v) := by
  let C := {v : ℝ × ℝ | truncatedSixthLowerAdmissibleRegion δ v.1 v.2}.indicator
    (truncatedSixthMassAKernel δ)
  have hc : ∀ᵐ v : ℝ × ℝ, ContinuousAt C v := by
    filter_upwards [(truncatedSixthMass_kernels_ae_continuous hδ hδhi).1,
      compl_mem_ae_iff.mpr ((truncatedSixthMass_regions_convex δ).2.addHaar_frontier volume)]
      with v hv hb
    exact truncatedSixthMass_indicator_continuousAt hv hb
  have hH : truncatedSixthMassHKernel δ = fun v => truncatedSixthMassAdmissibleKernel δ v - C v := by
    funext v
    by_cases hv : truncatedSixthLowerAdmissibleRegion δ v.1 v.2
    · simp [truncatedSixthMassAdmissibleKernel, C, hv]
    · simp [truncatedSixthMassAdmissibleKernel, truncatedSixthMassHKernel, C, hv]
  have hW : truncatedSixthMassWedgeKernel δ = fun v =>
      truncatedSixthMassAKernel δ v + truncatedSixthMassHKernel δ v -
        truncatedSixthMassAdmissibleKernel δ v := by
    funext v
    linarith [truncatedSixthMass_disjoint_kernel_identity δ v]
  have hHAE : ∀ᵐ v : ℝ × ℝ, ContinuousAt (truncatedSixthMassHKernel δ) v := by
    rw [hH]
    filter_upwards [(truncatedSixthMass_kernels_ae_continuous hδ hδhi).2, hc] with v hv hw
    exact hv.sub hw
  refine ⟨?_, hHAE⟩
  rw [hW]
  filter_upwards [(truncatedSixthMass_kernels_ae_continuous hδ hδhi).1, hHAE,
    (truncatedSixthMass_kernels_ae_continuous hδ hδhi).2] with v ha hh he
  exact (ha.add hh).sub he

end Wu2008DoubleSieve
