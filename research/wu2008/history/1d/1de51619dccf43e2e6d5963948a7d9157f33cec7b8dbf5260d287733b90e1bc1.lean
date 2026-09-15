import MathlibNt.Wu2008DoubleSieve.Gamma5GainApproximation
import MathlibNt.Wu2008DoubleSieve.Gamma5GainMass

namespace Wu2008DoubleSieve

open Finset Set Real Filter MeasureTheory
open scoped Classical Topology

theorem gamma5Gain_rectangle_H (δ : ℝ) (r : Gamma5GainRectangle) :
    gamma5GainH δ r.s = wuImprovementLimit true δ r.s := by
  exact congrArg (wuImprovementLimit true δ)
    (gamma5Gain_clip_eq ⟨(gamma5Gain_rectangle_bounds r).2.2.2.2.2.1.le, r.parameter.le⟩)

theorem gamma5Gain_approx_summand_integrable (δ : ℝ) (n : ℕ) (j : ℕ × ℕ) :
    Integrable ((truncatedSixthClosureCell n j).indicator
      (fun v => gamma5GainH δ (gamma5GainSample n j) * gamma5GainSmooth v)) := by
  apply IntegrableOn.integrable_indicator _ (truncatedSixthClosure_cell_measurable n j)
  exact (((continuous_const.mul gamma5Gain_smooth_continuous).continuousOn.integrableOn_compact
    (isCompact_Icc.prod isCompact_Icc)).mono_set
      (Set.prod_mono Ico_subset_Icc_self Ico_subset_Icc_self))

theorem gamma5Gain_approx_integral (δ : ℝ) (n : ℕ) :
    (∫ v : ℝ × ℝ, gamma5GainApprox δ n v) =
      ∑ j : {j // j ∈ gamma5GainInner n},
        wuImprovementLimit true δ (gamma5GainInnerRectangle n j).s *
          gamma5MassRectangleIntegral (gamma5GainInnerRectangle n j).A
            (gamma5GainInnerRectangle n j).B (gamma5GainInnerRectangle n j).C
            (gamma5GainInnerRectangle n j).D := by
  unfold gamma5GainApprox
  rw [integral_finsetSum _ (fun j _ => gamma5Gain_approx_summand_integrable δ n j)]
  rw [← Finset.sum_attach]
  change (∑ j : {j // j ∈ gamma5GainInner n}, _) = _
  apply sum_congr rfl
  intro j _
  let r := gamma5GainInnerRectangle n j
  have heq : (truncatedSixthClosureCell n j.val).indicator
      (fun v => gamma5GainH δ (gamma5GainSample n j.val) * gamma5GainSmooth v) =
      fun v => gamma5GainH δ r.s *
        (Ico r.A r.B ×ˢ Ico r.C r.D).indicator gamma5GainSmooth v := by
    funext v
    change (truncatedSixthClosureCell n j.val).indicator
      (fun v => gamma5GainH δ r.s * gamma5GainSmooth v) v =
        gamma5GainH δ r.s * (truncatedSixthClosureCell n j.val).indicator gamma5GainSmooth v
    by_cases hv : v ∈ truncatedSixthClosureCell n j.val
    · simp only [Set.indicator_of_mem hv]
    · simp only [Set.indicator_of_notMem hv, mul_zero]
  rw [heq, integral_const_mul, gamma5Gain_smooth_rectangle_indicator r.first.le r.second.le,
    gamma5Gain_smooth_rectangle_eq r.lower.le r.first.le r.ordered.le r.second.le r.upper.le,
    gamma5Gain_rectangle_H]

theorem gamma5Gain_sufficient_family {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hε : 0 < ε) :
    ∃ n : ℕ, gamma5GainIntegral δ - ε <
      ∑ j : {j // j ∈ gamma5GainInner n},
        wuImprovementLimit true δ (gamma5GainInnerRectangle n j).s *
          gamma5MassRectangleIntegral (gamma5GainInnerRectangle n j).A
            (gamma5GainInnerRectangle n j).B (gamma5GainInnerRectangle n j).C
            (gamma5GainInnerRectangle n j).D := by
  obtain ⟨n, hn⟩ := ((gamma5Gain_approx_integral_tendsto hδ hδhi).eventually
    (lt_mem_nhds (sub_lt_self _ hε))).exists
  exact ⟨n, by rwa [gamma5Gain_approx_integral] at hn⟩

theorem gamma5Gain_inner_packings_disjoint {i N n : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hR : 1 < gamma5GainScale N δ V) (hΔ : 1 < Δ) :
    Pairwise (fun j l : {j // j ∈ gamma5GainInner n} =>
      Disjoint (gamma5GainPacking N δ Δ V (gamma5GainInnerRectangle n j))
        (gamma5GainPacking N δ Δ V (gamma5GainInnerRectangle n l))) := by
  intro j l hjl
  apply Finset.disjoint_left.mpr
  intro x hxj hxl
  have hj := (mem_product.mp (gamma5Gain_packing_coarse hR hΔ _ hxj)).2
  have hl := (mem_product.mp (gamma5Gain_packing_coarse hR hΔ _ hxl)).2
  have heq : j.val = l.val :=
    truncatedSixthClosure_cell_unique (n := n)
      (v := (gamma5MassCoordinate (gamma5GainScale N δ V) x.2.1,
        gamma5MassCoordinate (gamma5GainScale N δ V) x.2.2))
      ⟨gamma5Gain_window_coordinate hR (mem_product.mp hj).1,
        gamma5Gain_window_coordinate hR (mem_product.mp hj).2⟩
      ⟨gamma5Gain_window_coordinate hR (mem_product.mp hl).1,
        gamma5Gain_window_coordinate hR (mem_product.mp hl).2⟩
  exact hjl (Subtype.ext heq)

end Wu2008DoubleSieve
