import MathlibNt.Wu2008DoubleSieve.Gamma78GainApproximation

namespace Wu2008DoubleSieve

open Finset Set Real Filter MeasureTheory
open scoped Classical Topology

theorem gamma78Gain_rectangle_H {tri : Bool} (δ : ℝ) (r : Gamma78GainRectangle tri) :
    gamma5GainH δ r.s = wuImprovementLimit true δ r.s :=
  congrArg (wuImprovementLimit true δ) (gamma5Gain_clip_eq (gamma78Gain_rectangle_parameter r))

theorem gamma78Gain_approx_summand_integrable (δ : ℝ) (n : ℕ) (j : ℕ × ℕ) :
    Integrable ((truncatedSixthClosureCell n j).indicator
      (fun v => gamma5GainH δ (gamma78GainSample n j) * gamma5GainSmooth v)) := by
  apply IntegrableOn.integrable_indicator _ (truncatedSixthClosure_cell_measurable n j)
  exact ((continuous_const.mul gamma5Gain_smooth_continuous).continuousOn.integrableOn_compact
    (isCompact_Icc.prod isCompact_Icc)).mono_set
      (Set.prod_mono Ico_subset_Icc_self Ico_subset_Icc_self)

theorem gamma78Gain_approx_integral (tri : Bool) (δ : ℝ) (n : ℕ) :
    (∫ v : ℝ × ℝ, gamma78GainApprox tri δ n v) =
      ∑ j : {j // j ∈ gamma78GainInner tri n},
        wuImprovementLimit true δ (gamma78GainInnerRectangle tri n j).s *
          gamma5MassRectangleIntegral (gamma78GainInnerRectangle tri n j).box.A
            (gamma78GainInnerRectangle tri n j).box.B (gamma78GainInnerRectangle tri n j).box.C
            (gamma78GainInnerRectangle tri n j).box.D := by
  unfold gamma78GainApprox
  rw [integral_finsetSum _ (fun j _ => gamma78Gain_approx_summand_integrable δ n j)]
  rw [← Finset.sum_attach]
  change (∑ j : {j // j ∈ gamma78GainInner tri n}, _) = _
  apply sum_congr rfl
  intro j _
  let r := gamma78GainInnerRectangle tri n j
  have heq : (truncatedSixthClosureCell n j.val).indicator
      (fun v => gamma5GainH δ (gamma78GainSample n j.val) * gamma5GainSmooth v) =
      fun v => gamma5GainH δ r.s *
        (Ico r.box.A r.box.B ×ˢ Ico r.box.C r.box.D).indicator gamma5GainSmooth v := by
    funext v
    change (truncatedSixthClosureCell n j.val).indicator
      (fun v => gamma5GainH δ r.s * gamma5GainSmooth v) v =
        gamma5GainH δ r.s * (truncatedSixthClosureCell n j.val).indicator gamma5GainSmooth v
    by_cases hv : v ∈ truncatedSixthClosureCell n j.val
    · simp only [Set.indicator_of_mem hv]
    · simp only [Set.indicator_of_notMem hv,mul_zero]
  rw [heq,integral_const_mul,gamma5Gain_smooth_rectangle_indicator r.box.first.le r.box.second.le,
    gamma5Gain_smooth_rectangle_eq r.box.lower.le r.box.first.le r.box.ordered.le
      r.box.second.le r.box.upper.le,gamma78Gain_rectangle_H]

/-- Both full domains have constructed sufficient families; no family is an input. -/
theorem gamma78Gain_sufficient_family {δ ε : ℝ} (tri : Bool)
    (hδ : 0 < δ) (hδhi : δ < 1/2) (hε : 0 < ε) :
    ∃ n : ℕ, gamma78GainIntegral tri δ - ε <
      ∑ j : {j // j ∈ gamma78GainInner tri n},
        wuImprovementLimit true δ (gamma78GainInnerRectangle tri n j).s *
          gamma5MassRectangleIntegral (gamma78GainInnerRectangle tri n j).box.A
            (gamma78GainInnerRectangle tri n j).box.B (gamma78GainInnerRectangle tri n j).box.C
            (gamma78GainInnerRectangle tri n j).box.D := by
  obtain ⟨n,hn⟩ := ((gamma78Gain_approx_integral_tendsto tri hδ hδhi).eventually
    (lt_mem_nhds (sub_lt_self _ hε))).exists
  exact ⟨n,by rwa [gamma78Gain_approx_integral] at hn⟩

theorem gamma78Gain_inner_packings_disjoint {tri : Bool} {i N n : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hR : 1 < gamma5GainScale N δ V) (hΔ : 1 < Δ) :
    Pairwise (fun j l : {j // j ∈ gamma78GainInner tri n} =>
      Disjoint (gamma5GainPacking N δ Δ V (gamma78GainInnerRectangle tri n j).box)
        (gamma5GainPacking N δ Δ V (gamma78GainInnerRectangle tri n l).box)) := by
  intro j l hjl
  apply Finset.disjoint_left.mpr
  intro x hxj hxl
  have hj := (mem_product.mp (gamma5Gain_packing_coarse hR hΔ _ hxj)).2
  have hl := (mem_product.mp (gamma5Gain_packing_coarse hR hΔ _ hxl)).2
  have heq : j.val=l.val :=
    truncatedSixthClosure_cell_unique (n := n)
      (v := (gamma5MassCoordinate (gamma5GainScale N δ V) x.2.1,
        gamma5MassCoordinate (gamma5GainScale N δ V) x.2.2))
      ⟨gamma5Gain_window_coordinate hR (mem_product.mp hj).1,
        gamma5Gain_window_coordinate hR (mem_product.mp hj).2⟩
      ⟨gamma5Gain_window_coordinate hR (mem_product.mp hl).1,
        gamma5Gain_window_coordinate hR (mem_product.mp hl).2⟩
  exact hjl (Subtype.ext heq)

end Wu2008DoubleSieve
