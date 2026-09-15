import MathlibNt.Wu2008DoubleSieve.Gamma6GainApproximation
import MathlibNt.Wu2008DoubleSieve.Gamma6GainMass

namespace Wu2008DoubleSieve

open Finset Set Real Filter MeasureTheory
open scoped Classical Topology

theorem gamma6Gain_rectangle_H (δ : ℝ) (r : Gamma6GainRectangle) :
    gamma5GainH δ r.s = wuImprovementLimit true δ r.s :=
  congrArg (wuImprovementLimit true δ)
    (gamma5Gain_clip_eq ⟨(gamma6Gain_rectangle_bounds r).2.2.2.2.2.2.2.le, r.parameter.le⟩)

theorem gamma6Gain_approx_integral (δ : ℝ) (n : ℕ) :
    (∫ v : ℝ × ℝ, gamma6GainApprox δ n v) =
      ∑ j : {j // j ∈ gamma6GainInner n},
        wuImprovementLimit true δ (gamma6GainInnerRectangle n j).s *
          gamma6BaseIntegral (gamma6GainInnerRectangle n j).A
            (gamma6GainInnerRectangle n j).B (gamma6GainInnerRectangle n j).C
            (gamma6GainInnerRectangle n j).D := by
  unfold gamma6GainApprox
  rw [integral_finsetSum _ (fun j _ => gamma5Gain_approx_summand_integrable δ n j)]
  rw [← Finset.sum_attach]
  change (∑ j : {j // j ∈ gamma6GainInner n}, _) = _
  apply sum_congr rfl
  intro j _
  let r := gamma6GainInnerRectangle n j
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
    gamma6Gain_smooth_rectangle_eq r.lower.le r.first.le r.firstUpper.le
      r.secondLower.le r.second.le r.upper.le, gamma6Gain_rectangle_H]

/-- A constructed sufficient family, with no family or approximation premise. -/
theorem gamma6Gain_sufficient_family {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hε : 0 < ε) :
    ∃ n : ℕ, gamma6GainIntegral δ - ε <
      ∑ j : {j // j ∈ gamma6GainInner n},
        wuImprovementLimit true δ (gamma6GainInnerRectangle n j).s *
          gamma6BaseIntegral (gamma6GainInnerRectangle n j).A
            (gamma6GainInnerRectangle n j).B (gamma6GainInnerRectangle n j).C
            (gamma6GainInnerRectangle n j).D := by
  obtain ⟨n, hn⟩ := ((gamma6Gain_approx_integral_tendsto hδ hδhi).eventually
    (lt_mem_nhds (sub_lt_self _ hε))).exists
  exact ⟨n, by rwa [gamma6Gain_approx_integral] at hn⟩

theorem gamma6Gain_inner_packings_disjoint {i N n : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hR : 1 < gamma5GainScale N δ V) (hΔ : 1 < Δ) :
    Pairwise (fun j l : {j // j ∈ gamma6GainInner n} =>
      Disjoint (gamma6GainPacking N δ Δ V (gamma6GainInnerRectangle n j))
        (gamma6GainPacking N δ Δ V (gamma6GainInnerRectangle n l))) := by
  intro j l hjl
  apply Finset.disjoint_left.mpr
  intro x hxj hxl
  have hj := (mem_product.mp (gamma6Gain_packing_coarse hR hΔ _ hxj)).2
  have hl := (mem_product.mp (gamma6Gain_packing_coarse hR hΔ _ hxl)).2
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
