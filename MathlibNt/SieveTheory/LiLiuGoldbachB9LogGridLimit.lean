import MathlibNt.SieveTheory.LiLiuGoldbachB9LogGridRegion

open Finset MeasureTheory Set
open scoped ENNReal BigOperators Interval

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

noncomputable section

set_option maxHeartbeats 800000

open MathlibNt.SieveTheory.LiuWeight
open PrimeReciprocalLogRectangle


def goldbachB9LogGridUpperIntegrand (n : ℕ) (x : ℝ × ℝ) : ℝ :=
  ∑ q ∈ goldbachB9LogGridCells n,
    (1 / (1 - goldbachB9AlphaGridPoint n (q.1 + 1) -
      goldbachB9BetaGridPoint n (q.2 + 1))) *
      (goldbachB9LogGridCell n q).indicator liuLogDensity x

theorem goldbachB9LogIntegrand_eq (u v : ℝ) :
    liuLogIntegrand (u, v) = 1 / (u * v * (1 - u - v)) := by
  simp only [liuLogIntegrand, liuLogKernel, liuLogDensity, one_div, mul_inv]
  ring

theorem goldbachB9LogDensity_bounds {x : ℝ × ℝ}
    (hx : x ∈ goldbachB9LogAmbientBox) :
    0 ≤ liuLogDensity x ∧ liuLogDensity x ≤ 80 := by
  constructor
  · exact one_div_nonneg.mpr (mul_nonneg (by linarith [hx.1.1]) (by linarith [hx.2.1]))
  · convert liuLogDensity_le_of_lower_bounds
      (by norm_num : 0 < (1 / 20 : ℝ)) (by norm_num : 0 < (1 / 4 : ℝ))
      hx.1.1 hx.2.1 using 1
    norm_num

theorem goldbachB9LogKernel_bounds {x : ℝ × ℝ}
    (hx : x ∈ goldbachB9LogAmbientBox) :
    0 ≤ liuLogKernel x ∧ liuLogKernel x ≤ 6 := by
  have hg := goldbachB9LogAmbientBox_gap hx
  change 0 ≤ 1 / (1 - x.1 - x.2) ∧ 1 / (1 - x.1 - x.2) ≤ 6
  constructor
  · exact one_div_nonneg.mpr (by linarith)
  · rw [div_le_iff₀ (by linarith : 0 < 1 - x.1 - x.2)]
    linarith

theorem goldbachB9LogIntegrand_bounds {x : ℝ × ℝ}
    (hx : x ∈ goldbachB9LogAmbientBox) :
    0 ≤ liuLogIntegrand x ∧ liuLogIntegrand x ≤ 480 := by
  have hd := goldbachB9LogDensity_bounds hx
  have hk := goldbachB9LogKernel_bounds hx
  exact ⟨mul_nonneg hk.1 hd.1,
    (mul_le_mul hk.2 hd.2 hd.1 (by norm_num)).trans (by norm_num)⟩

theorem continuousOn_goldbachB9LogDensity :
    ContinuousOn liuLogDensity goldbachB9LogAmbientBox := by
  exact continuousOn_liuLogDensity_box (by norm_num) (by norm_num)

theorem continuousOn_goldbachB9LogKernel :
    ContinuousOn liuLogKernel goldbachB9LogAmbientBox := by
  exact continuousOn_liuLogKernel_box (by norm_num)

theorem continuousOn_goldbachB9LogIntegrand :
    ContinuousOn liuLogIntegrand goldbachB9LogAmbientBox :=
  continuousOn_goldbachB9LogKernel.mul continuousOn_goldbachB9LogDensity


theorem integrableOn_goldbachB9LogDensity {s : Set (ℝ × ℝ)}
    (hs : MeasurableSet s) (hsub : s ⊆ goldbachB9LogAmbientBox) :
    IntegrableOn liuLogDensity s := by
  exact continuousOn_goldbachB9LogDensity.integrableOn_of_subset_isCompact isCompact_goldbachB9LogAmbientBox hs hsub
    (ne_top_of_le_ne_top isCompact_goldbachB9LogAmbientBox.measure_ne_top (measure_mono hsub))

theorem integrableOn_goldbachB9LogIntegrand {s : Set (ℝ × ℝ)}
    (hs : MeasurableSet s) (hsub : s ⊆ goldbachB9LogAmbientBox) :
    IntegrableOn liuLogIntegrand s := by
  exact continuousOn_goldbachB9LogIntegrand.integrableOn_of_subset_isCompact isCompact_goldbachB9LogAmbientBox hs hsub
    (ne_top_of_le_ne_top isCompact_goldbachB9LogAmbientBox.measure_ne_top (measure_mono hsub))


theorem goldbachB9LogGridUpperIntegrand_eq_of_mem {n : ℕ} (hn : 0 < n)
    {q : Fin n × Fin n} (hq : q ∈ goldbachB9LogGridCells n)
    {x : ℝ × ℝ} (hx : x ∈ goldbachB9LogGridCell n q) :
    goldbachB9LogGridUpperIntegrand n x =
      (1 / (1 - goldbachB9AlphaGridPoint n (q.1 + 1) -
        goldbachB9BetaGridPoint n (q.2 + 1))) * liuLogDensity x := by
  unfold goldbachB9LogGridUpperIntegrand
  exact MathlibNt.Analysis.LogGridEstimates.weighted_sum_eq_of_mem _ _ _ _
    (goldbachB9LogGridCell_pairwiseDisjoint hn) hq hx


private theorem b9CornerKernel_le_six {n : ℕ} (hn : 0 < n) (q : Fin n × Fin n) :
    1 / (1 - goldbachB9AlphaGridPoint n (q.1 + 1) -
      goldbachB9BetaGridPoint n (q.2 + 1)) ≤ 6 := by
  have hg := goldbachB9LogGridCell_cornerGap_ge hn q
  rw [div_le_iff₀ (goldbachB9LogGridCell_cornerGap_pos hn q)]
  linarith

theorem goldbachB9LogGridUpperIntegrand_le {n : ℕ} (hn : 0 < n)
    {x : ℝ × ℝ} (hx : x ∈ goldbachB9LogGridRegion n) :
    goldbachB9LogGridUpperIntegrand n x ≤ 480 := by
  obtain ⟨q, hq, hxq⟩ := Set.mem_iUnion₂.mp hx
  rw [goldbachB9LogGridUpperIntegrand_eq_of_mem hn hq hxq]
  have hd := goldbachB9LogDensity_bounds (goldbachB9LogGridCell_subset_ambientBox hn q hxq)
  exact (mul_le_mul (b9CornerKernel_le_six hn q) hd.2 hd.1 (by norm_num)).trans
    (by norm_num)

theorem goldbachB9LogGrid_kernel_variation_step {n : ℕ} (hn : 0 < n)
    (q : Fin n × Fin n) {x : ℝ × ℝ} (hx : x ∈ goldbachB9LogGridCell n q) :
    0 ≤ 1 / (1 - goldbachB9AlphaGridPoint n (q.1 + 1) -
      goldbachB9BetaGridPoint n (q.2 + 1)) - liuLogKernel x ∧
    1 / (1 - goldbachB9AlphaGridPoint n (q.1 + 1) -
      goldbachB9BetaGridPoint n (q.2 + 1)) - liuLogKernel x ≤
        36 * (goldbachB9AlphaGridStep n + goldbachB9BetaGridStep n) := by
  simp only [goldbachB9LogGridCell, goldbachB9AlphaGridPoint_succ, goldbachB9BetaGridPoint_succ] at hx
  simp only [goldbachB9AlphaGridPoint_succ, goldbachB9BetaGridPoint_succ, liuLogKernel]
  apply MathlibNt.Analysis.LogGridEstimates.cell_reciprocal_variation hx
    (l := 1 / 6) (by norm_num) ?_ (by have := goldbachB9AlphaGridStep_pos hn; have := goldbachB9BetaGridStep_pos hn; positivity) ?_
  · have h := goldbachB9LogGridCell_cornerGap_ge hn q
    rw [goldbachB9AlphaGridPoint_succ, goldbachB9BetaGridPoint_succ] at h
    linarith
  · ring_nf
    exact le_rfl

theorem goldbachB9LogGrid_kernel_error (n : ℕ) :
    36 * (goldbachB9AlphaGridStep n + goldbachB9BetaGridStep n) =
      96 / (5 * (n : ℝ)) ∧ 96 / (5 * (n : ℝ)) ≤ 20 / (n : ℝ) := by
  constructor
  · unfold goldbachB9AlphaGridStep goldbachB9BetaGridStep
      goldbachB9AlphaGridWidth goldbachB9BetaGridWidth
    ring
  · have h : (96 / 5 : ℝ) ≤ 20 := by norm_num
    simpa only [div_div] using div_le_div_of_nonneg_right h (Nat.cast_nonneg n)

theorem goldbachB9LogGrid_kernel_variation {n : ℕ} (hn : 0 < n)
    (q : Fin n × Fin n) {x : ℝ × ℝ} (hx : x ∈ goldbachB9LogGridCell n q) :
    0 ≤ 1 / (1 - goldbachB9AlphaGridPoint n (q.1 + 1) -
      goldbachB9BetaGridPoint n (q.2 + 1)) - liuLogKernel x ∧
    1 / (1 - goldbachB9AlphaGridPoint n (q.1 + 1) -
      goldbachB9BetaGridPoint n (q.2 + 1)) - liuLogKernel x ≤ 20 / (n : ℝ) := by
  have h := goldbachB9LogGrid_kernel_variation_step hn q hx
  have he := goldbachB9LogGrid_kernel_error n
  rw [he.1] at h
  exact ⟨h.1, h.2.trans he.2⟩

theorem goldbachB9LogGridUpperIntegrand_le_integrand_add {n : ℕ} (hn : 0 < n)
    {x : ℝ × ℝ} (hx : x ∈ goldbachB9LogGridRegion n) :
    goldbachB9LogGridUpperIntegrand n x ≤ liuLogIntegrand x + 1600 / (n : ℝ) := by
  obtain ⟨q, hq, hxq⟩ := Set.mem_iUnion₂.mp hx
  rw [goldbachB9LogGridUpperIntegrand_eq_of_mem hn hq hxq]
  have hd := goldbachB9LogDensity_bounds (goldbachB9LogGridCell_subset_ambientBox hn q hxq)
  have hk := goldbachB9LogGrid_kernel_variation hn q hxq
  have h := MathlibNt.Analysis.LogGridEstimates.weighted_error hd.1 hd.2
    (by positivity : 0 ≤ 20 / (n : ℝ)) hk.2
  convert h using 1
  dsimp [liuLogIntegrand]
  ring


end

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig