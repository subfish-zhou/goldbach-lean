import MathlibNt.SieveTheory.Liu.PrimePairs.LiuLogCoordinates
import MathlibNt.Analysis.LogGridEstimates
import MathlibNt.Analysis.MovingIntervalIntegral
import MathlibNt.SieveTheory.Liu.PrimePairs.LiuPrimePairLogGrid
import MathlibNt.SieveTheory.Liu.Weights.LiuWeightMainIntegral

/-!
# The canonical logarithmic grid tends to Liu's source integral

This file interprets each logarithmic rectangle mass as an actual integral,
checks the half-open grid partition, and compares the resulting upper sum with
the integral on Liu's triangular source region.
-/

open Filter Finset MeasureTheory Set
open scoped BigOperators Interval Topology

namespace MathlibNt.SieveTheory.LiuWeight

noncomputable section

open PrimeReciprocalLogRectangle

/-- A half-open canonical grid cell. -/
def liuLogGridCell (n : ℕ) (q : Fin n × Fin n) : Set (ℝ × ℝ) :=
  Ioc (liuAlphaGridPoint n q.1) (liuAlphaGridPoint n (q.1 + 1)) ×ˢ
    Ioc (liuBetaGridPoint n q.2) (liuBetaGridPoint n (q.2 + 1))

/-- The union of the cells selected by their lower-left corners. -/
def liuLogGridRegion (n : ℕ) : Set (ℝ × ℝ) :=
  ⋃ q ∈ liuLogGridCells n, liuLogGridCell n q

/-- The exact half-open source region from Liu's integral. -/
def liuLogSourceRegion : Set (ℝ × ℝ) :=
  {x | x.1 ∈ Ioc (1 / 10 : ℝ) (1 / 3) ∧
    x.2 ∈ Ioc (1 / 3 : ℝ) ((1 - x.1) / 2)}


/-- Canonical half-open cells are measurable. -/
lemma measurableSet_liuLogGridCell (n : ℕ) (q : Fin n × Fin n) :
    MeasurableSet (liuLogGridCell n q) :=
  measurableSet_Ioc.prod measurableSet_Ioc

private lemma liuAlphaGridPoint_mono {n i j : ℕ} (hn : 0 < n) (hij : i ≤ j) :
    liuAlphaGridPoint n i ≤ liuAlphaGridPoint n j := by
  rw [liuAlphaGridPoint_eq_step hn, liuAlphaGridPoint_eq_step hn]
  have hij' : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
  have := mul_le_mul_of_nonneg_right hij' (liuAlphaGridStep_pos hn).le
  linarith

private lemma liuBetaGridPoint_mono {n i j : ℕ} (hn : 0 < n) (hij : i ≤ j) :
    liuBetaGridPoint n i ≤ liuBetaGridPoint n j := by
  rw [liuBetaGridPoint_eq_step hn, liuBetaGridPoint_eq_step hn]
  have hij' : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
  have := mul_le_mul_of_nonneg_right hij' (liuBetaGridStep_pos hn).le
  linarith

/-- The strict-left/non-strict-right convention makes distinct cells genuinely
disjoint, including on all grid lines. -/
theorem liuLogGridCell_pairwiseDisjoint {n : ℕ} (hn : 0 < n) :
    (Set.univ : Set (Fin n × Fin n)).Pairwise
      (Function.onFun Disjoint (liuLogGridCell n)) := by
  exact MathlibNt.Analysis.LogGridEstimates.cells_pairwiseDisjoint n
    (liuAlphaGridPoint n) (liuBetaGridPoint n)
    (fun _ _ h => liuAlphaGridPoint_mono hn h)
    (fun _ _ h => liuBetaGridPoint_mono hn h)

/-- Every source point is in a selected half-open cell.  This is the geometric
counterpart of the prime-pair cover and fixes all boundary conventions. -/
theorem liuLogSourceRegion_subset_gridRegion {n : ℕ} (hn : 0 < n) :
    liuLogSourceRegion ⊆ liuLogGridRegion n := by
  intro x hx
  have haend :
      x.1 ≤ 1 / 10 + (n : ℝ) * liuAlphaGridStep n := by
    rw [show 1 / 10 + (n : ℝ) * liuAlphaGridStep n = (1 / 3 : ℝ) by
      unfold liuAlphaGridStep
      field_simp [Nat.cast_ne_zero.mpr hn.ne']
      ring]
    exact hx.1.2
  have hbend :
      x.2 ≤ 1 / 3 + (n : ℝ) * liuBetaGridStep n := by
    rw [show 1 / 3 + (n : ℝ) * liuBetaGridStep n = (9 / 20 : ℝ) by
      unfold liuBetaGridStep
      field_simp [Nat.cast_ne_zero.mpr hn.ne']
      ring]
    linarith [hx.1.1, hx.2.2]
  obtain ⟨i, hi, hail, haiu⟩ :=
    exists_nat_cell n (liuAlphaGridStep_pos hn) hx.1.1 haend
  obtain ⟨j, hj, hbjl, hbju⟩ :=
    exists_nat_cell n (liuBetaGridStep_pos hn) hx.2.1 hbend
  let fi : Fin n := ⟨i, hi⟩
  let fj : Fin n := ⟨j, hj⟩
  have hselected :
      liuBetaGridPoint n fj < (1 - liuAlphaGridPoint n fi) / 2 := by
    rw [liuAlphaGridPoint_eq_step hn, liuBetaGridPoint_eq_step hn]
    dsimp [fi, fj]
    nlinarith [hx.2.2]
  rw [liuLogGridRegion]
  refine Set.mem_iUnion.2 ⟨(fi, fj), Set.mem_iUnion.2 ⟨?_, ?_⟩⟩
  · rw [liuLogGridCells, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hselected⟩
  · exact ⟨⟨by simpa [fi, liuAlphaGridPoint_eq_step hn] using hail,
        by simpa [fi, liuAlphaGridPoint_eq_step hn] using haiu⟩,
      ⟨by simpa [fj, liuBetaGridPoint_eq_step hn] using hbjl,
        by simpa [fj, liuBetaGridPoint_eq_step hn] using hbju⟩⟩

private lemma liuBetaGridPoint_succ_le_end {n i : ℕ} (hn : 0 < n) (hi : i < n) :
    liuBetaGridPoint n (i + 1) ≤ 9 / 20 := by
  have hin : ((i + 1 : ℕ) : ℝ) ≤ n := by
    exact_mod_cast (Nat.succ_le_iff.mpr hi)
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hratio : ((i + 1 : ℕ) : ℝ) / (n : ℝ) ≤ 1 :=
    (div_le_one hnreal).mpr hin
  unfold liuBetaGridPoint
  nlinarith

/-- Every selected cell stays in the fixed source box and in a strip of width
`7/(15n)` above the oblique source boundary. -/
theorem liuLogGridRegion_geometry {n : ℕ} (hn : 0 < n) {x : ℝ × ℝ}
    (hx : x ∈ liuLogGridRegion n) :
    x.1 ∈ Ioc (1 / 10 : ℝ) (1 / 3) ∧
      x.2 ∈ Ioc (1 / 3 : ℝ) (9 / 20) ∧
      x.1 + 2 * x.2 < 1 + 7 / (15 * (n : ℝ)) := by
  rw [liuLogGridRegion] at hx
  obtain ⟨q, hx⟩ := Set.mem_iUnion.1 hx
  obtain ⟨hq, hxcell⟩ := Set.mem_iUnion.1 hx
  have hqsel : liuBetaGridPoint n q.2 <
      (1 - liuAlphaGridPoint n q.1) / 2 := by
    rw [liuLogGridCells, Finset.mem_filter] at hq
    exact hq.2
  have hstep :
      liuAlphaGridStep n + 2 * liuBetaGridStep n =
        7 / (15 * (n : ℝ)) := by
    unfold liuAlphaGridStep liuBetaGridStep
    field_simp [Nat.cast_ne_zero.mpr hn.ne']
    ring
  have ha0 : (1 / 10 : ℝ) ≤ liuAlphaGridPoint n q.1 := by
    rw [liuAlphaGridPoint_eq_step hn]
    exact le_add_of_nonneg_right
      (mul_nonneg (Nat.cast_nonneg _) (liuAlphaGridStep_pos hn).le)
  have hb0 : (1 / 3 : ℝ) ≤ liuBetaGridPoint n q.2 := by
    rw [liuBetaGridPoint_eq_step hn]
    exact le_add_of_nonneg_right
      (mul_nonneg (Nat.cast_nonneg _) (liuBetaGridStep_pos hn).le)
  refine ⟨⟨ha0.trans_lt hxcell.1.1,
      hxcell.1.2.trans (liuAlphaGridPoint_succ_le_end hn q.1.isLt)⟩,
    ⟨⟨hb0.trans_lt hxcell.2.1,
      hxcell.2.2.trans (liuBetaGridPoint_succ_le_end hn q.2.isLt)⟩, ?_⟩⟩
  change
    x.1 ∈ Ioc (liuAlphaGridPoint n q.1) (liuAlphaGridPoint n (q.1 + 1)) ∧
      x.2 ∈ Ioc (liuBetaGridPoint n q.2) (liuBetaGridPoint n (q.2 + 1))
    at hxcell
  rw [liuAlphaGridPoint_succ hn, liuBetaGridPoint_succ hn] at hxcell
  have hcorner :
      liuAlphaGridPoint n q.1 + 2 * liuBetaGridPoint n q.2 < 1 := by
    linarith
  calc
    x.1 + 2 * x.2 ≤
        (liuAlphaGridPoint n q.1 + liuAlphaGridStep n) +
          2 * (liuBetaGridPoint n q.2 + liuBetaGridStep n) := by
      linarith [hxcell.1.2, hxcell.2.2]
    _ = (liuAlphaGridPoint n q.1 + 2 * liuBetaGridPoint n q.2) +
        (liuAlphaGridStep n + 2 * liuBetaGridStep n) := by ring
    _ < 1 + 7 / (15 * (n : ℝ)) := by rw [hstep]; linarith

/-- The fixed compact box containing every source point and every selected cell. -/
def liuLogAmbientBox : Set (ℝ × ℝ) :=
  Icc (1 / 10 : ℝ) (1 / 3) ×ˢ Icc (1 / 3 : ℝ) (9 / 20)


lemma isCompact_liuLogAmbientBox : IsCompact liuLogAmbientBox :=
  isCompact_Icc.prod isCompact_Icc

lemma liuLogSourceRegion_subset_ambientBox :
    liuLogSourceRegion ⊆ liuLogAmbientBox := by
  intro x hx
  exact ⟨⟨hx.1.1.le, hx.1.2⟩,
    ⟨hx.2.1.le, by linarith [hx.1.1, hx.2.2]⟩⟩

lemma liuLogGridRegion_subset_ambientBox {n : ℕ} (hn : 0 < n) :
    liuLogGridRegion n ⊆ liuLogAmbientBox := by
  intro x hx
  exact ⟨⟨(liuLogGridRegion_geometry hn hx).1.1.le,
    (liuLogGridRegion_geometry hn hx).1.2⟩,
    ⟨(liuLogGridRegion_geometry hn hx).2.1.1.le,
      (liuLogGridRegion_geometry hn hx).2.1.2⟩⟩


lemma measurableSet_liuLogSourceRegion : MeasurableSet liuLogSourceRegion := by
  exact (measurableSet_Ioc.preimage measurable_fst).inter
    ((measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd (by fun_prop)))

lemma liuLogDensity_nonneg {x : ℝ × ℝ} (hx : x ∈ liuLogAmbientBox) :
    0 ≤ liuLogDensity x := by
  change 0 ≤ 1 / (x.1 * x.2)
  exact one_div_nonneg.mpr (mul_nonneg (by linarith [hx.1.1]) (by linarith [hx.2.1]))

lemma liuLogKernel_nonneg {x : ℝ × ℝ} (hx : x ∈ liuLogAmbientBox) :
    0 ≤ liuLogKernel x := by
  change 0 ≤ 1 / (1 - x.1 - x.2)
  exact one_div_nonneg.mpr (by linarith [hx.1.2, hx.2.2])

lemma liuLogIntegrand_nonneg {x : ℝ × ℝ} (hx : x ∈ liuLogAmbientBox) :
    0 ≤ liuLogIntegrand x := by
  dsimp [liuLogIntegrand]
  exact mul_nonneg (liuLogKernel_nonneg hx) (liuLogDensity_nonneg hx)

lemma continuousOn_liuLogDensity : ContinuousOn liuLogDensity liuLogAmbientBox := by
  exact continuousOn_liuLogDensity_box (by norm_num) (by norm_num)

lemma continuousOn_liuLogKernel : ContinuousOn liuLogKernel liuLogAmbientBox := by
  exact continuousOn_liuLogKernel_box (by norm_num)

lemma continuousOn_liuLogIntegrand : ContinuousOn liuLogIntegrand liuLogAmbientBox := by
  exact continuousOn_liuLogKernel.mul continuousOn_liuLogDensity

lemma integrableOn_liuLogDensity {s : Set (ℝ × ℝ)}
    (hs : MeasurableSet s) (hsub : s ⊆ liuLogAmbientBox) :
    IntegrableOn liuLogDensity s := by
  exact continuousOn_liuLogDensity.integrableOn_of_subset_isCompact isCompact_liuLogAmbientBox hs hsub
    (ne_top_of_le_ne_top isCompact_liuLogAmbientBox.measure_ne_top (measure_mono hsub))

lemma integrableOn_liuLogIntegrand {s : Set (ℝ × ℝ)}
    (hs : MeasurableSet s) (hsub : s ⊆ liuLogAmbientBox) :
    IntegrableOn liuLogIntegrand s := by
  exact continuousOn_liuLogIntegrand.integrableOn_of_subset_isCompact isCompact_liuLogAmbientBox hs hsub
    (ne_top_of_le_ne_top isCompact_liuLogAmbientBox.measure_ne_top (measure_mono hsub))

lemma liuLogIntegrand_eq_sourceInner {α β : ℝ}
    (hα : α ∈ Icc (1 / 10 : ℝ) (1 / 3))
    (hβ : β ∈ Icc (1 / 3 : ℝ) ((1 - α) / 2)) :
    liuLogIntegrand (α, β) = (1 / α) * liuSourceInnerIntegrand α β := by
  have hpos := liuSource_inner_domain_pos hα hβ
  have hα0 : α ≠ 0 := by linarith [hα.1]
  unfold liuLogIntegrand liuLogKernel liuLogDensity liuSourceInnerIntegrand
  field_simp [hα0, hpos.1.ne', hpos.2.ne']

theorem liuSourceMainIntegral_eq_iteratedSetIntegral :
    liuSourceMainIntegral =
      ∫ α in Ioc (1 / 10 : ℝ) (1 / 3),
        ∫ β in Ioc (1 / 3 : ℝ) ((1 - α) / 2),
          liuLogIntegrand (α, β) := by
  unfold liuSourceMainIntegral liuSourceInnerIntegral
  rw [intervalIntegral.integral_of_le (by norm_num : (1 / 10 : ℝ) ≤ 1 / 3)]
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
  intro α hα
  have hα' : α ∈ Icc (1 / 10 : ℝ) (1 / 3) := ⟨hα.1.le, hα.2⟩
  have hle : (1 / 3 : ℝ) ≤ (1 - α) / 2 := by linarith [hα'.2]
  change (1 / α) * (∫ β in (1 / 3 : ℝ)..(1 - α) / 2,
    liuSourceInnerIntegrand α β) =
    ∫ β in Ioc (1 / 3 : ℝ) ((1 - α) / 2), liuLogIntegrand (α, β)
  rw [intervalIntegral.integral_of_le hle, ← MeasureTheory.integral_const_mul]
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
  intro β hβ
  exact (liuLogIntegrand_eq_sourceInner hα' ⟨hβ.1.le, hβ.2⟩).symm

theorem liuSourceMainIntegral_eq_setIntegral :
    liuSourceMainIntegral =
      ∫ x in liuLogSourceRegion, liuLogIntegrand x := by
  rw [liuSourceMainIntegral_eq_iteratedSetIntegral]
  exact (MathlibNt.Analysis.setIntegral_moving_Ioc_eq_iterated
    (Ioc (1 / 10 : ℝ) (1 / 3)) (fun _ => (1 / 3 : ℝ)) (fun α => (1 - α) / 2)
    liuLogIntegrand measurableSet_Ioc measurableSet_liuLogSourceRegion
    (integrableOn_liuLogIntegrand measurableSet_liuLogSourceRegion
      liuLogSourceRegion_subset_ambientBox)).symm

/-- The piecewise upper-corner density whose integral is the finite upper sum. -/
noncomputable def liuLogGridUpperIntegrand (n : ℕ) (x : ℝ × ℝ) : ℝ :=
  ∑ q ∈ liuLogGridCells n,
    (1 / (1 - liuAlphaGridPoint n (q.1 + 1) -
      liuBetaGridPoint n (q.2 + 1))) *
      (liuLogGridCell n q).indicator liuLogDensity x

lemma liuLogGridCell_subset_ambientBox {n : ℕ} (hn : 0 < n)
    {q : Fin n × Fin n} (hq : q ∈ liuLogGridCells n) :
    liuLogGridCell n q ⊆ liuLogAmbientBox := by
  intro x hx
  apply liuLogGridRegion_subset_ambientBox hn
  rw [liuLogGridRegion]
  exact Set.mem_iUnion.2 ⟨q, Set.mem_iUnion.2 ⟨hq, hx⟩⟩

theorem liuLogGridUpperSum_eq_integral (n : ℕ) (hn : 0 < n) :
    liuLogGridUpperSum n = ∫ x, liuLogGridUpperIntegrand n x := by
  unfold liuLogGridUpperSum liuLogGridUpperIntegrand
  rw [MathlibNt.Analysis.LogGridEstimates.integral_weighted_sum _ _ _ _
    (fun q _ => measurableSet_liuLogGridCell n q)
    (fun q hq => integrableOn_liuLogDensity (measurableSet_liuLogGridCell n q)
      (liuLogGridCell_subset_ambientBox hn hq))]
  apply Finset.sum_congr rfl
  intro q _
  rw [logarithmicRectangleMass_eq_setIntegral
    (liuAlphaGridPoint_pos hn) (liuAlphaGridPoint_lt_succ hn)
    (liuBetaGridPoint_pos hn) (liuBetaGridPoint_lt_succ hn)]
  rfl

lemma integrable_liuLogGridUpperIntegrand (n : ℕ) (hn : 0 < n) :
    Integrable (liuLogGridUpperIntegrand n) := by
  exact MathlibNt.Analysis.LogGridEstimates.integrable_weighted_sum _ _ _ _
    (fun q _ => measurableSet_liuLogGridCell n q)
    (fun q hq => integrableOn_liuLogDensity (measurableSet_liuLogGridCell n q)
      (liuLogGridCell_subset_ambientBox hn hq))

lemma liuLogGridUpperIntegrand_nonneg {n : ℕ} (hn : 0 < n)
    (x : ℝ × ℝ) : 0 ≤ liuLogGridUpperIntegrand n x := by
  classical
  unfold liuLogGridUpperIntegrand
  apply Finset.sum_nonneg
  intro q hq
  apply mul_nonneg
  · apply one_div_nonneg.mpr
    linarith [liuLogGridCell_upperCorner_lt_one hn hq]
  · by_cases hx : x ∈ liuLogGridCell n q
    · rw [Set.indicator_of_mem hx]
      exact liuLogDensity_nonneg (liuLogGridCell_subset_ambientBox hn hq hx)
    · rw [Set.indicator_of_notMem hx]

/-- At a point of a selected cell, pairwise disjointness reduces the upper
integrand to that cell's single summand. -/
lemma liuLogGridUpperIntegrand_eq_of_mem {n : ℕ} (hn : 0 < n)
    {q : Fin n × Fin n} (hq : q ∈ liuLogGridCells n)
    {x : ℝ × ℝ} (hx : x ∈ liuLogGridCell n q) :
    liuLogGridUpperIntegrand n x =
      (1 / (1 - liuAlphaGridPoint n (q.1 + 1) -
        liuBetaGridPoint n (q.2 + 1))) * liuLogDensity x := by
  unfold liuLogGridUpperIntegrand
  exact MathlibNt.Analysis.LogGridEstimates.weighted_sum_eq_of_mem _ _ _ _
    (liuLogGridCell_pairwiseDisjoint hn) hq hx

lemma liuLogIntegrand_le_liuLogGridUpperIntegrand {n : ℕ} (hn : 0 < n)
    {x : ℝ × ℝ} (hx : x ∈ liuLogSourceRegion) :
    liuLogIntegrand x ≤ liuLogGridUpperIntegrand n x := by
  classical
  have hxregion := liuLogSourceRegion_subset_gridRegion hn hx
  rw [liuLogGridRegion] at hxregion
  obtain ⟨q, hxregion⟩ := Set.mem_iUnion.1 hxregion
  obtain ⟨hq, hxq⟩ := Set.mem_iUnion.1 hxregion
  have hdenUpper : 0 < 1 - liuAlphaGridPoint n (q.1 + 1) -
      liuBetaGridPoint n (q.2 + 1) := by
    linarith [liuLogGridCell_upperCorner_lt_one hn hq]
  have hden : 1 - liuAlphaGridPoint n (q.1 + 1) -
      liuBetaGridPoint n (q.2 + 1) ≤ 1 - x.1 - x.2 := by
    linarith [hxq.1.2, hxq.2.2]
  have hkernel :
      liuLogKernel x ≤
        1 / (1 - liuAlphaGridPoint n (q.1 + 1) -
          liuBetaGridPoint n (q.2 + 1)) := by
    unfold liuLogKernel
    exact one_div_le_one_div_of_le hdenUpper hden
  have hdensity : 0 ≤ liuLogDensity x :=
    liuLogDensity_nonneg (liuLogGridCell_subset_ambientBox hn hq hxq)
  rw [liuLogGridUpperIntegrand_eq_of_mem hn hq hxq]
  exact mul_le_mul_of_nonneg_right hkernel hdensity

theorem liuSourceMainIntegral_le_liuLogGridUpperSum (n : ℕ) (hn : 0 < n) :
    liuSourceMainIntegral ≤ liuLogGridUpperSum n := by
  have hsource : Integrable (liuLogSourceRegion.indicator liuLogIntegrand) :=
    integrable_indicator_of_integrableOn measurableSet_liuLogSourceRegion
      (integrableOn_liuLogIntegrand measurableSet_liuLogSourceRegion
        liuLogSourceRegion_subset_ambientBox)
  have hupper := integrable_liuLogGridUpperIntegrand n hn
  rw [liuSourceMainIntegral_eq_setIntegral,
    liuLogGridUpperSum_eq_integral n hn,
    ← MeasureTheory.integral_indicator measurableSet_liuLogSourceRegion]
  apply MeasureTheory.integral_mono hsource hupper
  intro x
  by_cases hx : x ∈ liuLogSourceRegion
  · rw [Set.indicator_of_mem hx]
    exact liuLogIntegrand_le_liuLogGridUpperIntegrand hn hx
  · rw [Set.indicator_of_notMem hx]
    exact liuLogGridUpperIntegrand_nonneg hn x

private lemma volume_unitBox :
    volume (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) = 1 := by
  rw [MeasureTheory.Measure.volume_eq_prod ℝ ℝ]
  rw [MeasureTheory.Measure.prod_prod]
  norm_num [Real.volume_Icc]

lemma liuLogGrid_upperKernel_sub_le {n : ℕ} (hn : 0 < n)
    {q : Fin n × Fin n} (_hq : q ∈ liuLogGridCells n)
    {x : ℝ × ℝ} (hx : x ∈ liuLogGridCell n q) :
    0 ≤ 1 / (1 - liuAlphaGridPoint n (q.1 + 1) -
      liuBetaGridPoint n (q.2 + 1)) - liuLogKernel x ∧
    1 / (1 - liuAlphaGridPoint n (q.1 + 1) -
      liuBetaGridPoint n (q.2 + 1)) - liuLogKernel x ≤ 25 / (n : ℝ) := by
  simp only [liuLogGridCell, liuAlphaGridPoint_succ hn, liuBetaGridPoint_succ hn] at hx
  simp only [liuAlphaGridPoint_succ hn, liuBetaGridPoint_succ hn, liuLogKernel]
  apply MathlibNt.Analysis.LogGridEstimates.cell_reciprocal_variation hx
    (l := 1 / 5) (by norm_num) ?_ (by positivity) ?_
  · have hα := liuAlphaGridPoint_succ_le_end hn q.1.isLt
    have hβ := liuBetaGridPoint_succ_le_end hn q.2.isLt
    simp only [liuAlphaGridPoint_succ hn, liuBetaGridPoint_succ hn] at hα hβ
    linarith
  · unfold liuAlphaGridStep liuBetaGridStep
    have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
    field_simp
    norm_num

/-- The logarithmic density is uniformly bounded on the ambient box. -/
lemma liuLogDensity_le_thirty {x : ℝ × ℝ} (hx : x ∈ liuLogAmbientBox) :
    liuLogDensity x ≤ 30 := by
  convert liuLogDensity_le_of_lower_bounds
    (by norm_num : (0 : ℝ) < 1/10) (by norm_num : (0 : ℝ) < 1/3)
    hx.1.1 hx.2.1 using 1; norm_num

/-- Every selected upper corner has remaining kernel at most five. -/
lemma liuLogGrid_upperKernel_le_five {n : ℕ} (hn : 0 < n)
    {q : Fin n × Fin n} (_hq : q ∈ liuLogGridCells n) :
    1 / (1 - liuAlphaGridPoint n (q.1 + 1) -
      liuBetaGridPoint n (q.2 + 1)) ≤ 5 := by
  have hα := liuAlphaGridPoint_succ_le_end hn q.1.isLt
  have hβ := liuBetaGridPoint_succ_le_end hn q.2.isLt
  have hden : (1 / 5 : ℝ) ≤
      1 - liuAlphaGridPoint n (q.1 + 1) -
        liuBetaGridPoint n (q.2 + 1) := by
    linarith
  rw [div_le_iff₀ (by linarith [hden])]
  nlinarith

/-- The upper integrand vanishes off the selected grid region. -/
lemma liuLogGridUpperIntegrand_eq_zero_of_notMem {n : ℕ}
    {x : ℝ × ℝ} (hx : x ∉ liuLogGridRegion n) :
    liuLogGridUpperIntegrand n x = 0 := by
  unfold liuLogGridUpperIntegrand
  exact MathlibNt.Analysis.LogGridEstimates.weighted_sum_zero _ _ _ _ hx

/-- The selected upper integrand is uniformly bounded by `150` on its grid. -/
lemma liuLogGridUpperIntegrand_le_oneHundredFifty {n : ℕ} (hn : 0 < n)
    {x : ℝ × ℝ} (hx : x ∈ liuLogGridRegion n) :
    liuLogGridUpperIntegrand n x ≤ 150 := by
  rw [liuLogGridRegion] at hx
  obtain ⟨q, hq, hxq⟩ := Set.mem_iUnion₂.1 hx
  rw [liuLogGridUpperIntegrand_eq_of_mem hn hq hxq]
  have hd := liuLogDensity_le_thirty (liuLogGridCell_subset_ambientBox hn hq hxq)
  have hk := liuLogGrid_upperKernel_le_five hn hq
  have hd0 := liuLogDensity_nonneg (liuLogGridCell_subset_ambientBox hn hq hxq)
  nlinarith [mul_le_mul_of_nonneg_right hk hd0]

/-- The thin oblique strip swept out above Liu's source boundary. -/
def liuLogExcessStrip (n : ℕ) : Set (ℝ × ℝ) :=
  {x | x.1 ∈ Icc (1 / 10 : ℝ) (1 / 3) ∧
    (1 - x.1) / 2 < x.2 ∧
    x.2 < (1 - x.1) / 2 + 7 / (30 * (n : ℝ))}

lemma measurableSet_liuLogExcessStrip (n : ℕ) :
    MeasurableSet (liuLogExcessStrip n) := by
  change MeasurableSet
    (Prod.fst ⁻¹' Icc (1 / 10 : ℝ) (1 / 3) ∩
      ({x : ℝ × ℝ | (1 - x.1) / 2 < x.2} ∩
        {x : ℝ × ℝ | x.2 < (1 - x.1) / 2 + 7 / (30 * (n : ℝ))}))
  exact (measurable_fst measurableSet_Icc).inter
    ((measurableSet_lt (by fun_prop) measurable_snd).inter
      (measurableSet_lt measurable_snd (by fun_prop)))

/-- A selected grid point outside the source belongs to the excess strip. -/
lemma liuLogGridRegion_diff_source_subset_excessStrip {n : ℕ} (hn : 0 < n) :
    liuLogGridRegion n \ liuLogSourceRegion ⊆ liuLogExcessStrip n := by
  intro x hx
  have hgeom := liuLogGridRegion_geometry hn hx.1
  have habove : (1 - x.1) / 2 < x.2 := by
    by_contra h
    apply hx.2
    exact ⟨hgeom.1, hgeom.2.1.1, le_of_not_gt h⟩
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hwidth : 2 * (7 / (30 * (n : ℝ))) = 7 / (15 * (n : ℝ)) := by
    field_simp
    ring
  exact ⟨⟨hgeom.1.1.le, hgeom.1.2⟩, habove, by
    linarith [hgeom.2.2, hwidth]⟩

/-- The excess strip has width `7/(30n)` in every vertical section. -/
lemma volume_liuLogExcessStrip {n : ℕ} (hn : 0 < n) :
    volume (liuLogExcessStrip n) =
      ENNReal.ofReal (49 / (900 * (n : ℝ))) := by
  simp only [liuLogExcessStrip]
  rw [MathlibNt.Analysis.LogGridEstimates.volume_strip (1 / 10) (1 / 3)
    (7 / (30 * (n : ℝ))) (fun u => (1 - u) / 2)
    (measurableSet_liuLogExcessStrip n) (by
    positivity)]
  congr 1
  ring

/-- On the source, replacing the kernel by the selected upper corner costs at
most `750/n`. -/
lemma liuLogGridUpperIntegrand_le_integrand_add {n : ℕ} (hn : 0 < n)
    {x : ℝ × ℝ} (hx : x ∈ liuLogSourceRegion) :
    liuLogGridUpperIntegrand n x ≤ liuLogIntegrand x + 750 / (n : ℝ) := by
  obtain ⟨q, hq, hxq⟩ := Set.mem_iUnion₂.mp (liuLogSourceRegion_subset_gridRegion hn hx)
  rw [liuLogGridUpperIntegrand_eq_of_mem hn hq hxq]
  have hb := liuLogGridCell_subset_ambientBox hn hq hxq
  have h := MathlibNt.Analysis.LogGridEstimates.weighted_error
    (liuLogDensity_nonneg hb) (liuLogDensity_le_thirty hb)
    (by positivity : 0 ≤ 25 / (n : ℝ)) (liuLogGrid_upperKernel_sub_le hn hq hxq).2
  convert h using 1
  dsimp [liuLogIntegrand]
  ring


/-- The grid upper sum exceeds Liu's source integral by at most `759/n`. -/
theorem liuLogGridUpperSum_sub_source_le (n : ℕ) (hn : 0 < n) :
    liuLogGridUpperSum n - liuSourceMainIntegral ≤ 759 / (n : ℝ) := by
  classical
  have h := MathlibNt.Analysis.IntegralExcessCover.integral_sub_setIntegral_le_of_excess_cover
    volume (liuLogGridRegion n) liuLogSourceRegion (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)
    (fun _ : Fin 1 => liuLogExcessStrip n)
    (liuLogGridUpperIntegrand n) liuLogIntegrand (750 / (n : ℝ)) 150
    (integrable_liuLogGridUpperIntegrand n hn)
    (integrableOn_liuLogIntegrand measurableSet_liuLogSourceRegion
      liuLogSourceRegion_subset_ambientBox)
    measurableSet_liuLogSourceRegion (measurableSet_Icc.prod measurableSet_Icc)
    (by rw [volume_unitBox]; norm_num)
    (fun _ => measurableSet_liuLogExcessStrip n)
    (fun _ => by rw [volume_liuLogExcessStrip hn]; exact ENNReal.ofReal_ne_top)
    (by positivity) (by norm_num)
    (fun _ hx => liuLogIntegrand_nonneg (liuLogSourceRegion_subset_ambientBox hx))
    (fun _ hx => liuLogGridUpperIntegrand_eq_zero_of_notMem hx)
    (by
      intro x hx
      have hb := liuLogSourceRegion_subset_ambientBox hx.2
      exact ⟨⟨by linarith [hb.1.1], by linarith [hb.1.2]⟩,
        ⟨by linarith [hb.2.1], by linarith [hb.2.2]⟩⟩)
    (fun _ hx => liuLogGridUpperIntegrand_le_integrand_add hn hx.2)
    (fun _ hx => ⟨0, liuLogGridRegion_diff_source_subset_excessStrip hn hx⟩)
    (fun _ hx => liuLogGridUpperIntegrand_le_oneHundredFifty hn hx.1)
  rw [← liuLogGridUpperSum_eq_integral n hn,
    ← liuSourceMainIntegral_eq_setIntegral] at h
  simp only [Fin.sum_univ_one, Measure.real_def, volume_unitBox,
    volume_liuLogExcessStrip hn, ENNReal.toReal_one, one_mul] at h
  rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ 49 / (900 * (n : ℝ)))] at h
  refine h.trans ?_
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  field_simp
  norm_num

/-- The canonical logarithmic-grid upper sums converge to Liu's source
integral as the mesh tends to zero. -/
theorem tendsto_liuLogGridUpperSum_sourceMainIntegral :
    Tendsto (fun n : ℕ => liuLogGridUpperSum (n + 1)) atTop
      (nhds liuSourceMainIntegral) := by
  exact MathlibNt.Analysis.LogGridEstimates.tendsto_of_sub_le_div_nat
    (fun n hn => liuSourceMainIntegral_le_liuLogGridUpperSum n hn) (fun n hn => liuLogGridUpperSum_sub_source_le n hn)

end

end MathlibNt.SieveTheory.LiuWeight
