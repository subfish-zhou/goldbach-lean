import MathlibNt.SieveTheory.Liu.PrimePairs.LiuPrimePairLogGrid
import MathlibNt.SieveTheory.Liu.Weights.LiuWeightMainIntegral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Function.LocallyIntegrable

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

/-- The logarithmic density in the two exponent coordinates. -/
def liuLogDensity (x : ℝ × ℝ) : ℝ := 1 / (x.1 * x.2)

/-- Liu's remaining kernel in logarithmic coordinates. -/
def liuLogKernel (x : ℝ × ℝ) : ℝ := 1 / (1 - x.1 - x.2)

/-- The full density occurring in Liu's source integral. -/
def liuLogIntegrand (x : ℝ × ℝ) : ℝ :=
  liuLogKernel x * liuLogDensity x

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

/-- A logarithmic rectangle mass is exactly the iterated integral of the
logarithmic density. -/
theorem logarithmicRectangleMass_eq_iteratedIntegral
    {a₀ a₁ b₀ b₁ : ℝ} (ha₀ : 0 < a₀) (ha : a₀ < a₁)
    (hb₀ : 0 < b₀) (hb : b₀ < b₁) :
    logarithmicRectangleMass a₀ a₁ b₀ b₁ =
      ∫ α in a₀..a₁, ∫ β in b₀..b₁, 1 / (α * β) := by
  have ha₁ : 0 < a₁ := ha₀.trans ha
  have hb₁ : 0 < b₁ := hb₀.trans hb
  have hia : (∫ α in a₀..a₁, 1 / α) = Real.log (a₁ / a₀) := by
    simpa only [one_div] using integral_inv_of_pos ha₀ ha₁
  have hib : (∫ β in b₀..b₁, 1 / β) = Real.log (b₁ / b₀) := by
    simpa only [one_div] using integral_inv_of_pos hb₀ hb₁
  calc
    logarithmicRectangleMass a₀ a₁ b₀ b₁ =
        Real.log (a₁ / a₀) * Real.log (b₁ / b₀) := rfl
    _ = (∫ α in a₀..a₁, 1 / α) * (∫ β in b₀..b₁, 1 / β) := by
      rw [hia, hib]
    _ = ∫ α in a₀..a₁, (1 / α) * (∫ β in b₀..b₁, 1 / β) := by
      rw [intervalIntegral.integral_mul_const]
    _ = ∫ α in a₀..a₁, ∫ β in b₀..b₁, 1 / (α * β) := by
      apply intervalIntegral.integral_congr
      intro α hα
      change (1 / α) * (∫ β in b₀..b₁, 1 / β) =
        ∫ β in b₀..b₁, 1 / (α * β)
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro β hβ
      simp [one_div]
      ring

/-- The same identity as a product-set integral. -/
theorem logarithmicRectangleMass_eq_setIntegral
    {a₀ a₁ b₀ b₁ : ℝ} (ha₀ : 0 < a₀) (ha : a₀ < a₁)
    (hb₀ : 0 < b₀) (hb : b₀ < b₁) :
    logarithmicRectangleMass a₀ a₁ b₀ b₁ =
      ∫ x in Ioc a₀ a₁ ×ˢ Ioc b₀ b₁, liuLogDensity x := by
  have ha₁ : 0 < a₁ := ha₀.trans ha
  have hb₁ : 0 < b₁ := hb₀.trans hb
  change logarithmicRectangleMass a₀ a₁ b₀ b₁ =
    ∫ x in Ioc a₀ a₁ ×ˢ Ioc b₀ b₁, 1 / (x.1 * x.2)
  have hfactor :
      (∫ x in Ioc a₀ a₁ ×ˢ Ioc b₀ b₁, 1 / (x.1 * x.2)) =
        ∫ x in Ioc a₀ a₁ ×ˢ Ioc b₀ b₁, (1 / x.1) * (1 / x.2) := by
    apply MeasureTheory.setIntegral_congr_fun
      (measurableSet_Ioc.prod measurableSet_Ioc)
    intro x hx
    simpa only [one_div] using (mul_inv x.1 x.2)
  rw [hfactor]
  rw [MeasureTheory.Measure.volume_eq_prod ℝ ℝ,
    MeasureTheory.setIntegral_prod_mul
    (fun α : ℝ => 1 / α) (fun β : ℝ => 1 / β)]
  rw [← intervalIntegral.integral_of_le ha.le,
    ← intervalIntegral.integral_of_le hb.le]
  have hia : (∫ α in a₀..a₁, 1 / α) = Real.log (a₁ / a₀) := by
    simpa only [one_div] using integral_inv_of_pos ha₀ ha₁
  have hib : (∫ β in b₀..b₁, 1 / β) = Real.log (b₁ / b₀) := by
    simpa only [one_div] using integral_inv_of_pos hb₀ hb₁
  rw [hia, hib]
  rfl

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
  intro q hq r hr hqr
  change Disjoint (liuLogGridCell n q) (liuLogGridCell n r)
  rw [Set.disjoint_left]
  intro x hxq hxr
  change
    x.1 ∈ Ioc (liuAlphaGridPoint n q.1) (liuAlphaGridPoint n (q.1 + 1)) ∧
      x.2 ∈ Ioc (liuBetaGridPoint n q.2) (liuBetaGridPoint n (q.2 + 1))
    at hxq
  change
    x.1 ∈ Ioc (liuAlphaGridPoint n r.1) (liuAlphaGridPoint n (r.1 + 1)) ∧
      x.2 ∈ Ioc (liuBetaGridPoint n r.2) (liuBetaGridPoint n (r.2 + 1))
    at hxr
  rcases hxq with ⟨hqa, hqb⟩
  rcases hxr with ⟨hra, hrb⟩
  by_cases hi : q.1 = r.1
  · have hj : q.2 ≠ r.2 := by
      intro h
      apply hqr
      exact Prod.ext hi h
    rcases lt_or_gt_of_ne hj with hjlt | hjgt
    · have hle := liuBetaGridPoint_mono hn
        (show (q.2 : ℕ) + 1 ≤ (r.2 : ℕ) by omega)
      exact not_lt_of_ge hle (hrb.1.trans_le hqb.2)
    · have hle := liuBetaGridPoint_mono hn
        (show (r.2 : ℕ) + 1 ≤ (q.2 : ℕ) by omega)
      exact not_lt_of_ge hle (hqb.1.trans_le hrb.2)
  · rcases lt_or_gt_of_ne hi with hilt | higt
    · have hle := liuAlphaGridPoint_mono hn
        (show (q.1 : ℕ) + 1 ≤ (r.1 : ℕ) by omega)
      exact not_lt_of_ge hle (hra.1.trans_le hqa.2)
    · have hle := liuAlphaGridPoint_mono hn
        (show (r.1 : ℕ) + 1 ≤ (q.1 : ℕ) by omega)
      exact not_lt_of_ge hle (hqa.1.trans_le hra.2)

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

lemma measurableSet_liuLogAmbientBox : MeasurableSet liuLogAmbientBox :=
  measurableSet_Icc.prod measurableSet_Icc

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

lemma measurableSet_liuLogGridRegion (n : ℕ) :
    MeasurableSet (liuLogGridRegion n) := by
  classical
  rw [liuLogGridRegion]
  exact Finset.measurableSet_biUnion _ fun q _ => measurableSet_liuLogGridCell n q

lemma measurableSet_liuLogSourceRegion : MeasurableSet liuLogSourceRegion := by
  change MeasurableSet
    {x : ℝ × ℝ | x.1 ∈ Ioc (1 / 10 : ℝ) (1 / 3) ∧
      x.2 ∈ Ioc (1 / 3 : ℝ) ((1 - x.1) / 2)}
  have hset :
      {x : ℝ × ℝ | x.1 ∈ Ioc (1 / 10 : ℝ) (1 / 3) ∧
        x.2 ∈ Ioc (1 / 3 : ℝ) ((1 - x.1) / 2)} =
      Prod.fst ⁻¹' Ioc (1 / 10 : ℝ) (1 / 3) ∩
        (Prod.snd ⁻¹' Ioi (1 / 3) ∩
          {x : ℝ × ℝ | x.2 ≤ (1 - x.1) / 2}) := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage,
      Set.mem_Ioc, Set.mem_Ioi]
  rw [hset]
  exact (measurable_fst measurableSet_Ioc).inter
    ((measurable_snd measurableSet_Ioi).inter
      (measurableSet_le measurable_snd (by fun_prop)))

lemma liuLogDensity_nonneg {x : ℝ × ℝ} (hx : x ∈ liuLogAmbientBox) :
    0 ≤ liuLogDensity x := by
  dsimp [liuLogDensity]
  apply one_div_nonneg.mpr
  exact mul_nonneg (by linarith [hx.1.1]) (by linarith [hx.2.1])

lemma liuLogKernel_nonneg {x : ℝ × ℝ} (hx : x ∈ liuLogAmbientBox) :
    0 ≤ liuLogKernel x := by
  dsimp [liuLogKernel]
  have hden : 0 < 1 - x.1 - x.2 := by
    rcases hx with ⟨hx₁, hx₂⟩
    linarith [hx₁.2, hx₂.2]
  positivity

lemma liuLogIntegrand_nonneg {x : ℝ × ℝ} (hx : x ∈ liuLogAmbientBox) :
    0 ≤ liuLogIntegrand x := by
  dsimp [liuLogIntegrand]
  exact mul_nonneg (liuLogKernel_nonneg hx) (liuLogDensity_nonneg hx)

lemma continuousOn_liuLogDensity : ContinuousOn liuLogDensity liuLogAmbientBox := by
  unfold liuLogDensity
  apply ContinuousOn.div continuousOn_const
    (continuous_fst.continuousOn.mul continuous_snd.continuousOn)
  intro x hx
  exact mul_ne_zero (by linarith [hx.1.1]) (by linarith [hx.2.1])

lemma continuousOn_liuLogKernel : ContinuousOn liuLogKernel liuLogAmbientBox := by
  unfold liuLogKernel
  apply ContinuousOn.div continuousOn_const
    ((continuousOn_const.sub continuous_fst.continuousOn).sub continuous_snd.continuousOn)
  intro x hx
  change 1 - x.1 - x.2 ≠ 0
  linarith [hx.1.2, hx.2.2]

lemma continuousOn_liuLogIntegrand : ContinuousOn liuLogIntegrand liuLogAmbientBox := by
  exact continuousOn_liuLogKernel.mul continuousOn_liuLogDensity

lemma integrableOn_liuLogDensity {s : Set (ℝ × ℝ)}
    (hs : MeasurableSet s) (hsub : s ⊆ liuLogAmbientBox) :
    IntegrableOn liuLogDensity s := by
  apply ContinuousOn.integrableOn_of_subset_isCompact continuousOn_liuLogDensity
    isCompact_liuLogAmbientBox hs hsub
  exact (lt_of_le_of_lt (measure_mono hsub)
    isCompact_liuLogAmbientBox.measure_lt_top).ne

lemma integrableOn_liuLogIntegrand {s : Set (ℝ × ℝ)}
    (hs : MeasurableSet s) (hsub : s ⊆ liuLogAmbientBox) :
    IntegrableOn liuLogIntegrand s := by
  apply ContinuousOn.integrableOn_of_subset_isCompact continuousOn_liuLogIntegrand
    isCompact_liuLogAmbientBox hs hsub
  exact (lt_of_le_of_lt (measure_mono hsub)
    isCompact_liuLogAmbientBox.measure_lt_top).ne

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
  let F : ℝ × ℝ → ℝ := liuLogSourceRegion.indicator liuLogIntegrand
  have hF : Integrable F :=
    (integrableOn_liuLogIntegrand measurableSet_liuLogSourceRegion
      liuLogSourceRegion_subset_ambientBox).integrable_indicator
        measurableSet_liuLogSourceRegion
  have hinner (α : ℝ) :
      (∫ β, F (α, β)) =
        (Ioc (1 / 10 : ℝ) (1 / 3)).indicator
          (fun α => ∫ β in Ioc (1 / 3 : ℝ) ((1 - α) / 2),
            liuLogIntegrand (α, β)) α := by
    by_cases hα : α ∈ Ioc (1 / 10 : ℝ) (1 / 3)
    · rw [Set.indicator_of_mem hα, ← MeasureTheory.integral_indicator measurableSet_Ioc]
      apply integral_congr_ae
      filter_upwards with β
      have hmem : (α, β) ∈ liuLogSourceRegion ↔
          β ∈ Ioc (1 / 3 : ℝ) ((1 - α) / 2) := by
        change (α ∈ Ioc (1 / 10 : ℝ) (1 / 3) ∧
          β ∈ Ioc (1 / 3 : ℝ) ((1 - α) / 2)) ↔ _
        exact and_iff_right hα
      change liuLogSourceRegion.indicator liuLogIntegrand (α, β) =
        (Ioc (1 / 3 : ℝ) ((1 - α) / 2)).indicator
          (fun β => liuLogIntegrand (α, β)) β
      by_cases hβ : β ∈ Ioc (1 / 3 : ℝ) ((1 - α) / 2)
      · rw [Set.indicator_of_mem (hmem.mpr hβ), Set.indicator_of_mem hβ]
      · rw [Set.indicator_of_notMem (fun h => hβ (hmem.mp h)),
          Set.indicator_of_notMem hβ]
    · rw [Set.indicator_of_notMem hα]
      apply integral_eq_zero_of_ae
      filter_upwards with β
      have hnot : (α, β) ∉ liuLogSourceRegion := by
        intro h
        exact hα h.1
      change liuLogSourceRegion.indicator liuLogIntegrand (α, β) = 0
      rw [Set.indicator_of_notMem hnot]
  have hFubini :
      (∫ z, F z) = ∫ α, ∫ β, F (α, β) := by
    rw [MeasureTheory.Measure.volume_eq_prod ℝ ℝ] at hF ⊢
    exact MeasureTheory.integral_prod F hF
  calc
    (∫ α in Ioc (1 / 10 : ℝ) (1 / 3),
        ∫ β in Ioc (1 / 3 : ℝ) ((1 - α) / 2),
          liuLogIntegrand (α, β)) =
        ∫ α, (Ioc (1 / 10 : ℝ) (1 / 3)).indicator
          (fun α => ∫ β in Ioc (1 / 3 : ℝ) ((1 - α) / 2),
            liuLogIntegrand (α, β)) α := by
          rw [MeasureTheory.integral_indicator measurableSet_Ioc]
    _ = ∫ α, ∫ β, F (α, β) := by
      apply integral_congr_ae
      filter_upwards with α
      exact (hinner α).symm
    _ = ∫ z, F z := hFubini.symm
    _ = ∫ x in liuLogSourceRegion, liuLogIntegrand x := by
      rw [MeasureTheory.integral_indicator measurableSet_liuLogSourceRegion]

/-- The piecewise upper-corner density whose integral is the finite upper sum. -/
noncomputable def liuLogGridUpperIntegrand (n : ℕ) (x : ℝ × ℝ) : ℝ :=
  ∑ q ∈ liuLogGridCells n,
    (1 / (1 - liuAlphaGridPoint n (q.1 + 1) -
      liuBetaGridPoint n (q.2 + 1))) *
      (liuLogGridCell n q).indicator liuLogDensity x

lemma integrable_indicator_of_integrableOn {f : ℝ × ℝ → ℝ} {s : Set (ℝ × ℝ)}
    (hs : MeasurableSet s) (hf : IntegrableOn f s) :
    Integrable (s.indicator f) := by
  exact hf.integrable_indicator hs

lemma liuLogGridCell_subset_ambientBox {n : ℕ} (hn : 0 < n)
    {q : Fin n × Fin n} (hq : q ∈ liuLogGridCells n) :
    liuLogGridCell n q ⊆ liuLogAmbientBox := by
  intro x hx
  apply liuLogGridRegion_subset_ambientBox hn
  rw [liuLogGridRegion]
  exact Set.mem_iUnion.2 ⟨q, Set.mem_iUnion.2 ⟨hq, hx⟩⟩

theorem liuLogGridUpperSum_eq_integral (n : ℕ) (hn : 0 < n) :
    liuLogGridUpperSum n = ∫ x, liuLogGridUpperIntegrand n x := by
  classical
  unfold liuLogGridUpperSum liuLogGridUpperIntegrand
  rw [MeasureTheory.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro q hq
    rw [MeasureTheory.integral_const_mul,
      MeasureTheory.integral_indicator (measurableSet_liuLogGridCell n q)]
    rw [logarithmicRectangleMass_eq_setIntegral
      (liuAlphaGridPoint_pos hn) (liuAlphaGridPoint_lt_succ hn)
      (liuBetaGridPoint_pos hn) (liuBetaGridPoint_lt_succ hn)]
    rfl
  · intro q hq
    exact (integrable_indicator_of_integrableOn
      (measurableSet_liuLogGridCell n q)
      (integrableOn_liuLogDensity (measurableSet_liuLogGridCell n q)
        (liuLogGridCell_subset_ambientBox hn hq))).const_mul _

lemma integrable_liuLogGridUpperIntegrand (n : ℕ) (hn : 0 < n) :
    Integrable (liuLogGridUpperIntegrand n) := by
  classical
  unfold liuLogGridUpperIntegrand
  exact integrable_finsetSum _ fun q hq =>
    (integrable_indicator_of_integrableOn
      (measurableSet_liuLogGridCell n q)
      (integrableOn_liuLogDensity (measurableSet_liuLogGridCell n q)
        (liuLogGridCell_subset_ambientBox hn hq))).const_mul _

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
  classical
  unfold liuLogGridUpperIntegrand
  rw [Finset.sum_eq_single q]
  · rw [Set.indicator_of_mem hx]
  · intro r hr hrq
    have hnot : x ∉ liuLogGridCell n r := by
      intro hxr
      have hd : Disjoint (liuLogGridCell n q) (liuLogGridCell n r) :=
        liuLogGridCell_pairwiseDisjoint hn
          (Set.mem_univ q) (Set.mem_univ r) hrq.symm
      exact Set.disjoint_left.1 hd hx hxr
    rw [Set.indicator_of_notMem hnot, mul_zero]
  · exact fun h => (h hq).elim

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
  change
    x.1 ∈ Ioc (liuAlphaGridPoint n q.1) (liuAlphaGridPoint n (q.1 + 1)) ∧
      x.2 ∈ Ioc (liuBetaGridPoint n q.2) (liuBetaGridPoint n (q.2 + 1))
    at hx
  rw [liuAlphaGridPoint_succ hn, liuBetaGridPoint_succ hn] at hx
  have hα : liuAlphaGridPoint n q.1 + liuAlphaGridStep n ≤ 1 / 3 :=
    (liuAlphaGridPoint_succ (n := n) (i := q.1) hn).symm ▸
      liuAlphaGridPoint_succ_le_end hn q.1.isLt
  have hβ : liuBetaGridPoint n q.2 + liuBetaGridStep n ≤ 9 / 20 :=
    (liuBetaGridPoint_succ (n := n) (i := q.2) hn).symm ▸
      liuBetaGridPoint_succ_le_end hn q.2.isLt
  have hstep : liuAlphaGridStep n + liuBetaGridStep n ≤ 1 / (n : ℝ) := by
    unfold liuAlphaGridStep liuBetaGridStep
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    field_simp
    nlinarith
  have hden : 1 / 5 ≤ 1 - (liuAlphaGridPoint n q.1 + liuAlphaGridStep n) -
      (liuBetaGridPoint n q.2 + liuBetaGridStep n) := by
    linarith
  have hdenx : 1 / 5 ≤ 1 - x.1 - x.2 := by
    linarith [hx.1.2, hx.2.2, hden]
  have hdelta : 0 ≤
      (liuAlphaGridPoint n q.1 + liuAlphaGridStep n) +
        (liuBetaGridPoint n q.2 + liuBetaGridStep n) - x.1 - x.2 ∧
      (liuAlphaGridPoint n q.1 + liuAlphaGridStep n) +
        (liuBetaGridPoint n q.2 + liuBetaGridStep n) - x.1 - x.2 ≤
        1 / (n : ℝ) := by
    constructor
    · linarith [hx.1.2, hx.2.2]
    · linarith [hx.1.1, hx.2.1, hstep]
  have hprod : 1 / 25 ≤
      (1 - (liuAlphaGridPoint n q.1 + liuAlphaGridStep n) -
        (liuBetaGridPoint n q.2 + liuBetaGridStep n)) * (1 - x.1 - x.2) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hden) (sub_nonneg.mpr hdenx)]
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
  have hformula :
      1 / (1 - (liuAlphaGridPoint n q.1 + liuAlphaGridStep n) -
        (liuBetaGridPoint n q.2 + liuBetaGridStep n)) - liuLogKernel x =
      ((liuAlphaGridPoint n q.1 + liuAlphaGridStep n) +
        (liuBetaGridPoint n q.2 + liuBetaGridStep n) - x.1 - x.2) /
      ((1 - (liuAlphaGridPoint n q.1 + liuAlphaGridStep n) -
        (liuBetaGridPoint n q.2 + liuBetaGridStep n)) * (1 - x.1 - x.2)) := by
    unfold liuLogKernel
    field_simp
    ring
  rw [liuAlphaGridPoint_succ hn, liuBetaGridPoint_succ hn, hformula]
  constructor
  · exact div_nonneg hdelta.1 (by positivity)
  · calc
      _ ≤ (1 / (n : ℝ)) /
          ((1 - (liuAlphaGridPoint n q.1 + liuAlphaGridStep n) -
            (liuBetaGridPoint n q.2 + liuBetaGridStep n)) * (1 - x.1 - x.2)) :=
        div_le_div_of_nonneg_right hdelta.2 (by positivity)
      _ ≤ (1 / (n : ℝ)) / (1 / 25 : ℝ) :=
        (div_le_div_iff₀ (by linarith [hprod]) (by norm_num)).mpr
          (mul_le_mul_of_nonneg_left hprod (by positivity))
      _ = 25 / (n : ℝ) := by field_simp [hnreal.ne']

/-- The logarithmic density is uniformly bounded on the ambient box. -/
lemma liuLogDensity_le_thirty {x : ℝ × ℝ} (hx : x ∈ liuLogAmbientBox) :
    liuLogDensity x ≤ 30 := by
  have hx₁ : 0 < x.1 := by linarith [hx.1.1]
  have hx₂ : 0 < x.2 := by linarith [hx.2.1]
  have hprod : (1 / 30 : ℝ) ≤ x.1 * x.2 := by
    calc
      (1 / 30 : ℝ) = (1 / 10) * (1 / 3) := by norm_num
      _ ≤ x.1 * x.2 :=
        mul_le_mul hx.1.1 hx.2.1 (by norm_num) (by linarith [hx.1.1])
  unfold liuLogDensity
  rw [div_le_iff₀ (mul_pos hx₁ hx₂)]
  nlinarith

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
  classical
  unfold liuLogGridUpperIntegrand
  apply Finset.sum_eq_zero
  intro q hq
  have hnot : x ∉ liuLogGridCell n q := by
    intro hxq
    apply hx
    rw [liuLogGridRegion]
    exact Set.mem_iUnion.2 ⟨q, Set.mem_iUnion.2 ⟨hq, hxq⟩⟩
  rw [Set.indicator_of_notMem hnot, mul_zero]

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
  rw [MeasureTheory.Measure.volume_eq_prod ℝ ℝ,
    MeasureTheory.Measure.prod_apply (measurableSet_liuLogExcessStrip n)]
  have hsection (α : ℝ) :
      Prod.mk α ⁻¹' liuLogExcessStrip n =
        if α ∈ Icc (1 / 10 : ℝ) (1 / 3) then
          Ioo ((1 - α) / 2)
            ((1 - α) / 2 + 7 / (30 * (n : ℝ)))
        else ∅ := by
    ext β
    simp [liuLogExcessStrip, and_assoc]
  have hfun :
      (fun α : ℝ => volume (Prod.mk α ⁻¹' liuLogExcessStrip n)) =
        (Icc (1 / 10 : ℝ) (1 / 3)).indicator
          (fun α => volume
            (Ioo ((1 - α) / 2)
              ((1 - α) / 2 + 7 / (30 * (n : ℝ))))) := by
    funext α
    rw [hsection]
    by_cases hα : α ∈ Icc (1 / 10 : ℝ) (1 / 3)
    · rw [if_pos hα, Set.indicator_of_mem hα, Real.volume_Ioo]
    · rw [if_neg hα, Set.indicator_of_notMem hα, measure_empty]
  rw [hfun, MeasureTheory.lintegral_indicator measurableSet_Icc]
  simp_rw [Real.volume_Ioo]
  have hdiff (α : ℝ) :
      (1 - α) / 2 + 7 / (30 * (n : ℝ)) - (1 - α) / 2 =
        7 / (30 * (n : ℝ)) := by ring
  simp_rw [hdiff]
  rw [MeasureTheory.setLIntegral_const, Real.volume_Icc]
  rw [← ENNReal.ofReal_mul (by positivity :
    0 ≤ 7 / (30 * (n : ℝ)))]
  congr 1
  field_simp [Nat.cast_ne_zero.mpr hn.ne']
  ring

/-- On the source, replacing the kernel by the selected upper corner costs at
most `750/n`. -/
lemma liuLogGridUpperIntegrand_le_integrand_add {n : ℕ} (hn : 0 < n)
    {x : ℝ × ℝ} (hx : x ∈ liuLogSourceRegion) :
    liuLogGridUpperIntegrand n x ≤ liuLogIntegrand x + 750 / (n : ℝ) := by
  have hxregion := liuLogSourceRegion_subset_gridRegion hn hx
  rw [liuLogGridRegion] at hxregion
  obtain ⟨q, hq, hxq⟩ := Set.mem_iUnion₂.1 hxregion
  rw [liuLogGridUpperIntegrand_eq_of_mem hn hq hxq]
  have hbox := liuLogGridCell_subset_ambientBox hn hq hxq
  have hd0 := liuLogDensity_nonneg hbox
  have hd := liuLogDensity_le_thirty hbox
  have hk := liuLogGrid_upperKernel_sub_le hn hq hxq
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hmul :
      (1 / (1 - liuAlphaGridPoint n (q.1 + 1) -
          liuBetaGridPoint n (q.2 + 1)) - liuLogKernel x) *
          liuLogDensity x ≤ (25 / (n : ℝ)) * 30 :=
    mul_le_mul hk.2 hd hd0 (by positivity)
  have hconst : (25 / (n : ℝ)) * 30 = 750 / (n : ℝ) := by
    field_simp
    ring
  unfold liuLogIntegrand
  calc
    _ = liuLogKernel x * liuLogDensity x +
        (1 / (1 - liuAlphaGridPoint n (q.1 + 1) -
          liuBetaGridPoint n (q.2 + 1)) - liuLogKernel x) *
          liuLogDensity x := by ring
    _ ≤ liuLogKernel x * liuLogDensity x + 750 / (n : ℝ) := by
      rw [← hconst]
      linarith

/-- A global integrable majorant separates the source error from the thin
geometric excess strip. -/
lemma liuLogGridUpperIntegrand_majorized {n : ℕ} (hn : 0 < n)
    (x : ℝ × ℝ) :
    liuLogGridUpperIntegrand n x ≤
      liuLogSourceRegion.indicator liuLogIntegrand x +
        (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1).indicator
          (fun _ => 750 / (n : ℝ)) x +
        (liuLogExcessStrip n).indicator (fun _ => 150) x := by
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  by_cases hs : x ∈ liuLogSourceRegion
  · have hambient := liuLogSourceRegion_subset_ambientBox hs
    have hunit : x ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 := by
      exact ⟨⟨by linarith [hambient.1.1], by linarith [hambient.1.2]⟩,
        ⟨by linarith [hambient.2.1], by linarith [hambient.2.2]⟩⟩
    rw [Set.indicator_of_mem hs, Set.indicator_of_mem hunit]
    have hstrip : 0 ≤
        (liuLogExcessStrip n).indicator (fun _ => (150 : ℝ)) x := by
      by_cases hx : x ∈ liuLogExcessStrip n
      · rw [Set.indicator_of_mem hx]
        norm_num
      · rw [Set.indicator_of_notMem hx]
    linarith [liuLogGridUpperIntegrand_le_integrand_add hn hs]
  · rw [Set.indicator_of_notMem hs]
    by_cases hg : x ∈ liuLogGridRegion n
    · have he : x ∈ liuLogExcessStrip n :=
        liuLogGridRegion_diff_source_subset_excessStrip hn ⟨hg, hs⟩
      rw [Set.indicator_of_mem he]
      have hunit : 0 ≤
          (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1).indicator
            (fun _ => 750 / (n : ℝ)) x := by
        by_cases hx : x ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1
        · rw [Set.indicator_of_mem hx]
          positivity
        · rw [Set.indicator_of_notMem hx]
      linarith [liuLogGridUpperIntegrand_le_oneHundredFifty hn hg]
    · rw [liuLogGridUpperIntegrand_eq_zero_of_notMem hg]
      have hunit : 0 ≤
          (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1).indicator
            (fun _ => 750 / (n : ℝ)) x := by
        by_cases hx : x ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1
        · rw [Set.indicator_of_mem hx]
          positivity
        · rw [Set.indicator_of_notMem hx]
      have hstrip : 0 ≤
          (liuLogExcessStrip n).indicator (fun _ => (150 : ℝ)) x := by
        by_cases hx : x ∈ liuLogExcessStrip n
        · rw [Set.indicator_of_mem hx]
          norm_num
        · rw [Set.indicator_of_notMem hx]
      linarith

/-- The grid upper sum exceeds Liu's source integral by at most `759/n`. -/
theorem liuLogGridUpperSum_sub_source_le (n : ℕ) (hn : 0 < n) :
    liuLogGridUpperSum n - liuSourceMainIntegral ≤ 759 / (n : ℝ) := by
  let unitBox : Set (ℝ × ℝ) := Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1
  let fSource := liuLogSourceRegion.indicator liuLogIntegrand
  let fUnit := unitBox.indicator (fun _ => 750 / (n : ℝ))
  let fStrip := (liuLogExcessStrip n).indicator (fun _ => (150 : ℝ))
  have hSource : Integrable fSource :=
    integrable_indicator_of_integrableOn measurableSet_liuLogSourceRegion
      (integrableOn_liuLogIntegrand measurableSet_liuLogSourceRegion
        liuLogSourceRegion_subset_ambientBox)
  have hUnit : Integrable fUnit := by
    apply integrable_indicator_of_integrableOn
      (measurableSet_Icc.prod measurableSet_Icc)
    apply integrableOn_const
    · dsimp [unitBox]
      rw [volume_unitBox]
      norm_num
    · finiteness
  have hStrip : Integrable fStrip := by
    apply integrable_indicator_of_integrableOn
      (measurableSet_liuLogExcessStrip n)
    apply integrableOn_const
    · rw [volume_liuLogExcessStrip hn]
      exact ENNReal.ofReal_ne_top
    · finiteness
  have hmono :
      (∫ x, liuLogGridUpperIntegrand n x) ≤
        ∫ x, (fSource x + fUnit x) + fStrip x := by
    apply MeasureTheory.integral_mono
      (integrable_liuLogGridUpperIntegrand n hn)
      ((hSource.add hUnit).add hStrip)
    intro x
    exact liuLogGridUpperIntegrand_majorized hn x
  rw [← liuLogGridUpperSum_eq_integral n hn] at hmono
  change liuLogGridUpperSum n ≤
    ∫ x, (fSource x + fUnit x) + fStrip x at hmono
  have hOuter := MeasureTheory.integral_add (hSource.add hUnit) hStrip
  change (∫ x, (fSource x + fUnit x) + fStrip x) =
    (∫ x, fSource x + fUnit x) + ∫ x, fStrip x at hOuter
  rw [hOuter] at hmono
  have hInner := MeasureTheory.integral_add hSource hUnit
  change (∫ x, fSource x + fUnit x) =
    (∫ x, fSource x) + ∫ x, fUnit x at hInner
  rw [hInner] at hmono
  dsimp [fSource, fUnit, fStrip, unitBox] at hmono
  rw [MeasureTheory.integral_indicator measurableSet_liuLogSourceRegion,
    ← liuSourceMainIntegral_eq_setIntegral,
    MeasureTheory.integral_indicator_const (750 / (n : ℝ))
      (measurableSet_Icc.prod measurableSet_Icc),
    MeasureTheory.integral_indicator_const (150 : ℝ)
      (measurableSet_liuLogExcessStrip n),
    MeasureTheory.Measure.real_def, volume_unitBox,
    MeasureTheory.Measure.real_def, volume_liuLogExcessStrip hn] at hmono
  simp only [ENNReal.toReal_one, smul_eq_mul] at hmono
  rw [ENNReal.toReal_ofReal (by positivity :
    0 ≤ 49 / (900 * (n : ℝ)))] at hmono
  have herr :
      750 / (n : ℝ) + 49 / (900 * (n : ℝ)) * 150 ≤
        759 / (n : ℝ) := by
    have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
    field_simp
    norm_num
  linarith

/-- The canonical logarithmic-grid upper sums converge to Liu's source
integral as the mesh tends to zero. -/
theorem tendsto_liuLogGridUpperSum_sourceMainIntegral :
    Tendsto (fun n : ℕ => liuLogGridUpperSum (n + 1)) atTop
      (nhds liuSourceMainIntegral) := by
  have herror :
      Tendsto (fun n : ℕ => (759 : ℝ) / ((n + 1 : ℕ) : ℝ)) atTop (nhds 0) := by
    simpa only [Nat.cast_add, Nat.cast_one, div_eq_mul_inv, one_mul, mul_zero] using
      (Tendsto.const_mul (759 : ℝ)
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ) :
          Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (nhds 0)))
  have hdiff :
      Tendsto
        (fun n : ℕ => liuLogGridUpperSum (n + 1) - liuSourceMainIntegral)
        atTop (nhds 0) := by
    apply squeeze_zero'
    · exact Filter.Eventually.of_forall fun n =>
        sub_nonneg.mpr
          (liuSourceMainIntegral_le_liuLogGridUpperSum (n + 1) (Nat.succ_pos n))
    · exact Filter.Eventually.of_forall fun n =>
        liuLogGridUpperSum_sub_source_le (n + 1) (Nat.succ_pos n)
    · exact herror
  have hconst :
      Tendsto (fun _ : ℕ => liuSourceMainIntegral) atTop
        (nhds liuSourceMainIntegral) :=
    tendsto_const_nhds
  simpa only [sub_add_cancel, zero_add] using hdiff.add hconst

end

end MathlibNt.SieveTheory.LiuWeight
