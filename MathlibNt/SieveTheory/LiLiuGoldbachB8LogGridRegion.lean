import MathlibNt.Analysis.LogGridEstimates
import MathlibNt.SieveTheory.LiLiuGoldbachB8FixedGridLimit
import MathlibNt.SieveTheory.LiLiuGoldbachB8DiagonalStrip

open MeasureTheory Set

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

noncomputable section

def goldbachB8LogGridCell (n : ℕ) (q : Fin n × Fin n) : Set (ℝ × ℝ) :=
  Ioc (goldbachB8AlphaGridPoint n q.1) (goldbachB8AlphaGridPoint n (q.1 + 1)) ×ˢ
    Ioc (goldbachB8BetaGridPoint n q.2) (goldbachB8BetaGridPoint n (q.2 + 1))

def goldbachB8LogGridRegion (n : ℕ) : Set (ℝ × ℝ) :=
  ⋃ q ∈ goldbachB8LogGridCells n, goldbachB8LogGridCell n q

/-- Half-open continuous source; this does not alter the finite closed carrier. -/
def goldbachB8LogSourceRegion : Set (ℝ × ℝ) :=
  {x | x.1 ∈ Ioc (3 / 11) (1 / 3) ∧ x.2 ∈ Ioc x.1 ((1 - x.1) / 2)}

def goldbachB8LogAmbientBox : Set (ℝ × ℝ) :=
  Icc (1 / 4) (1 / 3) ×ˢ Icc (1 / 4) (4 / 11)

def goldbachB8LeftStrip (n : ℕ) : Set (ℝ × ℝ) :=
  Ioc (3 / 11 - goldbachB8AlphaGridStep n) (3 / 11) ×ˢ Icc (1 / 4) (4 / 11)

def goldbachB8ObliqueStrip (n : ℕ) : Set (ℝ × ℝ) :=
  {x | x.1 ∈ Icc (3 / 11) (1 / 3) ∧
    (1 - x.1) / 2 < x.2 ∧
    x.2 < (1 - x.1) / 2 +
      (goldbachB8AlphaGridStep n + 2 * goldbachB8BetaGridStep n) / 2}

theorem measurableSet_goldbachB8LogGridCell (n : ℕ) (q : Fin n × Fin n) :
    MeasurableSet (goldbachB8LogGridCell n q) :=
  measurableSet_Ioc.prod measurableSet_Ioc

theorem measurableSet_goldbachB8LogGridRegion (n : ℕ) :
    MeasurableSet (goldbachB8LogGridRegion n) := by
  classical
  exact Finset.measurableSet_biUnion _ fun q _ => measurableSet_goldbachB8LogGridCell n q

theorem measurableSet_goldbachB8LogSourceRegion :
    MeasurableSet goldbachB8LogSourceRegion := by
  exact (measurableSet_Ioc.preimage measurable_fst).inter
    ((isOpen_lt continuous_fst continuous_snd).measurableSet.inter
      (measurableSet_le measurable_snd (by fun_prop)))

theorem measurableSet_goldbachB8LogAmbientBox :
    MeasurableSet goldbachB8LogAmbientBox :=
  measurableSet_Icc.prod measurableSet_Icc

theorem isCompact_goldbachB8LogAmbientBox : IsCompact goldbachB8LogAmbientBox :=
  isCompact_Icc.prod isCompact_Icc

theorem measurableSet_goldbachB8LeftStrip (n : ℕ) :
    MeasurableSet (goldbachB8LeftStrip n) :=
  measurableSet_Ioc.prod measurableSet_Icc

theorem measurableSet_goldbachB8ObliqueStrip (n : ℕ) :
    MeasurableSet (goldbachB8ObliqueStrip n) := by
  exact (measurableSet_Icc.preimage measurable_fst).inter
    ((measurableSet_lt (by fun_prop) measurable_snd).inter
      (measurableSet_lt measurable_snd (by fun_prop)))

theorem goldbachB8LogSourceRegion_section (u : ℝ) :
    Prod.mk u ⁻¹' goldbachB8LogSourceRegion =
      if u ∈ Ioc (3 / 11 : ℝ) (1 / 3) then Ioc u ((1 - u) / 2) else ∅ := by
  classical
  ext v
  simp [goldbachB8LogSourceRegion]

theorem goldbachB8LeftStrip_section (n : ℕ) (u : ℝ) :
    Prod.mk u ⁻¹' goldbachB8LeftStrip n =
      if u ∈ Ioc (3 / 11 - goldbachB8AlphaGridStep n) (3 / 11) then
        Icc (1 / 4) (4 / 11) else ∅ := by
  classical
  ext v
  simp [goldbachB8LeftStrip]

theorem goldbachB8DiagonalStrip_section (n : ℕ) (u : ℝ) :
    Prod.mk u ⁻¹' goldbachB8DiagonalStrip n =
      if u ∈ Icc (3 / 11 : ℝ) (1 / 3) then
        Ioc (u - (goldbachB8AlphaGridStep n + goldbachB8BetaGridStep n)) u else ∅ := by
  classical
  exact goldbachAffineDiagonalStrip_section _ _ _ _

theorem goldbachB8ObliqueStrip_section (n : ℕ) (u : ℝ) :
    Prod.mk u ⁻¹' goldbachB8ObliqueStrip n =
      if u ∈ Icc (3 / 11 : ℝ) (1 / 3) then
        Ioo ((1 - u) / 2) ((1 - u) / 2 +
          (goldbachB8AlphaGridStep n + 2 * goldbachB8BetaGridStep n) / 2) else ∅ := by
  classical
  ext v
  simp [goldbachB8ObliqueStrip, and_assoc]

theorem volume_goldbachB8LeftStrip (n : ℕ) :
    volume (goldbachB8LeftStrip n) = ENNReal.ofReal ((5 / 528 : ℝ) / n) := by
  unfold goldbachB8LeftStrip
  rw [Measure.volume_eq_prod ℝ ℝ, Measure.prod_prod, Real.volume_Ioc, Real.volume_Icc]
  have hlen : (3 / 11 : ℝ) - (3 / 11 - goldbachB8AlphaGridStep n) =
      goldbachB8AlphaGridStep n := by ring
  rw [hlen, ← ENNReal.ofReal_mul (by
    unfold goldbachB8AlphaGridStep goldbachB8AlphaGridWidth
    positivity)]
  congr 1
  unfold goldbachB8AlphaGridStep goldbachB8AlphaGridWidth
  ring

theorem volume_goldbachB8ObliqueStrip (n : ℕ) :
    volume (goldbachB8ObliqueStrip n) = ENNReal.ofReal ((41 / 4356 : ℝ) / n) := by
  unfold goldbachB8ObliqueStrip
  rw [MathlibNt.Analysis.LogGridEstimates.volume_strip (3 / 11) (1 / 3)
    ((goldbachB8AlphaGridStep n + 2 * goldbachB8BetaGridStep n) / 2) (fun u => (1 - u) / 2)
    (measurableSet_goldbachB8ObliqueStrip n) (by
    unfold goldbachB8AlphaGridStep goldbachB8BetaGridStep
      goldbachB8AlphaGridWidth goldbachB8BetaGridWidth
    positivity)]
  congr 1
  unfold goldbachB8AlphaGridStep goldbachB8BetaGridStep
    goldbachB8AlphaGridWidth goldbachB8BetaGridWidth
  ring

theorem goldbachB8LogGridCell_pairwiseDisjoint {n : ℕ} (hn : 0 < n) :
    (Set.univ : Set (Fin n × Fin n)).Pairwise
      (Function.onFun Disjoint (goldbachB8LogGridCell n)) := by
  exact MathlibNt.Analysis.LogGridEstimates.cells_pairwiseDisjoint n
    (goldbachB8AlphaGridPoint n) (goldbachB8BetaGridPoint n)
    (fun _ _ h => goldbachB8AlphaGridPoint_mono hn h)
    (fun _ _ h => goldbachB8BetaGridPoint_mono hn h)

theorem goldbachB8LogGridCell_subset_ambientBox {n : ℕ} (hn : 0 < n)
    (q : Fin n × Fin n) : goldbachB8LogGridCell n q ⊆ goldbachB8LogAmbientBox := by
  intro x hx
  have ha : (1 / 4 : ℝ) ≤ goldbachB8AlphaGridPoint n q.1 := by
    rw [goldbachB8AlphaGridPoint_eq_step]
    exact le_add_of_nonneg_right
      (mul_nonneg (Nat.cast_nonneg _) (goldbachB8AlphaGridStep_pos hn).le)
  have hb : (1 / 4 : ℝ) ≤ goldbachB8BetaGridPoint n q.2 := by
    rw [goldbachB8BetaGridPoint_eq_step]
    exact le_add_of_nonneg_right
      (mul_nonneg (Nat.cast_nonneg _) (goldbachB8BetaGridStep_pos hn).le)
  exact ⟨⟨ha.trans hx.1.1.le,
      hx.1.2.trans (goldbachB8AlphaGridPoint_succ_le_end hn q.1.isLt)⟩,
    ⟨hb.trans hx.2.1.le,
      hx.2.2.trans (goldbachB8BetaGridPoint_succ_le_end hn q.2.isLt)⟩⟩

theorem goldbachB8LogGridRegion_subset_ambientBox {n : ℕ} (hn : 0 < n) :
    goldbachB8LogGridRegion n ⊆ goldbachB8LogAmbientBox := by
  intro x hx
  obtain ⟨q, _, hxq⟩ := Set.mem_iUnion₂.mp hx
  exact goldbachB8LogGridCell_subset_ambientBox hn q hxq

theorem goldbachB8LogSourceRegion_subset_ambientBox :
    goldbachB8LogSourceRegion ⊆ goldbachB8LogAmbientBox := by
  intro x hx
  change x.1 ∈ Ioc (3 / 11 : ℝ) (1 / 3) ∧ x.2 ∈ Ioc x.1 ((1 - x.1) / 2) at hx
  exact ⟨⟨by linarith [hx.1.1], hx.1.2⟩,
    ⟨by linarith [hx.1.1, hx.2.1], by linarith [hx.1.1, hx.2.2]⟩⟩

theorem goldbachB8LogAmbientBox_gap {x : ℝ × ℝ} (hx : x ∈ goldbachB8LogAmbientBox) :
    (10 / 33 : ℝ) ≤ 1 - x.1 - x.2 := by
  linarith [hx.1.2, hx.2.2]

/-- All excess points, including equality on the diagonal, are paid by three strips. -/
theorem goldbachB8LogGridRegion_excess_subset {n : ℕ} (hn : 0 < n) :
    goldbachB8LogGridRegion n \ goldbachB8LogSourceRegion ⊆
      goldbachB8LeftStrip n ∪ goldbachB8DiagonalStrip n ∪ goldbachB8ObliqueStrip n := by
  intro x hx
  obtain ⟨hg, hs⟩ := hx
  obtain ⟨q, hq, hxq⟩ := Set.mem_iUnion₂.mp hg
  have hb := goldbachB8LogGridCell_subset_ambientBox hn q hxq
  have hsel := mem_goldbachB8LogGridCells_iff.mp hq
  change
    x.1 ∈ Ioc (goldbachB8AlphaGridPoint n q.1) (goldbachB8AlphaGridPoint n (q.1 + 1)) ∧
      x.2 ∈ Ioc (goldbachB8BetaGridPoint n q.2) (goldbachB8BetaGridPoint n (q.2 + 1))
    at hxq
  rw [goldbachB8AlphaGridPoint_succ, goldbachB8BetaGridPoint_succ] at hxq hsel
  dsimp [goldbachB8Gamma] at hsel
  by_cases hl : x.1 ≤ (3 / 11 : ℝ)
  · apply Or.inl ∘ Or.inl
    exact ⟨⟨by linarith [hxq.1.1, hsel.1], hl⟩, hb.2⟩
  · have hl' : (3 / 11 : ℝ) < x.1 := lt_of_not_ge hl
    by_cases hd : x.2 ≤ x.1
    · apply Or.inl ∘ Or.inr
      change x.1 ∈ Icc (3 / 11) (1 / 3) ∧
        x.2 ∈ Ioc (x.1 - (goldbachB8AlphaGridStep n + goldbachB8BetaGridStep n)) x.1
      exact ⟨⟨hl'.le, hb.1.2⟩, ⟨by linarith [hxq.1.2, hxq.2.1, hsel.2.1], hd⟩⟩
    · apply Or.inr
      have hu : (1 - x.1) / 2 < x.2 := by
        by_contra h
        exact hs ⟨⟨hl', hb.1.2⟩, ⟨lt_of_not_ge hd, le_of_not_gt h⟩⟩
      exact ⟨⟨hl'.le, hb.1.2⟩, hu, by linarith [hxq.1.2, hxq.2.2, hsel.2.2]⟩

end

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig