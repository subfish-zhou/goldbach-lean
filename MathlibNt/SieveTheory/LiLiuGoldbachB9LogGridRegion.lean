import MathlibNt.SieveTheory.LiLiuGoldbachB9LogGrid
import MathlibNt.SieveTheory.Liu.PrimePairs.LiuLogCoordinates

open MeasureTheory Set

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

noncomputable section

def goldbachB9LogGridCell (n : ℕ) (q : Fin n × Fin n) : Set (ℝ × ℝ) :=
  Ioc (goldbachB9AlphaGridPoint n q.1) (goldbachB9AlphaGridPoint n (q.1 + 1)) ×ˢ
    Ioc (goldbachB9BetaGridPoint n q.2) (goldbachB9BetaGridPoint n (q.2 + 1))

def goldbachB9LogGridRegion (n : ℕ) : Set (ℝ × ℝ) :=
  ⋃ q ∈ goldbachB9LogGridCells n, goldbachB9LogGridCell n q

/-- This half-open continuous region does not change the finite closed carrier. -/
def goldbachB9LogSourceRegion : Set (ℝ × ℝ) :=
  {x | x.1 ∈ Ioc (4 / 53) (1 / 3) ∧ x.2 ∈ Ioc (1 / 3) ((1 - x.1) / 2)}

def goldbachB9LogAmbientBox : Set (ℝ × ℝ) :=
  Icc (1 / 20) (1 / 3) ×ˢ Icc (1 / 4) (1 / 2)

def goldbachB9LeftStrip (n : ℕ) : Set (ℝ × ℝ) :=
  Ioc (4 / 53 - goldbachB9AlphaGridStep n) (4 / 53) ×ˢ Icc (1 / 4) (1 / 2)

def goldbachB9BottomStrip (n : ℕ) : Set (ℝ × ℝ) :=
  Icc (4 / 53) (1 / 3) ×ˢ Ioc (1 / 3 - goldbachB9BetaGridStep n) (1 / 3)


theorem measurableSet_goldbachB9LogGridCell (n : ℕ) (q : Fin n × Fin n) :
    MeasurableSet (goldbachB9LogGridCell n q) :=
  measurableSet_Ioc.prod measurableSet_Ioc


theorem isCompact_goldbachB9LogAmbientBox : IsCompact goldbachB9LogAmbientBox :=
  isCompact_Icc.prod isCompact_Icc

theorem measurableSet_goldbachB9LeftStrip (n : ℕ) :
    MeasurableSet (goldbachB9LeftStrip n) :=
  measurableSet_Ioc.prod measurableSet_Icc

theorem measurableSet_goldbachB9BottomStrip (n : ℕ) :
    MeasurableSet (goldbachB9BottomStrip n) :=
  measurableSet_Icc.prod measurableSet_Ioc


theorem volume_goldbachB9LeftStrip (n : ℕ) :
    volume (goldbachB9LeftStrip n) = ENNReal.ofReal ((17 / 240 : ℝ) / n) := by
  unfold goldbachB9LeftStrip
  rw [Measure.volume_eq_prod ℝ ℝ, Measure.prod_prod, Real.volume_Ioc, Real.volume_Icc]
  have hlen : (4 / 53 : ℝ) - (4 / 53 - goldbachB9AlphaGridStep n) =
      goldbachB9AlphaGridStep n := by ring
  rw [hlen, ← ENNReal.ofReal_mul (by
    unfold goldbachB9AlphaGridStep goldbachB9AlphaGridWidth
    positivity)]
  congr 1
  unfold goldbachB9AlphaGridStep goldbachB9AlphaGridWidth
  ring

theorem volume_goldbachB9BottomStrip (n : ℕ) :
    volume (goldbachB9BottomStrip n) = ENNReal.ofReal ((41 / 636 : ℝ) / n) := by
  unfold goldbachB9BottomStrip
  rw [Measure.volume_eq_prod ℝ ℝ, Measure.prod_prod, Real.volume_Icc, Real.volume_Ioc,
    ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 3 - 4 / 53)]
  congr 1
  unfold goldbachB9BetaGridStep goldbachB9BetaGridWidth
  ring


theorem goldbachB9LogGridCell_pairwiseDisjoint {n : ℕ} (hn : 0 < n) :
    (Set.univ : Set (Fin n × Fin n)).Pairwise
      (Function.onFun Disjoint (goldbachB9LogGridCell n)) := by
  exact MathlibNt.Analysis.LogGridEstimates.cells_pairwiseDisjoint n
    (goldbachB9AlphaGridPoint n) (goldbachB9BetaGridPoint n)
    (fun _ _ h => goldbachB9AlphaGridPoint_mono hn h)
    (fun _ _ h => goldbachB9BetaGridPoint_mono hn h)

theorem goldbachB9LogGridCell_subset_ambientBox {n : ℕ} (hn : 0 < n)
    (q : Fin n × Fin n) : goldbachB9LogGridCell n q ⊆ goldbachB9LogAmbientBox := by
  intro x hx
  have ha : (1 / 20 : ℝ) ≤ goldbachB9AlphaGridPoint n q.1 := by
    rw [goldbachB9AlphaGridPoint_eq_step]
    exact le_add_of_nonneg_right
      (mul_nonneg (Nat.cast_nonneg _) (goldbachB9AlphaGridStep_pos hn).le)
  have hb : (1 / 4 : ℝ) ≤ goldbachB9BetaGridPoint n q.2 := by
    rw [goldbachB9BetaGridPoint_eq_step]
    exact le_add_of_nonneg_right
      (mul_nonneg (Nat.cast_nonneg _) (goldbachB9BetaGridStep_pos hn).le)
  exact ⟨⟨ha.trans hx.1.1.le,
      hx.1.2.trans (goldbachB9AlphaGridPoint_succ_le_end hn q.1.isLt)⟩,
    ⟨hb.trans hx.2.1.le,
      hx.2.2.trans (goldbachB9BetaGridPoint_succ_le_end hn q.2.isLt)⟩⟩

theorem goldbachB9LogGridRegion_subset_ambientBox {n : ℕ} (hn : 0 < n) :
    goldbachB9LogGridRegion n ⊆ goldbachB9LogAmbientBox := by
  intro x hx
  obtain ⟨q, _, hxq⟩ := Set.mem_iUnion₂.mp hx
  exact goldbachB9LogGridCell_subset_ambientBox hn q hxq


theorem goldbachB9LogAmbientBox_gap {x : ℝ × ℝ} (hx : x ∈ goldbachB9LogAmbientBox) :
    (1 / 6 : ℝ) ≤ 1 - x.1 - x.2 := by
  linarith [hx.1.2, hx.2.2]


end

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig