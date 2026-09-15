import MathlibNt.SieveTheory.LiLiuGoldbachB9LogGrid
import MathlibNt.SieveTheory.LiuPrimePairLogGridLimit

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

def goldbachB9ObliqueStrip (n : ℕ) : Set (ℝ × ℝ) :=
  {x | x.1 ∈ Icc (4 / 53) (1 / 3) ∧
    (1 - x.1) / 2 < x.2 ∧
    x.2 < (1 - x.1) / 2 +
      (goldbachB9AlphaGridStep n + 2 * goldbachB9BetaGridStep n) / 2}

theorem measurableSet_goldbachB9LogGridCell (n : ℕ) (q : Fin n × Fin n) :
    MeasurableSet (goldbachB9LogGridCell n q) :=
  measurableSet_Ioc.prod measurableSet_Ioc

theorem measurableSet_goldbachB9LogGridRegion (n : ℕ) :
    MeasurableSet (goldbachB9LogGridRegion n) := by
  classical
  exact Finset.measurableSet_biUnion _ fun q _ => measurableSet_goldbachB9LogGridCell n q

theorem measurableSet_goldbachB9LogSourceRegion :
    MeasurableSet goldbachB9LogSourceRegion := by
  exact (measurableSet_Ioc.preimage measurable_fst).inter
    ((measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd (by fun_prop)))

theorem measurableSet_goldbachB9LogAmbientBox :
    MeasurableSet goldbachB9LogAmbientBox :=
  measurableSet_Icc.prod measurableSet_Icc

theorem isCompact_goldbachB9LogAmbientBox : IsCompact goldbachB9LogAmbientBox :=
  isCompact_Icc.prod isCompact_Icc

theorem measurableSet_goldbachB9LeftStrip (n : ℕ) :
    MeasurableSet (goldbachB9LeftStrip n) :=
  measurableSet_Ioc.prod measurableSet_Icc

theorem measurableSet_goldbachB9BottomStrip (n : ℕ) :
    MeasurableSet (goldbachB9BottomStrip n) :=
  measurableSet_Icc.prod measurableSet_Ioc

theorem measurableSet_goldbachB9ObliqueStrip (n : ℕ) :
    MeasurableSet (goldbachB9ObliqueStrip n) := by
  exact (measurableSet_Icc.preimage measurable_fst).inter
    ((measurableSet_lt (by fun_prop) measurable_snd).inter
      (measurableSet_lt measurable_snd (by fun_prop)))

theorem goldbachB9LogSourceRegion_section (u : ℝ) :
    Prod.mk u ⁻¹' goldbachB9LogSourceRegion =
      if u ∈ Ioc (4 / 53 : ℝ) (1 / 3) then Ioc (1 / 3) ((1 - u) / 2) else ∅ := by
  classical
  ext v
  simp [goldbachB9LogSourceRegion]

theorem goldbachB9LeftStrip_section (n : ℕ) (u : ℝ) :
    Prod.mk u ⁻¹' goldbachB9LeftStrip n =
      if u ∈ Ioc (4 / 53 - goldbachB9AlphaGridStep n) (4 / 53) then
        Icc (1 / 4) (1 / 2) else ∅ := by
  classical
  ext v
  simp [goldbachB9LeftStrip]

theorem goldbachB9BottomStrip_section (n : ℕ) (u : ℝ) :
    Prod.mk u ⁻¹' goldbachB9BottomStrip n =
      if u ∈ Icc (4 / 53 : ℝ) (1 / 3) then
        Ioc (1 / 3 - goldbachB9BetaGridStep n) (1 / 3) else ∅ := by
  classical
  ext v
  simp [goldbachB9BottomStrip]

theorem goldbachB9ObliqueStrip_section (n : ℕ) (u : ℝ) :
    Prod.mk u ⁻¹' goldbachB9ObliqueStrip n =
      if u ∈ Icc (4 / 53 : ℝ) (1 / 3) then
        Ioo ((1 - u) / 2) ((1 - u) / 2 +
          (goldbachB9AlphaGridStep n + 2 * goldbachB9BetaGridStep n) / 2) else ∅ := by
  classical
  ext v
  simp [goldbachB9ObliqueStrip, and_assoc]

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

theorem volume_goldbachB9ObliqueStrip (n : ℕ) :
    volume (goldbachB9ObliqueStrip n) = ENNReal.ofReal ((1927 / 19080 : ℝ) / n) := by
  classical
  rw [Measure.volume_eq_prod ℝ ℝ,
    Measure.prod_apply (measurableSet_goldbachB9ObliqueStrip n)]
  have hfun : (fun u : ℝ => volume (Prod.mk u ⁻¹' goldbachB9ObliqueStrip n)) =
      (Icc (4 / 53 : ℝ) (1 / 3)).indicator
        (fun _ => ENNReal.ofReal
          ((goldbachB9AlphaGridStep n + 2 * goldbachB9BetaGridStep n) / 2)) := by
    funext u
    rw [goldbachB9ObliqueStrip_section]
    by_cases hu : u ∈ Icc (4 / 53 : ℝ) (1 / 3)
    · rw [if_pos hu, indicator_of_mem hu, Real.volume_Ioo]
      congr 1
      ring
    · rw [if_neg hu, indicator_of_notMem hu, measure_empty]
  rw [hfun, lintegral_indicator measurableSet_Icc, setLIntegral_const, Real.volume_Icc,
    ← ENNReal.ofReal_mul (by
      unfold goldbachB9AlphaGridStep goldbachB9BetaGridStep
        goldbachB9AlphaGridWidth goldbachB9BetaGridWidth
      positivity)]
  congr 1
  unfold goldbachB9AlphaGridStep goldbachB9BetaGridStep
    goldbachB9AlphaGridWidth goldbachB9BetaGridWidth
  ring

theorem goldbachB9LogGridCell_pairwiseDisjoint {n : ℕ} (hn : 0 < n) :
    (Set.univ : Set (Fin n × Fin n)).Pairwise
      (Function.onFun Disjoint (goldbachB9LogGridCell n)) := by
  intro q _ r _ hqr
  change Disjoint (goldbachB9LogGridCell n q) (goldbachB9LogGridCell n r)
  rw [Set.disjoint_left]
  intro x hxq hxr
  change
    x.1 ∈ Ioc (goldbachB9AlphaGridPoint n q.1) (goldbachB9AlphaGridPoint n (q.1 + 1)) ∧
      x.2 ∈ Ioc (goldbachB9BetaGridPoint n q.2) (goldbachB9BetaGridPoint n (q.2 + 1))
    at hxq
  change
    x.1 ∈ Ioc (goldbachB9AlphaGridPoint n r.1) (goldbachB9AlphaGridPoint n (r.1 + 1)) ∧
      x.2 ∈ Ioc (goldbachB9BetaGridPoint n r.2) (goldbachB9BetaGridPoint n (r.2 + 1))
    at hxr
  by_cases hi : q.1 = r.1
  · have hj : q.2 ≠ r.2 := fun h => hqr (Prod.ext hi h)
    rcases lt_or_gt_of_ne hj with hjlt | hjgt
    · have hle := goldbachB9BetaGridPoint_mono hn
        (show (q.2 : ℕ) + 1 ≤ (r.2 : ℕ) by omega)
      exact not_lt_of_ge hle (hxr.2.1.trans_le hxq.2.2)
    · have hle := goldbachB9BetaGridPoint_mono hn
        (show (r.2 : ℕ) + 1 ≤ (q.2 : ℕ) by omega)
      exact not_lt_of_ge hle (hxq.2.1.trans_le hxr.2.2)
  · rcases lt_or_gt_of_ne hi with hilt | higt
    · have hle := goldbachB9AlphaGridPoint_mono hn
        (show (q.1 : ℕ) + 1 ≤ (r.1 : ℕ) by omega)
      exact not_lt_of_ge hle (hxr.1.1.trans_le hxq.1.2)
    · have hle := goldbachB9AlphaGridPoint_mono hn
        (show (r.1 : ℕ) + 1 ≤ (q.1 : ℕ) by omega)
      exact not_lt_of_ge hle (hxq.1.1.trans_le hxr.1.2)

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

theorem goldbachB9LogSourceRegion_subset_ambientBox :
    goldbachB9LogSourceRegion ⊆ goldbachB9LogAmbientBox := by
  intro x hx
  change x.1 ∈ Ioc (4 / 53 : ℝ) (1 / 3) ∧ x.2 ∈ Ioc (1 / 3) ((1 - x.1) / 2) at hx
  exact ⟨⟨by linarith [hx.1.1], hx.1.2⟩,
    ⟨by linarith [hx.2.1], by linarith [hx.1.1, hx.2.2]⟩⟩

theorem goldbachB9LogAmbientBox_gap {x : ℝ × ℝ} (hx : x ∈ goldbachB9LogAmbientBox) :
    (1 / 6 : ℝ) ≤ 1 - x.1 - x.2 := by
  linarith [hx.1.2, hx.2.2]

/-- The source has a horizontal lower edge, not the B8 diagonal edge. -/
theorem goldbachB9LogGridRegion_excess_subset {n : ℕ} (hn : 0 < n) :
    goldbachB9LogGridRegion n \ goldbachB9LogSourceRegion ⊆
      goldbachB9LeftStrip n ∪ goldbachB9BottomStrip n ∪ goldbachB9ObliqueStrip n := by
  intro x hx
  obtain ⟨hg, hs⟩ := hx
  obtain ⟨q, hq, hxq⟩ := Set.mem_iUnion₂.mp hg
  have hb := goldbachB9LogGridCell_subset_ambientBox hn q hxq
  have hsel := mem_goldbachB9LogGridCells_iff.mp hq
  change
    x.1 ∈ Ioc (goldbachB9AlphaGridPoint n q.1) (goldbachB9AlphaGridPoint n (q.1 + 1)) ∧
      x.2 ∈ Ioc (goldbachB9BetaGridPoint n q.2) (goldbachB9BetaGridPoint n (q.2 + 1))
    at hxq
  rw [goldbachB9AlphaGridPoint_succ, goldbachB9BetaGridPoint_succ] at hxq hsel
  by_cases hl : x.1 ≤ (4 / 53 : ℝ)
  · apply Or.inl ∘ Or.inl
    exact ⟨⟨by linarith [hxq.1.1, hsel.1], hl⟩, hb.2⟩
  · have hl' : (4 / 53 : ℝ) < x.1 := lt_of_not_ge hl
    by_cases hd : x.2 ≤ (1 / 3 : ℝ)
    · apply Or.inl ∘ Or.inr
      exact ⟨⟨hl'.le, hb.1.2⟩, ⟨by linarith [hxq.2.1, hsel.2.1], hd⟩⟩
    · apply Or.inr
      have hu : (1 - x.1) / 2 < x.2 := by
        by_contra h
        exact hs ⟨⟨hl', hb.1.2⟩, ⟨lt_of_not_ge hd, le_of_not_gt h⟩⟩
      exact ⟨⟨hl'.le, hb.1.2⟩, hu, by linarith [hxq.1.2, hxq.2.2, hsel.2.2]⟩

end

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig