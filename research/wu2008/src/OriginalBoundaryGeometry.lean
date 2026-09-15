import OriginalBoundaryMeasure
open MeasureTheory Set
noncomputable section
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
namespace OriginalU8.Weighted
variable {a : ℝ}

def leftStrip (a : ℝ) (n : ℕ) : Set (ℝ × ℝ) :=
  Ioc (a-goldbachB9AlphaGridStep n) a ×ˢ Icc (1/4) (1/2)

def bottomStrip (a : ℝ) (n : ℕ) : Set (ℝ × ℝ) :=
  Icc a (1/3) ×ˢ Ioc (1/3-goldbachB9BetaGridStep n) (1/3)

theorem measurableSet_leftStrip (n : ℕ) : MeasurableSet (leftStrip a n) :=
  measurableSet_Ioc.prod measurableSet_Icc

theorem measurableSet_bottomStrip (n : ℕ) : MeasurableSet (bottomStrip a n) :=
  measurableSet_Icc.prod measurableSet_Ioc

theorem volume_leftStrip (n : ℕ) :
    volume (leftStrip a n) = ENNReal.ofReal ((17/240 : ℝ)/n) := by
  unfold leftStrip
  rw [Measure.volume_eq_prod ℝ ℝ, Measure.prod_prod, Real.volume_Ioc, Real.volume_Icc]
  rw [sub_sub_cancel, ← ENNReal.ofReal_mul (by
    unfold goldbachB9AlphaGridStep goldbachB9AlphaGridWidth; positivity)]
  congr 1
  unfold goldbachB9AlphaGridStep goldbachB9AlphaGridWidth
  ring

theorem volume_bottomStrip (hab : a ≤ 1/10) (n : ℕ) :
    volume (bottomStrip a n) = ENNReal.ofReal ((1/3-a)*goldbachB9BetaGridStep n) := by
  unfold bottomStrip
  rw [Measure.volume_eq_prod ℝ ℝ, Measure.prod_prod, Real.volume_Icc, Real.volume_Ioc]
  rw [sub_sub_cancel, ← ENNReal.ofReal_mul (by linarith : 0 ≤ (1/3 : ℝ)-a)]
def region (a : ℝ) (n : ℕ) (h : ℝ) : Set (ℝ × ℝ) :=
  ⋃ q ∈ cells a n h, goldbachB9LogGridCell n q

def obliqueStrip (a : ℝ) (n : ℕ) (h : ℝ) : Set (ℝ × ℝ) :=
  {x | x.1 ∈ Icc a (1 / 3) ∧
    (1 - x.1) / 2 < x.2 ∧
    x.2 < (1 - x.1) / 2 +
      (h + goldbachB9AlphaGridStep n + 2 * goldbachB9BetaGridStep n) / 2}

theorem measurableSet_obliqueStrip (n : ℕ) (h : ℝ) :
    MeasurableSet (obliqueStrip a n h) := by
  exact (measurableSet_Icc.preimage measurable_fst).inter
    ((measurableSet_lt (by fun_prop) measurable_snd).inter
      (measurableSet_lt measurable_snd (by fun_prop)))

theorem obliqueStrip_section (n : ℕ) (h : ℝ) (u : ℝ) :
    Prod.mk u ⁻¹' obliqueStrip a n h =
      if u ∈ Icc a (1 / 3) then
        Ioo ((1 - u) / 2) ((1 - u) / 2 +
          (h + goldbachB9AlphaGridStep n + 2 * goldbachB9BetaGridStep n) / 2) else ∅ := by
  classical
  ext v
  simp [obliqueStrip, and_assoc]

theorem volume_obliqueStrip (n : ℕ) (h : ℝ) (hh : 0 ≤ h) :
    volume (obliqueStrip a n h) = ENNReal.ofReal ((1/3-a)*((h + goldbachB9AlphaGridStep n + 2*goldbachB9BetaGridStep n)/2)) := by
  classical
  rw [Measure.volume_eq_prod ℝ ℝ,
    Measure.prod_apply (measurableSet_obliqueStrip n h)]
  have hfun : (fun u : ℝ => volume (Prod.mk u ⁻¹' obliqueStrip a n h)) =
      (Icc a (1 / 3)).indicator
        (fun _ => ENNReal.ofReal
          ((h + goldbachB9AlphaGridStep n + 2 * goldbachB9BetaGridStep n) / 2)) := by
    funext u
    rw [obliqueStrip_section]
    by_cases hu : u ∈ Icc a (1 / 3)
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

theorem region_subset_ambient {n : ℕ} (hn : 0 < n) (h : ℝ) :
    region a n h ⊆ goldbachB9LogAmbientBox := by
  intro x hx
  obtain ⟨q, _, hxq⟩ := Set.mem_iUnion₂.mp hx
  exact goldbachB9LogGridCell_subset_ambientBox hn q hxq

theorem region_excess_subset {n : ℕ} (hn : 0 < n) (h : ℝ) :
    region a n h \ source a ⊆
      leftStrip a n ∪ bottomStrip a n ∪
        obliqueStrip a n h ∪ fouvryG9WeightedRightStrip n := by
  intro x hx
  obtain ⟨hg, hs⟩ := hx
  obtain ⟨q, hq, hxq⟩ := Set.mem_iUnion₂.mp hg
  have hb := goldbachB9LogGridCell_subset_ambientBox hn q hxq
  have ht := selected_cell_geometry q hq hxq.1 hxq.2
  by_cases hl : x.1 ≤ a
  · exact Or.inl (Or.inl (Or.inl ⟨⟨ht.1, hl⟩, hb.2⟩))
  have hl' := lt_of_not_ge hl
  by_cases hr : (1/10 : ℝ) < x.1
  · exact Or.inr ⟨⟨hr, ht.2.1.le⟩, hb.2⟩
  by_cases hd : x.2 ≤ (1/3 : ℝ)
  · exact Or.inl (Or.inl (Or.inr ⟨⟨hl'.le, hb.1.2⟩, ⟨ht.2.2.1, hd⟩⟩))
  apply Or.inl ∘ Or.inr
  have hu : (1-x.1)/2 < x.2 := by
    by_contra hh
    exact hs ⟨⟨hl', le_of_not_gt hr⟩, ⟨lt_of_not_ge hd, le_of_not_gt hh⟩⟩
  exact ⟨⟨hl'.le, hb.1.2⟩, hu, by linarith [ht.2.2.2]⟩


end OriginalU8.Weighted
