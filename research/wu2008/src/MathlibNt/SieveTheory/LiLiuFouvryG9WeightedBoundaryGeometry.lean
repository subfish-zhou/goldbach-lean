import MathlibNt.SieveTheory.LiLiuFouvryG9WeightedBoundary
open MeasureTheory Set
noncomputable section
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
set_option maxHeartbeats 800000

def fouvryG9WeightedRegion (n : ℕ) (h : ℝ) : Set (ℝ × ℝ) :=
  ⋃ q ∈ fouvryG9RelaxedIntegralCells n h, goldbachB9LogGridCell n q

def fouvryG9WeightedRightStrip (n : ℕ) : Set (ℝ × ℝ) :=
  Ioc (1/10) (1/10 + goldbachB9AlphaGridStep n) ×ˢ Icc (1/4) (1/2)

theorem measurableSet_fouvryG9WeightedRightStrip (n : ℕ) :
    MeasurableSet (fouvryG9WeightedRightStrip n) :=
  measurableSet_Ioc.prod measurableSet_Icc

theorem volume_fouvryG9WeightedRightStrip (n : ℕ) :
    volume (fouvryG9WeightedRightStrip n) = ENNReal.ofReal ((17/240 : ℝ)/n) := by
  unfold fouvryG9WeightedRightStrip
  rw [Measure.volume_eq_prod ℝ ℝ, Measure.prod_prod, Real.volume_Ioc, Real.volume_Icc]
  rw [add_sub_cancel_left, ← ENNReal.ofReal_mul (by
    unfold goldbachB9AlphaGridStep goldbachB9AlphaGridWidth; positivity)]
  congr 1
  unfold goldbachB9AlphaGridStep goldbachB9AlphaGridWidth
  ring

def fouvryG9WeightedObliqueStrip (n : ℕ) (h : ℝ) : Set (ℝ × ℝ) :=
  {x | x.1 ∈ Icc (4 / 53) (1 / 3) ∧
    (1 - x.1) / 2 < x.2 ∧
    x.2 < (1 - x.1) / 2 +
      (h + goldbachB9AlphaGridStep n + 2 * goldbachB9BetaGridStep n) / 2}

theorem measurableSet_fouvryG9WeightedObliqueStrip (n : ℕ) (h : ℝ) :
    MeasurableSet (fouvryG9WeightedObliqueStrip n h) := by
  exact (measurableSet_Icc.preimage measurable_fst).inter
    ((measurableSet_lt (by fun_prop) measurable_snd).inter
      (measurableSet_lt measurable_snd (by fun_prop)))

theorem fouvryG9WeightedObliqueStrip_section (n : ℕ) (h : ℝ) (u : ℝ) :
    Prod.mk u ⁻¹' fouvryG9WeightedObliqueStrip n h =
      if u ∈ Icc (4 / 53 : ℝ) (1 / 3) then
        Ioo ((1 - u) / 2) ((1 - u) / 2 +
          (h + goldbachB9AlphaGridStep n + 2 * goldbachB9BetaGridStep n) / 2) else ∅ := by
  classical
  ext v
  simp [fouvryG9WeightedObliqueStrip, and_assoc]

theorem volume_fouvryG9WeightedObliqueStrip (n : ℕ) (h : ℝ) (hh : 0 ≤ h) :
    volume (fouvryG9WeightedObliqueStrip n h) = ENNReal.ofReal ((41/318 : ℝ)*h + (1927 / 19080 : ℝ) / n) := by
  classical
  rw [Measure.volume_eq_prod ℝ ℝ,
    Measure.prod_apply (measurableSet_fouvryG9WeightedObliqueStrip n h)]
  have hfun : (fun u : ℝ => volume (Prod.mk u ⁻¹' fouvryG9WeightedObliqueStrip n h)) =
      (Icc (4 / 53 : ℝ) (1 / 3)).indicator
        (fun _ => ENNReal.ofReal
          ((h + goldbachB9AlphaGridStep n + 2 * goldbachB9BetaGridStep n) / 2)) := by
    funext u
    rw [fouvryG9WeightedObliqueStrip_section]
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

theorem fouvryG9WeightedRegion_subset_ambient {n : ℕ} (hn : 0 < n) (h : ℝ) :
    fouvryG9WeightedRegion n h ⊆ goldbachB9LogAmbientBox := by
  intro x hx
  obtain ⟨q, _, hxq⟩ := Set.mem_iUnion₂.mp hx
  exact goldbachB9LogGridCell_subset_ambientBox hn q hxq

theorem fouvryG9WeightedRegion_excess_subset {n : ℕ} (hn : 0 < n) (h : ℝ) :
    fouvryG9WeightedRegion n h \ fouvryG9WeightedSource ⊆
      goldbachB9LeftStrip n ∪ goldbachB9BottomStrip n ∪
        fouvryG9WeightedObliqueStrip n h ∪ fouvryG9WeightedRightStrip n := by
  intro x hx
  obtain ⟨hg, hs⟩ := hx
  obtain ⟨q, hq, hxq⟩ := Set.mem_iUnion₂.mp hg
  have hb := goldbachB9LogGridCell_subset_ambientBox hn q hxq
  have ht := fouvryG9RelaxedIntegral_selected_cell_geometry q hq hxq.1 hxq.2
  by_cases hl : x.1 ≤ (4/53 : ℝ)
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

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
