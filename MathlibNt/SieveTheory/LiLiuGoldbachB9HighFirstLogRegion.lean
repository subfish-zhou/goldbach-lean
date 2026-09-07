import MathlibNt.SieveTheory.LiLiuGoldbachB9HighFirstLogGrid

open MeasureTheory Set
open scoped BigOperators Interval

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

open MathlibNt.SieveTheory.LiuWeight
open PrimeReciprocalLogRectangle

noncomputable section

def goldbachB9HighLogGridRegion (n : ℕ) : Set (ℝ × ℝ) :=
  ⋃ q ∈ goldbachB9HighLogGridCells n, goldbachB9LogGridCell n q

def goldbachB9HighLogSourceRegion : Set (ℝ × ℝ) :=
  {x | x.1 ∈ Ioc (1 / 10) (1 / 3) ∧ x.2 ∈ Ioc (1 / 3) ((1 - x.1) / 2)}

def goldbachB9HighLeftStrip (n : ℕ) : Set (ℝ × ℝ) :=
  Ioc (1 / 10 - goldbachB9AlphaGridStep n) (1 / 10) ×ˢ Icc (1 / 4) (1 / 2)

def goldbachB9HighBottomStrip (n : ℕ) : Set (ℝ × ℝ) :=
  Icc (1 / 10) (1 / 3) ×ˢ Ioc (1 / 3 - goldbachB9BetaGridStep n) (1 / 3)

def goldbachB9HighObliqueStrip (n : ℕ) : Set (ℝ × ℝ) :=
  {x | x.1 ∈ Icc (1 / 10) (1 / 3) ∧
    (1 - x.1) / 2 < x.2 ∧
    x.2 < (1 - x.1) / 2 +
      (goldbachB9AlphaGridStep n + 2 * goldbachB9BetaGridStep n) / 2}

def goldbachB9HighLogGridUpperIntegrand (n : ℕ) (x : ℝ × ℝ) : ℝ :=
  ∑ q ∈ goldbachB9HighLogGridCells n,
    (1 / (1 - goldbachB9AlphaGridPoint n (q.1 + 1) -
      goldbachB9BetaGridPoint n (q.2 + 1))) *
      (goldbachB9LogGridCell n q).indicator liuLogDensity x

theorem measurableSet_goldbachB9HighLogGridRegion (n : ℕ) :
    MeasurableSet (goldbachB9HighLogGridRegion n) := by
  classical
  exact Finset.measurableSet_biUnion _ fun q _ => measurableSet_goldbachB9LogGridCell n q

theorem measurableSet_goldbachB9HighLogSourceRegion :
    MeasurableSet goldbachB9HighLogSourceRegion := by
  exact (measurableSet_Ioc.preimage measurable_fst).inter
    ((measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd (by fun_prop)))

theorem measurableSet_goldbachB9HighLeftStrip (n : ℕ) :
    MeasurableSet (goldbachB9HighLeftStrip n) :=
  measurableSet_Ioc.prod measurableSet_Icc

theorem measurableSet_goldbachB9HighBottomStrip (n : ℕ) :
    MeasurableSet (goldbachB9HighBottomStrip n) :=
  measurableSet_Icc.prod measurableSet_Ioc

theorem measurableSet_goldbachB9HighObliqueStrip (n : ℕ) :
    MeasurableSet (goldbachB9HighObliqueStrip n) := by
  exact (measurableSet_Icc.preimage measurable_fst).inter
    ((measurableSet_lt (by fun_prop) measurable_snd).inter
      (measurableSet_lt measurable_snd (by fun_prop)))

theorem goldbachB9HighLogGridRegion_subset_full (n : ℕ) :
    goldbachB9HighLogGridRegion n ⊆ goldbachB9LogGridRegion n := by
  intro x hx
  obtain ⟨q, hq, hxq⟩ := Set.mem_iUnion₂.mp hx
  exact Set.mem_iUnion₂.mpr ⟨q, goldbachB9HighLogGridCells_subset n hq, hxq⟩

theorem goldbachB9HighLogGridRegion_subset_ambientBox {n : ℕ} (hn : 0 < n) :
    goldbachB9HighLogGridRegion n ⊆ goldbachB9LogAmbientBox :=
  (goldbachB9HighLogGridRegion_subset_full n).trans
    (goldbachB9LogGridRegion_subset_ambientBox hn)

theorem goldbachB9HighLogSourceRegion_subset_ambientBox :
    goldbachB9HighLogSourceRegion ⊆ goldbachB9LogAmbientBox := by
  intro x hx
  exact ⟨⟨by linarith [hx.1.1], hx.1.2⟩,
    ⟨by linarith [hx.2.1], by linarith [hx.1.1, hx.2.2]⟩⟩

theorem goldbachB9HighLogSourceRegion_subset_gridRegion {n : ℕ} (hn : 0 < n) :
    goldbachB9HighLogSourceRegion ⊆ goldbachB9HighLogGridRegion n := by
  intro x hx
  have halow : (1 / 20 : ℝ) < x.1 := by linarith [hx.1.1]
  have hblow : (1 / 4 : ℝ) < x.2 := by linarith [hx.2.1]
  have haup : x.1 ≤ 1 / 20 + (n : ℝ) * goldbachB9AlphaGridStep n := by
    rw [← goldbachB9AlphaGridPoint_eq_step, goldbachB9AlphaGridPoint_end hn]
    exact hx.1.2
  have hbup : x.2 ≤ 1 / 4 + (n : ℝ) * goldbachB9BetaGridStep n := by
    rw [← goldbachB9BetaGridPoint_eq_step, goldbachB9BetaGridPoint_end hn]
    linarith [hx.1.1, hx.2.2]
  obtain ⟨i, hi, hail, haiu⟩ :=
    exists_nat_cell n (goldbachB9AlphaGridStep_pos hn) halow haup
  obtain ⟨j, hj, hbjl, hbju⟩ :=
    exists_nat_cell n (goldbachB9BetaGridStep_pos hn) hblow hbup
  have hal : goldbachB9AlphaGridPoint n i < x.1 := by
    simpa only [goldbachB9AlphaGridPoint_eq_step] using hail
  have hau : x.1 ≤ goldbachB9AlphaGridPoint n (i + 1) := by
    simpa only [goldbachB9AlphaGridPoint_eq_step] using haiu
  have hbl : goldbachB9BetaGridPoint n j < x.2 := by
    simpa only [goldbachB9BetaGridPoint_eq_step] using hbjl
  have hbu : x.2 ≤ goldbachB9BetaGridPoint n (j + 1) := by
    simpa only [goldbachB9BetaGridPoint_eq_step] using hbju
  apply Set.mem_iUnion₂.mpr
  refine ⟨(⟨i, hi⟩, ⟨j, hj⟩), mem_goldbachB9HighLogGridCells_iff.mpr ?_, ?_⟩
  · exact ⟨hx.1.1.le.trans hau, hx.2.1.le.trans hbu, by
      dsimp
      linarith [hx.2.2]⟩
  · exact ⟨⟨hal, hau⟩, ⟨hbl, hbu⟩⟩

theorem goldbachB9HighLogGridRegion_excess_subset {n : ℕ} (hn : 0 < n) :
    goldbachB9HighLogGridRegion n \ goldbachB9HighLogSourceRegion ⊆
      goldbachB9HighLeftStrip n ∪ goldbachB9HighBottomStrip n ∪
        goldbachB9HighObliqueStrip n := by
  intro x hx
  obtain ⟨hg, hs⟩ := hx
  obtain ⟨q, hq, hxq⟩ := Set.mem_iUnion₂.mp hg
  have hb := goldbachB9LogGridCell_subset_ambientBox hn q hxq
  have hsel := mem_goldbachB9HighLogGridCells_iff.mp hq
  change
    x.1 ∈ Ioc (goldbachB9AlphaGridPoint n q.1) (goldbachB9AlphaGridPoint n (q.1 + 1)) ∧
      x.2 ∈ Ioc (goldbachB9BetaGridPoint n q.2) (goldbachB9BetaGridPoint n (q.2 + 1))
    at hxq
  rw [goldbachB9AlphaGridPoint_succ, goldbachB9BetaGridPoint_succ] at hxq hsel
  by_cases hl : x.1 ≤ (1 / 10 : ℝ)
  · apply Or.inl ∘ Or.inl
    exact ⟨⟨by linarith [hxq.1.1, hsel.1], hl⟩, hb.2⟩
  · have hl' : (1 / 10 : ℝ) < x.1 := lt_of_not_ge hl
    by_cases hd : x.2 ≤ (1 / 3 : ℝ)
    · apply Or.inl ∘ Or.inr
      exact ⟨⟨hl'.le, hb.1.2⟩, ⟨by linarith [hxq.2.1, hsel.2.1], hd⟩⟩
    · apply Or.inr
      have hu : (1 - x.1) / 2 < x.2 := by
        by_contra h
        exact hs ⟨⟨hl', hb.1.2⟩, ⟨lt_of_not_ge hd, le_of_not_gt h⟩⟩
      exact ⟨⟨hl'.le, hb.1.2⟩, hu, by linarith [hxq.1.2, hxq.2.2, hsel.2.2]⟩

theorem volume_goldbachB9HighLeftStrip (n : ℕ) :
    volume (goldbachB9HighLeftStrip n) = ENNReal.ofReal ((17 / 240 : ℝ) / n) := by
  unfold goldbachB9HighLeftStrip
  rw [Measure.volume_eq_prod ℝ ℝ, Measure.prod_prod, Real.volume_Ioc, Real.volume_Icc]
  have hlen : (1 / 10 : ℝ) - (1 / 10 - goldbachB9AlphaGridStep n) =
      goldbachB9AlphaGridStep n := by ring
  rw [hlen, ← ENNReal.ofReal_mul (by
    unfold goldbachB9AlphaGridStep goldbachB9AlphaGridWidth
    positivity)]
  congr 1
  unfold goldbachB9AlphaGridStep goldbachB9AlphaGridWidth
  ring

theorem volume_goldbachB9HighBottomStrip (n : ℕ) :
    volume (goldbachB9HighBottomStrip n) =
      ENNReal.ofReal (((1 / 3 : ℝ) - 1 / 10) * goldbachB9BetaGridStep n) := by
  unfold goldbachB9HighBottomStrip
  rw [Measure.volume_eq_prod ℝ ℝ, Measure.prod_prod, Real.volume_Icc, Real.volume_Ioc,
    ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 3 - 1 / 10)]
  congr 1
  ring

theorem goldbachB9HighObliqueStrip_section (n : ℕ) (u : ℝ) :
    Prod.mk u ⁻¹' goldbachB9HighObliqueStrip n =
      if u ∈ Icc (1 / 10 : ℝ) (1 / 3) then
        Ioo ((1 - u) / 2) ((1 - u) / 2 +
          (goldbachB9AlphaGridStep n + 2 * goldbachB9BetaGridStep n) / 2) else ∅ := by
  classical
  ext v
  simp [goldbachB9HighObliqueStrip, and_assoc]

theorem volume_goldbachB9HighObliqueStrip (n : ℕ) :
    volume (goldbachB9HighObliqueStrip n) =
      ENNReal.ofReal (((1 / 3 : ℝ) - 1 / 10) *
        (goldbachB9AlphaGridStep n + 2 * goldbachB9BetaGridStep n) / 2) := by
  classical
  rw [Measure.volume_eq_prod ℝ ℝ,
    Measure.prod_apply (measurableSet_goldbachB9HighObliqueStrip n)]
  have hfun : (fun u : ℝ => volume (Prod.mk u ⁻¹' goldbachB9HighObliqueStrip n)) =
      (Icc (1 / 10 : ℝ) (1 / 3)).indicator
        (fun _ => ENNReal.ofReal
          ((goldbachB9AlphaGridStep n + 2 * goldbachB9BetaGridStep n) / 2)) := by
    funext u
    rw [goldbachB9HighObliqueStrip_section]
    by_cases hu : u ∈ Icc (1 / 10 : ℝ) (1 / 3)
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
  ring

theorem integrable_goldbachB9HighSourceIndicator :
    Integrable (goldbachB9HighLogSourceRegion.indicator liuLogIntegrand) :=
  integrable_indicator_of_integrableOn measurableSet_goldbachB9HighLogSourceRegion
    (integrableOn_goldbachB9LogIntegrand measurableSet_goldbachB9HighLogSourceRegion
      goldbachB9HighLogSourceRegion_subset_ambientBox)

theorem integrable_goldbachB9HighLogGridUpperIntegrand (n : ℕ) (hn : 0 < n) :
    Integrable (goldbachB9HighLogGridUpperIntegrand n) := by
  classical
  exact integrable_finsetSum _ fun q _ =>
    (integrable_indicator_of_integrableOn (measurableSet_goldbachB9LogGridCell n q)
      (integrableOn_goldbachB9LogDensity (measurableSet_goldbachB9LogGridCell n q)
        (goldbachB9LogGridCell_subset_ambientBox hn q))).const_mul _

theorem goldbachB9HighLogGridUpperSum_eq_integral (n : ℕ) (hn : 0 < n) :
    goldbachB9HighLogGridUpperSum n = ∫ x, goldbachB9HighLogGridUpperIntegrand n x := by
  classical
  unfold goldbachB9HighLogGridUpperSum goldbachB9HighLogGridUpperIntegrand
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro q _
    rw [integral_const_mul, integral_indicator (measurableSet_goldbachB9LogGridCell n q),
      logarithmicRectangleMass_eq_setIntegral
        (goldbachB9AlphaGridPoint_pos n q.1) (goldbachB9AlphaGridPoint_lt_succ hn)
        (goldbachB9BetaGridPoint_pos n q.2) (goldbachB9BetaGridPoint_lt_succ hn)]
    rfl
  · intro q _
    exact (integrable_indicator_of_integrableOn (measurableSet_goldbachB9LogGridCell n q)
      (integrableOn_goldbachB9LogDensity (measurableSet_goldbachB9LogGridCell n q)
        (goldbachB9LogGridCell_subset_ambientBox hn q))).const_mul _

theorem goldbachB9HighLogGridUpperIntegrand_eq_of_mem {n : ℕ} (hn : 0 < n)
    {q : Fin n × Fin n} (hq : q ∈ goldbachB9HighLogGridCells n)
    {x : ℝ × ℝ} (hx : x ∈ goldbachB9LogGridCell n q) :
    goldbachB9HighLogGridUpperIntegrand n x =
      (1 / (1 - goldbachB9AlphaGridPoint n (q.1 + 1) -
        goldbachB9BetaGridPoint n (q.2 + 1))) * liuLogDensity x := by
  classical
  unfold goldbachB9HighLogGridUpperIntegrand
  rw [Finset.sum_eq_single q]
  · rw [indicator_of_mem hx]
  · intro r _ hrq
    have hnot : x ∉ goldbachB9LogGridCell n r := fun hxr =>
      Set.disjoint_left.mp
        (goldbachB9LogGridCell_pairwiseDisjoint hn (Set.mem_univ q) (Set.mem_univ r)
          hrq.symm) hx hxr
    rw [indicator_of_notMem hnot, mul_zero]
  · exact fun h => (h hq).elim

theorem goldbachB9HighLogGridUpperIntegrand_eq_zero {n : ℕ} {x : ℝ × ℝ}
    (hx : x ∉ goldbachB9HighLogGridRegion n) :
    goldbachB9HighLogGridUpperIntegrand n x = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro q hq
  have hnot : x ∉ goldbachB9LogGridCell n q :=
    fun h => hx (Set.mem_iUnion₂.mpr ⟨q, hq, h⟩)
  rw [indicator_of_notMem hnot, mul_zero]

/-- Equality only on selected cells lets us reuse the produced corner estimates. -/
theorem goldbachB9HighLogGridUpperIntegrand_eq_full_of_mem {n : ℕ} (hn : 0 < n)
    {x : ℝ × ℝ} (hx : x ∈ goldbachB9HighLogGridRegion n) :
    goldbachB9HighLogGridUpperIntegrand n x = goldbachB9LogGridUpperIntegrand n x := by
  obtain ⟨q, hq, hxq⟩ := Set.mem_iUnion₂.mp hx
  rw [goldbachB9HighLogGridUpperIntegrand_eq_of_mem hn hq hxq,
    goldbachB9LogGridUpperIntegrand_eq_of_mem hn (goldbachB9HighLogGridCells_subset n hq) hxq]

theorem goldbachB9HighLogGridUpperIntegrand_le {n : ℕ} (hn : 0 < n)
    {x : ℝ × ℝ} (hx : x ∈ goldbachB9HighLogGridRegion n) :
    goldbachB9HighLogGridUpperIntegrand n x ≤ 480 := by
  rw [goldbachB9HighLogGridUpperIntegrand_eq_full_of_mem hn hx]
  exact goldbachB9LogGridUpperIntegrand_le hn (goldbachB9HighLogGridRegion_subset_full n hx)

theorem goldbachB9HighLogGridUpperIntegrand_le_integrand_add {n : ℕ} (hn : 0 < n)
    {x : ℝ × ℝ} (hx : x ∈ goldbachB9HighLogGridRegion n) :
    goldbachB9HighLogGridUpperIntegrand n x ≤ liuLogIntegrand x + 1600 / (n : ℝ) := by
  rw [goldbachB9HighLogGridUpperIntegrand_eq_full_of_mem hn hx]
  exact goldbachB9LogGridUpperIntegrand_le_integrand_add hn
    (goldbachB9HighLogGridRegion_subset_full n hx)

end

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig