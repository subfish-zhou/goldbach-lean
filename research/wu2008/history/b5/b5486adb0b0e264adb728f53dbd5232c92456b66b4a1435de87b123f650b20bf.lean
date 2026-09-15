import W01WeightedCount

noncomputable section
namespace WuTarget.W01Continuous
open Real Set MeasureTheory NodeExtension Wu2008DoubleSieve
open scoped Classical BigOperators

def upperProfile (x : Fin 9 → ℝ) (t : ℝ) : ℝ :=
  (Icc 1 (rNode 2)).indicator (fun _ => x 0) t +
    ∑ i ∈ Finset.Icc 3 29,
      (Ioc (rNode (i-1)) (rNode i)).indicator (fun _ => extendedNode x i) t

def hContinuous (x : Fin 9 → ℝ) (s : ℝ) : ℝ :=
  ∫ t in (s-1)..rNode 29, upperProfile x t / t

theorem rNode_strictMono : StrictMono rNode := by
  intro i j hij
  have h : (i : ℝ) < j := by exact_mod_cast hij
  dsimp [rNode]
  linarith

theorem extendedNode_mono {x y : Fin 9 → ℝ} (hxy : ∀ k, x k ≤ y k)
    {i : ℕ} (hi : 2 ≤ i) (hi29 : i ≤ 29) :
    extendedNode x i ≤ extendedNode y i := by
  rw [extendedNode_expansion x hi hi29, extendedNode_expansion y hi hi29]
  exact Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_right (hxy k)
    (extendedNode_nonneg (nodeBasis_nonneg k) hi hi29))

theorem upper_cells_unique {i j : ℕ} {t : ℝ}
    (hi : t ∈ Ioc (rNode (i-1)) (rNode i))
    (hj : t ∈ Ioc (rNode (j-1)) (rNode j)) : i = j := by
  by_contra h
  rcases lt_or_gt_of_ne h with hij | hji
  · have hm := rNode_mono (show i ≤ j-1 by omega)
    linarith [hi.2,hj.1]
  · have hm := rNode_mono (show j ≤ i-1 by omega)
    linarith [hj.2,hi.1]

theorem upperProfile_initial (x : Fin 9 → ℝ) {t : ℝ}
    (ht : t ∈ Icc 1 (rNode 2)) : upperProfile x t = x 0 := by
  unfold upperProfile
  rw [indicator_of_mem ht]
  have hz : (∑ i ∈ Finset.Icc 3 29,
      (Ioc (rNode (i-1)) (rNode i)).indicator (fun _ => extendedNode x i) t) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    apply indicator_of_notMem
    intro h
    have hm := rNode_mono (show 2 ≤ i-1 by have := (Finset.mem_Icc.mp hi).1; omega)
    linarith [ht.2,h.1]
  rw [hz,add_zero]

theorem upperProfile_cell (x : Fin 9 → ℝ) {i : ℕ} {t : ℝ}
    (hi : 3 ≤ i) (hi29 : i ≤ 29)
    (ht : t ∈ Ioc (rNode (i-1)) (rNode i)) :
    upperProfile x t = extendedNode x i := by
  unfold upperProfile
  have hnot : t ∉ Icc 1 (rNode 2) := by
    intro h
    have hm := rNode_mono (show 2 ≤ i-1 by omega)
    linarith [h.2,ht.1]
  rw [indicator_of_notMem hnot,zero_add,Finset.sum_eq_single i]
  · exact indicator_of_mem ht _
  · intro j _ hji
    exact indicator_of_notMem (fun hj => hji (upper_cells_unique hj ht)) _
  · simp only [Finset.mem_Icc,hi,hi29,and_self,not_true_eq_false,IsEmpty.forall_iff]

theorem upperProfile_nonneg {x : Fin 9 → ℝ} (hx : ∀ i, 0 ≤ x i) (t : ℝ) :
    0 ≤ upperProfile x t := by
  apply add_nonneg (indicator_nonneg (fun _ _ => hx 0) t)
  apply Finset.sum_nonneg
  intro i hi
  exact indicator_nonneg (fun _ _ =>
    extendedNode_nonneg hx (by have := (Finset.mem_Icc.mp hi).1; omega)
      (Finset.mem_Icc.mp hi).2) t

theorem upperProfile_zero_outside (x : Fin 9 → ℝ) {t : ℝ}
    (ht : t ∉ Icc 1 (rNode 29)) : upperProfile x t = 0 := by
  unfold upperProfile
  rw [indicator_of_notMem (fun h => ht ⟨h.1,h.2.trans (rNode_mono (by omega))⟩)]
  rw [zero_add]
  apply Finset.sum_eq_zero
  intro i hi
  apply indicator_of_notMem
  intro h
  exact ht ⟨(rNode_bounds (show i-1 ≤ 29 by have := (Finset.mem_Icc.mp hi).2; omega)).1.trans h.1.le,
    h.2.trans (rNode_mono (Finset.mem_Icc.mp hi).2)⟩

theorem upperProfile_le_actual {x : Fin 9 → ℝ} {δ t : ℝ}
    (hδ : 0 < δ) (hd : δ ≤ 1/10) (hx : ∀ i, x i ≤ actualNine δ i)
    (ht : t ∈ Icc 1 5) :
    upperProfile x t ≤ wuImprovementLimit true δ t := by
  by_cases hfirst : t ∈ Icc 1 (rNode 2)
  · rw [upperProfile_initial x hfirst]
    exact (hx 0).trans (wuImprovementLimit_upper_antitone hδ hd
      ⟨ht.1,ht.2.trans (by norm_num)⟩
      ⟨(upperNode_bounds 0).1,(upperNode_bounds 0).2.trans (by norm_num)⟩
      (by have h := hfirst.2; norm_num [upperNode,rNode] at h ⊢; exact h))
  · by_cases he : ∃ i ∈ Finset.Icc 3 29, t ∈ Ioc (rNode (i-1)) (rNode i)
    · obtain ⟨i,hi,hcell⟩ := he
      have hi' := Finset.mem_Icc.mp hi
      rw [upperProfile_cell x hi'.1 hi'.2 hcell]
      exact ((extendedNode_mono hx (by omega) hi'.2).trans
        (extendedNode_le_actual hδ hd (by omega) hi'.2)).trans
        (wuImprovementLimit_upper_antitone hδ hd
          ⟨ht.1,ht.2.trans (by norm_num)⟩
          ⟨(rNode_bounds hi'.2).1,(rNode_bounds hi'.2).2.trans (by norm_num)⟩ hcell.2)
    · have hz : upperProfile x t = 0 := by
        unfold upperProfile
        rw [indicator_of_notMem hfirst,zero_add]
        exact Finset.sum_eq_zero (fun i hi => indicator_of_notMem (fun h => he ⟨i,hi,h⟩) _)
      rw [hz]
      exact wuImprovementLimit_nonneg true hδ (by linarith) ht.1 (ht.2.trans (by norm_num))

theorem upperProfile_div_integrable (x : Fin 9 → ℝ) :
    Integrable (fun t => upperProfile x t / t) := by
  have hc (a b c : ℝ) (ha : 0 < a) :
      IntegrableOn (fun t : ℝ => c/t) (Icc a b) := by
    apply ContinuousOn.integrableOn_Icc
    exact continuousOn_const.div continuousOn_id (fun t ht => ne_of_gt (ha.trans_le ht.1))
  have he : (fun t => upperProfile x t / t) =
      (Icc 1 (rNode 2)).indicator (fun t => x 0 / t) +
        ∑ i ∈ Finset.Icc 3 29,
          (Ioc (rNode (i-1)) (rNode i)).indicator (fun t => extendedNode x i / t) := by
    funext t
    simp only [upperProfile,add_div,Finset.sum_div,Pi.add_apply,Finset.sum_apply]
    congr 1
    · by_cases ht : t ∈ Icc 1 (rNode 2) <;> simp [ht]
    · apply Finset.sum_congr rfl
      intro i _
      by_cases ht : t ∈ Ioc (rNode (i-1)) (rNode i) <;> simp [ht]
  rw [he]
  apply Integrable.add
  · exact (integrable_indicator_iff measurableSet_Icc).mpr (hc _ _ _ (by norm_num))
  · have hsum : (∑ i ∈ Finset.Icc 3 29,
        (Ioc (rNode (i-1)) (rNode i)).indicator (fun t => extendedNode x i / t)) =
        fun t => ∑ i ∈ Finset.Icc 3 29,
          (Ioc (rNode (i-1)) (rNode i)).indicator (fun t => extendedNode x i / t) t := by
      funext t
      simp only [Finset.sum_apply]
    rw [hsum]
    apply integrable_finsetSum
    intro i _
    exact (integrable_indicator_iff measurableSet_Ioc).mpr
      ((hc _ _ _ (rNode_pos _)).mono_set Ioc_subset_Icc_self)

theorem upperProfile_div_nonneg {x : Fin 9 → ℝ} (hx : ∀ i, 0 ≤ x i) (t : ℝ) :
    0 ≤ upperProfile x t / t := by
  by_cases ht : t ∈ Icc 1 (rNode 29)
  · exact div_nonneg (upperProfile_nonneg hx t) (by linarith [ht.1])
  · rw [upperProfile_zero_outside x ht,zero_div]

theorem hContinuous_continuous (x : Fin 9 → ℝ) : Continuous (hContinuous x) := by
  have hc := (intervalIntegral.continuous_primitive
    (fun _ _ => (upperProfile_div_integrable x).intervalIntegrable) (rNode 29)).neg
  have he : hContinuous x = fun s => -(∫ t in rNode 29..(s-1), upperProfile x t/t) := by
    funext s
    exact intervalIntegral.integral_symm _ _
  rw [he]
  exact hc.comp (continuous_id.sub continuous_const)

theorem hContinuous_antitone {x : Fin 9 → ℝ} (hx : ∀ i, 0 ≤ x i) :
    Antitone (hContinuous x) := by
  intro a b hab
  have hi := upperProfile_div_integrable x
  have hj := intervalIntegral.integral_add_adjacent_intervals
    (hi.intervalIntegrable (a := a-1) (b := b-1))
    (hi.intervalIntegrable (a := b-1) (b := rNode 29))
  have hn := intervalIntegral.integral_nonneg (μ := volume) (show a-1 ≤ b-1 by linarith)
    (fun t _ => upperProfile_div_nonneg hx t)
  dsimp [hContinuous]
  linarith only [hj,hn]

theorem hContinuous_nonneg {x : Fin 9 → ℝ} (hx : ∀ i, 0 ≤ x i)
    {s : ℝ} (hs : s ≤ 41/10) : 0 ≤ hContinuous x s := by
  apply intervalIntegral.integral_nonneg (show s-1 ≤ rNode 29 by norm_num [rNode]; linarith)
  exact fun t _ => upperProfile_div_nonneg hx t

theorem hContinuous_le_actual {x : Fin 9 → ℝ} {δ s : ℝ}
    (hδ : 0 < δ) (hd : δ ≤ 1/10) (hx : ∀ i, x i ≤ actualNine δ i)
    (hs : s ∈ Icc 2 (41/10)) :
    hContinuous x s ≤ wuImprovementLimit false δ s := by
  have hr : rNode 29 ≤ (5:ℝ) := (rNode_bounds (i := 29) le_rfl).2
  have hs1 : 1 ≤ s-1 := by linarith [hs.1]
  have hsr : s-1 ≤ rNode 29 := by norm_num [rNode]; linarith [hs.2]
  have hi := wuImprovementLimit_div_intervalIntegrable true hδ (by linarith)
    hs1 hsr (hr.trans (by norm_num))
  have hm := intervalIntegral.integral_mono_on hsr
    (upperProfile_div_integrable x).intervalIntegrable hi (fun t ht =>
      div_le_div_of_nonneg_right
        (upperProfile_le_actual hδ hd hx ⟨hs1.trans ht.1,ht.2.trans hr⟩)
        (by linarith [ht.1]))
  have hit := wuImprovementLimit_div_intervalIntegrable true hδ (by linarith)
    (rNode_bounds (i := 29) le_rfl).1 hr (by norm_num : (5:ℝ) ≤ 10)
  have hj := intervalIntegral.integral_add_adjacent_intervals hi hit
  have hn : 0 ≤ ∫ t in rNode 29..5, wuImprovementLimit true δ t/t := by
    apply intervalIntegral.integral_nonneg hr
    intro t ht
    exact div_nonneg
      (wuImprovementLimit_nonneg true hδ (by linarith)
        ((rNode_bounds (i := 29) le_rfl).1.trans ht.1) (ht.2.trans (by norm_num)))
      (by have := (rNode_bounds (i := 29) le_rfl).1; linarith [ht.1])
  have hc := wuImprovementLimit_lower_cross hδ hd (s := s) (t := 6)
    hs.1 (by linarith [hs.2]) (by norm_num)
  have h6 := wuImprovementLimit_nonneg false hδ (by linarith)
    (s := 6) (by norm_num) (by norm_num)
  norm_num at hc
  change hContinuous x s ≤ _ at hm
  linarith only [hm,hj,hn,hc,h6]

end WuTarget.W01Continuous
