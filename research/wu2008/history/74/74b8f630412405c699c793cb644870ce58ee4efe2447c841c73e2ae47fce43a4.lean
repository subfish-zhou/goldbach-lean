import W01ContinuousProfile

noncomputable section
namespace WuTarget.W01Continuous
open Real Set MeasureTheory NodeExtension Wu2008DoubleSieve ActualNineFeedback
open scoped Classical BigOperators

theorem upperProfile_cell_integral (x : Fin 9 → ℝ) {i : ℕ}
    (hi : 3 ≤ i) (hi29 : i ≤ 29) :
    (∫ t in rNode (i-1)..rNode i, upperProfile x t/t) =
      extendedNode x i * log (rNode i / rNode (i-1)) := by
  have he : (∫ t in rNode (i-1)..rNode i, upperProfile x t/t) =
      ∫ t in rNode (i-1)..rNode i, extendedNode x i * (1/t) := by
    apply intervalIntegral.integral_congr_ae
    exact Filter.Eventually.of_forall (fun t ht => by
      rw [uIoc_of_le (rNode_mono (show i-1 ≤ i by omega))] at ht
      rw [upperProfile_cell x hi hi29 ht]
      ring)
  rw [he,intervalIntegral.integral_const_mul,
    integral_one_div_of_pos (rNode_pos _) (rNode_pos _)]

theorem upperProfile_initial_integral (x : Fin 9 → ℝ) {j : ℕ}
    (hj : 1 ≤ j) (hj21 : j ≤ 21) :
    (∫ t in (rNode j-1)..rNode (gridStart j), upperProfile x t/t) =
      x 0 * log (rNode (gridStart j)/(rNode j-1)) := by
  by_cases hlate : 12 ≤ j
  · rw [start_log_zero hlate,start_degenerate hlate]
    simp
  · have hs : gridStart j = 2 := by unfold gridStart; omega
    have hb := start_bounds hj hj21
    have he : (∫ t in (rNode j-1)..rNode (gridStart j), upperProfile x t/t) =
        ∫ t in (rNode j-1)..rNode (gridStart j), x 0 * (1/t) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le hb.2.2.2] at ht
      dsimp only
      rw [upperProfile_initial x ⟨hb.2.2.1.trans ht.1,by simpa only [hs] using ht.2⟩]
      ring
    rw [he,intervalIntegral.integral_const_mul,
      integral_one_div_of_pos (by linarith [hb.2.2.1]) (rNode_pos _)]

/-- Exact symbolic concatenation on the original upper grid, without evaluating a matrix cell. -/
theorem hContinuous_node_nat (x : Fin 9 → ℝ) {j : ℕ}
    (hj : 1 ≤ j) (hj21 : j ≤ 21) :
    hContinuous x (rNode j) = originalTransfer x j := by
  have hb := start_bounds hj hj21
  have hi := upperProfile_div_integrable x
  have hsum := grid_integral_sum (f := fun t => upperProfile x t/t)
    (show gridStart j ≤ 29 by omega)
    (fun _ _ _ => hi.intervalIntegrable)
  have he : (∑ i ∈ Finset.Icc (gridStart j+1) 29,
      ∫ t in rNode (i-1)..rNode i, upperProfile x t/t) =
      ∑ i ∈ Finset.Icc (gridStart j+1) 29,
        extendedNode x i * log (rNode i/rNode (i-1)) := by
    apply Finset.sum_congr rfl
    intro i hi
    exact upperProfile_cell_integral x (by have := (Finset.mem_Icc.mp hi).1; omega)
      (Finset.mem_Icc.mp hi).2
  have hjoin := intervalIntegral.integral_add_adjacent_intervals
    (hi.intervalIntegrable (a := rNode j-1) (b := rNode (gridStart j)))
    (hi.intervalIntegrable (a := rNode (gridStart j)) (b := rNode 29))
  rw [upperProfile_initial_integral x hj hj21,← hsum,he] at hjoin
  unfold hContinuous originalTransfer
  rw [← grid_start_index]
  exact hjoin.symm

theorem hContinuous_node (x : Fin 9 → ℝ) (j : Fin 21) :
    hContinuous x (rNode (j.val+1)) = matrixApply transferMatrix x j := by
  rw [hContinuous_node_nat x (by omega) (by omega),originalTransfer_expansion]
  rfl

theorem old_profile_le_continuous {x : Fin 9 → ℝ} (hx : ∀ i, 0 ≤ x i)
    {s : ℝ} (hs : s ∈ Icc 2 (41/10)) :
    DirectFiniteF6.profile (matrixApply transferMatrix x) s ≤ hContinuous x s := by
  apply StaircaseShrink.eval_le_of_nodes _ _ ((hContinuous_antitone hx).antitoneOn _) ?_
    hs le_rfl (hContinuous_nonneg hx hs.2)
  intro r hr
  refine ⟨DirectFiniteF6.row_endpoint _ hr,?_⟩
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp hr
  change matrixApply transferMatrix x j ≤ hContinuous x (originalRow j).2.1
  rw [originalRow_node,hContinuous_node]

end WuTarget.W01Continuous
