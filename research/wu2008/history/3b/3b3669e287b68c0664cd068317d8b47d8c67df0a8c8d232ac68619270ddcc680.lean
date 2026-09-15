import W02Tail

noncomputable section
namespace WuTarget.W02
open Real Set NodeExtension
open scoped BigOperators

def gridIndices (j : Fin 21) : Finset ℕ :=
  Finset.Icc (max 3 (j.val + 1 - 9)) 29

def directNode (i : ℕ) (k : Fin 9) : ℝ :=
  if h : 2 ≤ i ∧ i ≤ 10 then nodeBasis k ⟨i - 2, by omega⟩ else 0

def sigmaNode (i : ℕ) : ℝ :=
  if 2 ≤ i ∧ i ≤ 10 then 0 else log (4 / (rNode i - 1))

def tailNode (i : ℕ) (k : Fin 9) : ℝ :=
  if 2 ≤ i ∧ i ≤ 10 then 0 else tailIntegral (rNode i) k

def paidNode (i : ℕ) (k : Fin 9) : ℝ :=
  if h : 2 ≤ i ∧ i ≤ 10 then nodeBasis k ⟨i - 2, by omega⟩
  else tailCell (rNode i) k

def directMatrix (j : Fin 21) (k : Fin 9) : ℝ :=
  nodeBasis k 0 * log (rNode (gridStart (j.val + 1)) / (rNode (j.val + 1) - 1)) +
    ∑ i ∈ gridIndices j, directNode i k * log (rNode i / rNode (i - 1))

def sigmaWeight (j : Fin 21) : ℝ :=
  ∑ i ∈ gridIndices j, sigmaNode i * log (rNode i / rNode (i - 1))

def tailMatrix (j : Fin 21) (k : Fin 9) : ℝ :=
  ∑ i ∈ gridIndices j, tailNode i k * log (rNode i / rNode (i - 1))

def rationalMatrix (j : Fin 21) (k : Fin 9) : ℝ :=
  nodeBasis k 0 * logLower (rNode (j.val + 1) - 1) (rNode (gridStart (j.val + 1))) +
    ∑ i ∈ gridIndices j, paidNode i k * logLower (rNode (i - 1)) (rNode i)

theorem grid_mem_bounds {j : Fin 21} {i : ℕ} (hi : i ∈ gridIndices j) :
    2 ≤ i ∧ i ≤ 29 := by
  have hh := Finset.mem_Icc.mp hi
  constructor <;> omega

theorem extended_bounds {i : ℕ} (hi : 2 ≤ i) (hi29 : i ≤ 29)
    (h : ¬ (2 ≤ i ∧ i ≤ 10)) : 3 ≤ rNode i ∧ rNode i ≤ 5 := by
  have hh := rNode_mono (show 10 ≤ i by omega)
  norm_num [rNode] at hh
  exact ⟨hh, (rNode_bounds hi29).2⟩

theorem extended_basis_decomposition {i : ℕ} (hi : 2 ≤ i) (hi29 : i ≤ 29) (k : Fin 9) :
    extendedNode (nodeBasis k) i =
      directNode i k + aProfile (nineProfile (nodeBasis k)) * sigmaNode i + tailNode i k := by
  by_cases h : 2 ≤ i ∧ i ≤ 10
  · simp [extendedNode, directNode, sigmaNode, tailNode, h]
  · have hb := extended_bounds hi hi29 h
    simp only [extendedNode, directNode, sigmaNode, tailNode, dif_neg h, if_neg h, zero_add]
    exact eProfile_basis_decomposition hb.1 hb.2 k

theorem transferMatrix_decomposition (j : Fin 21) (k : Fin 9) :
    transferMatrix j k =
      directMatrix j k + aProfile (nineProfile (nodeBasis k)) * sigmaWeight j + tailMatrix j k := by
  unfold transferMatrix originalTransfer directMatrix sigmaWeight tailMatrix
  change _ + (∑ i ∈ gridIndices j, _) = _
  have he : (∑ i ∈ gridIndices j, extendedNode (nodeBasis k) i *
      log (rNode i / rNode (i - 1))) =
      ∑ i ∈ gridIndices j,
        (directNode i k + aProfile (nineProfile (nodeBasis k)) * sigmaNode i + tailNode i k) *
          log (rNode i / rNode (i - 1)) := by
    apply Finset.sum_congr rfl
    intro i hit
    rw [extended_basis_decomposition (grid_mem_bounds hit).1 (grid_mem_bounds hit).2]
  rw [he]
  simp only [add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
  rfl

theorem paidNode_nonneg {i : ℕ} (hi : 2 ≤ i) (hi29 : i ≤ 29) (k : Fin 9) :
    0 ≤ paidNode i k := by
  unfold paidNode
  split_ifs with h
  · exact nodeBasis_nonneg k _
  · exact tailCell_nonneg (extended_bounds hi hi29 h).1 k

theorem paidNode_le_direct_tail {i : ℕ} (hi : 2 ≤ i) (hi29 : i ≤ 29) (k : Fin 9) :
    paidNode i k ≤ directNode i k + tailNode i k := by
  by_cases h : 2 ≤ i ∧ i ≤ 10
  · simp [paidNode, directNode, tailNode, h]
  · have hb := extended_bounds hi hi29 h
    simpa only [paidNode, directNode, tailNode, dif_neg h, if_neg h, zero_add,
      ← logMoment_basis_eq hb.1 hb.2] using tailCell_le_logMoment hb.1 hb.2 k

theorem sigmaWeight_nonneg (j : Fin 21) : 0 ≤ sigmaWeight j := by
  apply Finset.sum_nonneg
  intro i hit
  have hb := grid_mem_bounds hit
  apply mul_nonneg
  · unfold sigmaNode
    split_ifs with h
    · exact le_rfl
    · have he := extended_bounds hb.1 hb.2 h
      exact log_nonneg ((one_le_div (by linarith : 0 < rNode i - 1)).mpr (by linarith))
  · exact log_nonneg ((one_le_div (rNode_pos _)).mpr (rNode_mono (by omega)))

theorem rationalMatrix_nonneg (j : Fin 21) (k : Fin 9) : 0 ≤ rationalMatrix j k := by
  have hb := start_bounds (j := j.val + 1) (by omega) (by omega)
  apply add_nonneg
  · exact mul_nonneg (nodeBasis_nonneg k 0)
      (logLower_nonneg (by linarith : 0 < rNode (j.val + 1) - 1) hb.2.2.2)
  · apply Finset.sum_nonneg
    intro i hit
    exact mul_nonneg (paidNode_nonneg (grid_mem_bounds hit).1 (grid_mem_bounds hit).2 k)
      (logLower_nonneg (rNode_pos _) (rNode_mono (by omega)))

theorem rationalMatrix_le_direct_tail (j : Fin 21) (k : Fin 9) :
    rationalMatrix j k ≤ directMatrix j k + tailMatrix j k := by
  have hb := start_bounds (j := j.val + 1) (by omega) (by omega)
  unfold rationalMatrix directMatrix tailMatrix
  rw [add_assoc, ← Finset.sum_add_distrib]
  apply add_le_add
  · exact mul_le_mul_of_nonneg_left
      (logLower_le (by linarith : 0 < rNode (j.val + 1) - 1) hb.2.2.2) (nodeBasis_nonneg k 0)
  · apply Finset.sum_le_sum
    intro i hit
    rw [← add_mul]
    exact mul_le_mul (paidNode_le_direct_tail (grid_mem_bounds hit).1 (grid_mem_bounds hit).2 k)
      (logLower_le (rNode_pos _) (rNode_mono (by omega)))
      (logLower_nonneg (rNode_pos _) (rNode_mono (by omega)))
      ((paidNode_nonneg (grid_mem_bounds hit).1 (grid_mem_bounds hit).2 k).trans
        (paidNode_le_direct_tail (grid_mem_bounds hit).1 (grid_mem_bounds hit).2 k))

theorem rationalMatrix_lower_keeps_sigma (j : Fin 21) (k : Fin 9) :
    rationalMatrix j k + aProfile (nineProfile (nodeBasis k)) * sigmaWeight j ≤
      transferMatrix j k := by
  rw [transferMatrix_decomposition]
  linarith only [rationalMatrix_le_direct_tail j k]

theorem rationalMatrix_le_transferMatrix (j : Fin 21) (k : Fin 9) :
    rationalMatrix j k ≤ transferMatrix j k := by
  have ha := (profiles_nonneg (fun t _ => nineProfile_nonneg (nodeBasis_nonneg k) t)).1
  exact (le_add_of_nonneg_right (mul_nonneg ha (sigmaWeight_nonneg j))).trans
    (rationalMatrix_lower_keeps_sigma j k)

end WuTarget.W02
