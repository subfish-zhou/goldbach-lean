import W02Transfer

noncomputable section
namespace WuTarget.E03Sigma
open Real NodeExtension
open scoped BigOperators

def logTerm (i : ℕ) : ℝ := (30 - (i : ℝ)) / (40 * (20 + (i : ℝ)))

theorem logTerm_le {i : ℕ} (hlo : 11 ≤ i) (hhi : i ≤ 29) :
    logTerm i ≤ W02.sigmaNode i * log (rNode i / rNode (i - 1)) := by
  have he := W02.extended_bounds (show 2 ≤ i by omega) hhi (by omega)
  have ha : 0 < rNode i - 1 := by linarith
  have hab : rNode i - 1 ≤ 4 := by linarith
  have hr : rNode (i - 1) ≤ rNode i := rNode_mono (by omega)
  have h1 := W02.logLower_le ha hab
  have h2 := W02.logLower_le (rNode_pos (i - 1)) hr
  have hn1 := W02.logLower_nonneg ha hab
  have hn2 := W02.logLower_nonneg (rNode_pos (i - 1)) hr
  have hm := mul_le_mul h1 h2 hn2 (hn1.trans h1)
  have hcast : ((i - 1 : ℕ) : ℝ) = (i : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  have hid : W02.logLower (rNode i - 1) 4 *
      W02.logLower (rNode (i - 1)) (rNode i) = logTerm i := by
    unfold W02.logLower rNode logTerm
    rw [hcast]
    field_simp
    ring
  simpa only [hid, W02.sigmaNode, if_neg (show ¬ (2 ≤ i ∧ i ≤ 10) by omega)] using hm

theorem sigmaTerm_nonneg {j : Fin 21} {i : ℕ} (hi : i ∈ W02.gridIndices j) :
    0 ≤ W02.sigmaNode i * log (rNode i / rNode (i - 1)) := by
  have hb := W02.grid_mem_bounds hi
  apply mul_nonneg
  · unfold W02.sigmaNode
    split_ifs with h
    · exact le_rfl
    · have he := W02.extended_bounds hb.1 hb.2 h
      exact log_nonneg ((one_le_div (by linarith : 0 < rNode i - 1)).mpr (by linarith))
  · exact log_nonneg ((one_le_div (rNode_pos _)).mpr (rNode_mono (by omega)))

def sigmaStart (j : Fin 21) : ℕ := if j.val < 20 then 11 else 12

def weightLower (j : Fin 21) : ℝ :=
  ∑ i ∈ Finset.Icc (sigmaStart j) 29, logTerm i

theorem weightLower_nonneg (j : Fin 21) : 0 ≤ weightLower j := by
  apply Finset.sum_nonneg
  intro i hi
  have hb := Finset.mem_Icc.mp hi
  have hhi : (i : ℝ) ≤ 29 := by exact_mod_cast hb.2
  exact div_nonneg (by linarith) (by positivity)

theorem weightLower_le (j : Fin 21) : weightLower j ≤ W02.sigmaWeight j := by
  have hsub : Finset.Icc (sigmaStart j) 29 ⊆ W02.gridIndices j := by
    intro i hi
    have hb := Finset.mem_Icc.mp hi
    apply Finset.mem_Icc.mpr
    unfold sigmaStart at hb
    split_ifs at hb <;> constructor <;> omega
  calc
    weightLower j ≤ ∑ i ∈ Finset.Icc (sigmaStart j) 29,
        W02.sigmaNode i * log (rNode i / rNode (i - 1)) := by
      apply Finset.sum_le_sum
      intro i hi
      have hb := Finset.mem_Icc.mp hi
      apply logTerm_le _ hb.2
      unfold sigmaStart at hb
      split_ifs at hb <;> omega
    _ ≤ W02.sigmaWeight j :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ hi _ => sigmaTerm_nonneg hi)

end WuTarget.E03Sigma
