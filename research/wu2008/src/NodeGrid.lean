import NodeStaircase

namespace NodeExtension
open Real Set MeasureTheory Wu2008DoubleSieve
open scoped Interval BigOperators

noncomputable def rNode (i : ℕ) : ℝ := 2 + (i : ℝ) / 10

def gridStart (j : ℕ) : ℕ := max 2 (j - 10)

noncomputable def extendedNode (z : Fin 9 → ℝ) (i : ℕ) : ℝ :=
  if h : 2 ≤ i ∧ i ≤ 10 then z ⟨i - 2, by omega⟩
  else eProfile (nineProfile z) (rNode i)

noncomputable def originalTransfer (z : Fin 9 → ℝ) (j : ℕ) : ℝ :=
  z 0 * log (rNode (max 2 (j - 10)) / (rNode j - 1)) +
    ∑ i ∈ Finset.Icc (max 3 (j - 9)) 29,
      extendedNode z i * log (rNode i / rNode (i - 1))

theorem grid_start_index (j : ℕ) : gridStart j + 1 = max 3 (j - 9) := by
  unfold gridStart
  omega

theorem rNode_mono : Monotone rNode := by
  intro i j hij
  have h : (i : ℝ) ≤ j := by exact_mod_cast hij
  dsimp [rNode]
  linarith

theorem rNode_pos (i : ℕ) : 0 < rNode i := by
  have h := Nat.cast_nonneg (α := ℝ) i
  dsimp [rNode]
  linarith

theorem start_bounds {j : ℕ} (hj : 1 ≤ j) (hj21 : j ≤ 21) :
    2 ≤ gridStart j ∧ gridStart j ≤ 11 ∧
      1 ≤ rNode j - 1 ∧ rNode j - 1 ≤ rNode (gridStart j) := by
  have hp := Nat.cast_nonneg (α := ℝ) j
  have hn : gridStart j ≤ 11 := by unfold gridStart; omega
  refine ⟨by unfold gridStart; omega, hn, ?_, ?_⟩
  · dsimp [rNode]; linarith
  · by_cases h : j ≤ 12
    · have hs : gridStart j = 2 := by unfold gridStart; omega
      have hc : (j : ℝ) ≤ 12 := by exact_mod_cast h
      rw [hs]; dsimp [rNode]; norm_num; linarith
    · have hs : gridStart j = j - 10 := by unfold gridStart; omega
      rw [hs, rNode, rNode, Nat.cast_sub (by omega : 10 ≤ j)]
      norm_num
      linarith

theorem start_degenerate {j : ℕ} (hj : 12 ≤ j) :
    rNode (gridStart j) = rNode j - 1 := by
  have hs : gridStart j = j - 10 := by unfold gridStart; omega
  rw [hs, rNode, rNode, Nat.cast_sub (by omega : 10 ≤ j)]
  norm_num
  ring

theorem start_log_zero {j : ℕ} (hj : 12 ≤ j) :
    log (rNode (gridStart j) / (rNode j - 1)) = 0 := by
  rw [← start_degenerate hj, div_self (ne_of_gt (rNode_pos _)), log_one]

theorem rNode_upperNode {i : ℕ} (hi : 2 ≤ i) (hi10 : i ≤ 10) :
    rNode i = upperNode ⟨i - 2, by omega⟩ := by
  dsimp [rNode, upperNode]
  rw [Nat.cast_sub hi]
  norm_num
  ring

theorem rNode_bounds {i : ℕ} (hi : i ≤ 29) : 1 ≤ rNode i ∧ rNode i ≤ 5 := by
  have h := rNode_mono hi
  have hp := rNode_pos i
  have hn := Nat.cast_nonneg (α := ℝ) i
  norm_num [rNode] at h ⊢
  constructor <;> linarith

theorem extendedNode_le_actual {δ : ℝ} (hd : 0 < δ) (hdhi : δ ≤ 1 / 10)
    {i : ℕ} (hi : 2 ≤ i) (hi29 : i ≤ 29) :
    extendedNode (actualNine δ) i ≤ wuImprovementLimit true δ (rNode i) := by
  unfold extendedNode
  split_ifs with h
  · rw [rNode_upperNode h.1 h.2]
    rfl
  · have hlo : 3 ≤ rNode i := by
      have hn : 10 ≤ i := by omega
      have hh := rNode_mono hn
      norm_num [rNode] at hh
      exact hh
    exact (actual_nine_extension hd hdhi).2.2.2 _ ⟨hlo, (rNode_bounds hi29).2⟩

theorem extendedNode_nonneg {z : Fin 9 → ℝ} (hz : ∀ k, 0 ≤ z k)
    {i : ℕ} (hi : 2 ≤ i) (hi29 : i ≤ 29) : 0 ≤ extendedNode z i := by
  unfold extendedNode
  split_ifs with h
  · exact hz _
  · have hlo : 3 ≤ rNode i := by
      have hh := rNode_mono (show 10 ≤ i by omega)
      norm_num [rNode] at hh
      exact hh
    exact (profiles_nonneg (fun t _ => nineProfile_nonneg hz t)).2.2 _
      ⟨hlo, (rNode_bounds hi29).2⟩

/-- Genuine finite integral concatenation on the original fixed grid. -/
theorem grid_integral_sum {f : ℝ → ℝ} {a n : ℕ} (han : a ≤ n)
    (hf : ∀ i, a ≤ i → i ≤ n → IntervalIntegrable f volume (rNode a) (rNode i)) :
    (∑ i ∈ Finset.Icc (a + 1) n, ∫ t in rNode (i - 1)..rNode i, f t) =
      ∫ t in rNode a..rNode n, f t := by
  induction n, han using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    rw [ih (fun i hi hin => hf i hi (by omega))]
    simp only [Nat.add_sub_cancel]
    exact intervalIntegral.integral_add_adjacent_intervals
      (hf n hn (by omega)) ((hf n hn (by omega)).symm.trans (hf (n + 1) (by omega) le_rfl))

end NodeExtension
