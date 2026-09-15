import SrcGridFullIndex

namespace WuSource.SrcGrid
open Real Set MeasureTheory Wu2008DoubleSieve NodeExtension
open scoped Interval BigOperators

theorem initial_log_nonneg_all {j : ℕ} (hj : j ≤ 29) :
    0 ≤ log (rNode (gridStart j) / (rNode j - 1)) := by
  have hb := start_bounds_all hj
  exact log_nonneg ((le_div_iff₀ (by linarith [hb.2.2.1] : 0 < rNode j - 1)).2
    (by simpa only [one_mul] using hb.2.2.2))

theorem cell_log_nonneg (i : ℕ) :
    0 ≤ log (rNode i / rNode (i - 1)) :=
  log_nonneg ((le_div_iff₀ (rNode_pos (i - 1))).2
    (by simpa only [one_mul] using rNode_mono (show i - 1 ≤ i by omega)))

theorem originalTransfer_mono_all {z w : Fin 9 → ℝ} (hzw : ∀ k, z k ≤ w k)
    {j : ℕ} (hj : j ≤ 29) : originalTransfer z j ≤ originalTransfer w j := by
  unfold originalTransfer
  apply add_le_add
  · exact mul_le_mul_of_nonneg_right (hzw 0) (initial_log_nonneg_all hj)
  · apply Finset.sum_le_sum
    intro i hit
    have hh := Finset.mem_Icc.mp hit
    exact mul_le_mul_of_nonneg_right
      (WuTarget.W01Continuous.extendedNode_mono hzw (by omega) hh.2) (cell_log_nonneg i)

theorem originalTransfer_nonneg_all {z : Fin 9 → ℝ} (hz : ∀ k, 0 ≤ z k)
    {j : ℕ} (hj : j ≤ 29) : 0 ≤ originalTransfer z j := by
  by_cases hold : 1 ≤ j ∧ j ≤ 21
  · exact originalTransfer_nonneg hz hold.1 hold.2
  · apply add_nonneg
    · exact mul_nonneg (hz 0) (initial_log_nonneg_all hj)
    · apply Finset.sum_nonneg
      intro i hit
      have hh := Finset.mem_Icc.mp hit
      exact mul_nonneg (extendedNode_nonneg hz (by omega) hh.2) (cell_log_nonneg i)

theorem originalTransfer_antitone_all {z : Fin 9 → ℝ} (hz : ∀ k, 0 ≤ z k)
    {i j : ℕ} (hij : i ≤ j) (hj : j ≤ 29) :
    originalTransfer z j ≤ originalTransfer z i := by
  rw [← hContinuous_node_all z hj, ← hContinuous_node_all z (hij.trans hj)]
  exact WuTarget.W01Continuous.hContinuous_antitone hz (rNode_mono hij)

theorem upper_table_lower {δ : ℝ} (hd : 0 < δ) (hdhi : δ ≤ 1 / 10)
    {z : Fin 9 → ℝ} (hz : ∀ k, z k ≤ actualNine δ k)
    {i : ℕ} (hi : 2 ≤ i) (hi29 : i ≤ 29) :
    extendedNode z i ≤ wuImprovementLimit true δ (rNode i) :=
  (WuTarget.W01Continuous.extendedNode_mono hz hi hi29).trans
    (extendedNode_le_actual hd hdhi hi hi29)

theorem table_transfer_nat {δ : ℝ} (hd : 0 < δ) (hdhi : δ ≤ 1 / 10)
    {z : Fin 9 → ℝ} (hz : ∀ k, z k ≤ actualNine δ k)
    {j : ℕ} (hj : j ≤ 29) :
    originalTransfer z j ≤ wuImprovementLimit false δ (rNode j) :=
  (originalTransfer_mono_all hz hj).trans (actual_all_nat hd hdhi hj)

/-- A signed lower vector is sufficient for transfer; nonnegativity is not a hidden premise. -/
theorem full_tables_lower {δ : ℝ} (hd : 0 < δ) (hdhi : δ ≤ 1 / 10)
    {z : Fin 9 → ℝ} (hz : ∀ k, z k ≤ actualNine δ k) :
    (∀ i : ℕ, 2 ≤ i → i ≤ 29 →
      extendedNode z i ≤ wuImprovementLimit true δ (rNode i)) ∧
    (∀ j : ℕ, j ≤ 29 →
      originalTransfer z j ≤ wuImprovementLimit false δ (rNode j)) :=
  ⟨fun _ hi hi29 => upper_table_lower hd hdhi hz hi hi29,
    fun _ hj => table_transfer_nat hd hdhi hz hj⟩

theorem full_tables_nonneg {z : Fin 9 → ℝ} (hz : ∀ k, 0 ≤ z k) :
    (∀ i : ℕ, 2 ≤ i → i ≤ 29 → 0 ≤ extendedNode z i) ∧
    (∀ j : ℕ, j ≤ 29 → 0 ≤ originalTransfer z j) :=
  ⟨fun _ hi hi29 => extendedNode_nonneg hz hi hi29,
    fun _ hj => originalTransfer_nonneg_all hz hj⟩

theorem full_tables_mono {z w : Fin 9 → ℝ} (hzw : ∀ k, z k ≤ w k) :
    (∀ i : ℕ, 2 ≤ i → i ≤ 29 → extendedNode z i ≤ extendedNode w i) ∧
    (∀ j : ℕ, j ≤ 29 → originalTransfer z j ≤ originalTransfer w j) :=
  ⟨fun _ hi hi29 => WuTarget.W01Continuous.extendedNode_mono hzw hi hi29,
    fun _ hj => originalTransfer_mono_all hzw hj⟩

noncomputable def transferMatrix30 (j : Fin 30) (k : Fin 9) : ℝ :=
  originalTransfer (nodeBasis k) j.val

theorem transferMatrix30_nonneg (j : Fin 30) (k : Fin 9) :
    0 ≤ transferMatrix30 j k :=
  originalTransfer_nonneg_all (nodeBasis_nonneg k) (by omega)

theorem transferMatrix30_old (j : Fin 21) (k : Fin 9) :
    transferMatrix30 ⟨j.val + 1, by omega⟩ k = transferMatrix j k := rfl

theorem transferMatrix30_expansion (z : Fin 9 → ℝ) (j : Fin 30) :
    originalTransfer z j.val = ∑ k : Fin 9, transferMatrix30 j k * z k := by
  by_cases hold : 1 ≤ j.val ∧ j.val ≤ 21
  · have he := originalTransfer_expansion z ⟨j.val - 1, by omega⟩
    have hj : j.val - 1 + 1 = j.val := by omega
    simpa only [transferMatrix, transferMatrix30, hj] using he
  · classical
    simp only [transferMatrix30, originalTransfer]
    simp only [Finset.sum_mul, add_mul]
    rw [Finset.sum_add_distrib]
    congr 1
    · simp [nodeBasis, mul_comm]
    · rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hit
      have hh := Finset.mem_Icc.mp hit
      rw [extendedNode_expansion z (by omega) hh.2, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      ring

theorem transferMatrix30_lower {δ : ℝ} (hd : 0 < δ) (hdhi : δ ≤ 1 / 10)
    {z : Fin 9 → ℝ} (hz : ∀ k, z k ≤ actualNine δ k) (j : Fin 30) :
    (∑ k : Fin 9, transferMatrix30 j k * z k) ≤
      wuImprovementLimit false δ (rNode j.val) := by
  rw [← transferMatrix30_expansion]
  exact table_transfer_nat hd hdhi hz (by omega)

theorem transferMatrix30_mono {z w : Fin 9 → ℝ} (hzw : ∀ k, z k ≤ w k)
    (j : Fin 30) :
    (∑ k : Fin 9, transferMatrix30 j k * z k) ≤
      ∑ k : Fin 9, transferMatrix30 j k * w k :=
  Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_left (hzw k)
    (transferMatrix30_nonneg j k))

theorem transferMatrix30_antitone (k : Fin 9) :
    Antitone (fun j : Fin 30 => transferMatrix30 j k) := by
  intro i j hij
  exact originalTransfer_antitone_all (nodeBasis_nonneg k) hij (by omega)

theorem full_tables_uniform {z : Fin 9 → ℝ}
    (hz : ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 10 → ∀ k, z k ≤ actualNine δ k) :
    ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 10 →
      (∀ i : ℕ, 2 ≤ i → i ≤ 29 →
        extendedNode z i ≤ wuImprovementLimit true δ (rNode i)) ∧
      (∀ j : Fin 30, (∑ k : Fin 9, transferMatrix30 j k * z k) ≤
        wuImprovementLimit false δ (rNode j.val)) := by
  intro δ hd hdhi
  exact ⟨fun _ hi hi29 => upper_table_lower hd hdhi (hz δ hd hdhi) hi hi29,
    transferMatrix30_lower hd hdhi (hz δ hd hdhi)⟩

end WuSource.SrcGrid
