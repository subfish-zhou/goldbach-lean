import WR2XiSixthRationalH

noncomputable section
namespace WuPaper.R2Xi.SixthContinuous
open Real Set NodeExtension Finset SourceRational
open scoped Classical

def profileLeft (i : ℕ) : ℝ := if i = 2 then 1 else rNode (i-1)
def profileCell (i : ℕ) (s : ℝ) : ℝ :=
  upperLower i*lowerLogCell (profileLeft i) (rNode i) s

theorem profileLeft_pos (i : ℕ) : 0 < profileLeft i := by
  unfold profileLeft
  split_ifs
  · norm_num
  · exact rNode_pos _

theorem sum_Icc_head {k n : ℕ} (h : k ≤ n) (f : ℕ → ℝ) :
    (∑ i ∈ Icc k n, f i) = f k + ∑ i ∈ Icc (k+1) n, f i := by
  rw [← Finset.insert_Icc_succ_left_eq_Icc h,sum_insert]
  · rfl
  · simp

theorem pointLower_sum (s : ℝ) : pointLower s = ∑ i ∈ Icc 2 29, profileCell i s := by
  rw [sum_Icc_head (by omega : 2 ≤ 29)]
  rfl

/-- Only one clipped logarithm varies within each profile cell; the rest is a shared tail. -/
theorem partial_tail_le_pointLower {k : ℕ} {s T : ℝ}
    (hk : 2 ≤ k) (hk29 : k ≤ 29)
    (hs0 : profileLeft k ≤ s-1) (hs1 : s-1 ≤ rNode k)
    (hT : T ≤ ∑ i ∈ Icc (k+1) 29,
      upperLower i*SourceLogRational.lower (rNode i/rNode (i-1))) :
    upperLower k*SourceLogRational.lower (rNode k/(s-1))+T ≤ pointLower s := by
  rw [pointLower_sum]
  have hsub : (∑ i ∈ Icc k 29, profileCell i s) ≤ ∑ i ∈ Icc 2 29, profileCell i s := by
    apply sum_le_sum_of_subset_of_nonneg
    · exact Icc_subset_Icc_left hk
    · intro i _ _
      exact mul_nonneg (upperLower_nonneg _) (lowerLogCell_bounds (profileLeft_pos _)).1
  apply le_trans _ hsub
  rw [sum_Icc_head hk29]
  have he : profileCell k s = upperLower k*SourceLogRational.lower (rNode k/(s-1)) := by
    simp only [profileCell,lowerLogCell,max_eq_right hs0,if_pos hs1]
  rw [he]
  apply add_le_add_right
  apply hT.trans
  apply sum_le_sum
  intro i hi
  have hik : k+1 ≤ i := (mem_Icc.mp hi).1
  have hprev : s-1 ≤ rNode (i-1) := hs1.trans (rNode_mono (by omega))
  have hnode : rNode (i-1) ≤ rNode i := rNode_mono (by omega)
  have hn : i ≠ 2 := by omega
  simp only [profileCell,profileLeft,if_neg hn,lowerLogCell,max_eq_left hprev,if_pos hnode,le_refl]

end WuPaper.R2Xi.SixthContinuous
#print axioms WuPaper.R2Xi.SixthContinuous.partial_tail_le_pointLower
