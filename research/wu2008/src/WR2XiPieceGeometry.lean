import WR2XiPieces
import WR2XiUniformPanels

/-! Explicit original support bounds for clipped uniform panel certificates. -/
noncomputable section
namespace WuPaper.R2Xi
open Real Set Wu2008DoubleSieve MotherPair SecondFunctionalParameters NodeExtension
open WuPaper.RMapMMatrix

theorem original_piece_support_bounds (r : Fin 4) (j : Fin 9) :
    1 ≤ (xi2PieceInterval (gamma5OriginalRow r) j).1 ∧
    (xi2PieceInterval (gamma5OriginalRow r) j).1 ≤ (xi2PieceInterval (gamma5OriginalRow r) j).2 ∧
    (xi2PieceInterval (gamma5OriginalRow r) j).2 ≤ 3 ∧
    (xi2PieceInterval (gamma5OriginalRow r) j).2 < (gamma5OriginalRow r).S := by
  fin_cases r <;> fin_cases j <;>
    norm_num [xi2PieceInterval, gamma5OriginalRow, row1, row2, row3, row4,
      alpha1, alpha2, alpha3, alpha5, alpha6, alpha7, alpha8, alpha9]

theorem panelPoint_mem {a b : ℝ} {N m : ℕ} (hab : a ≤ b) (hN : 0 < N) (hm : m ≤ N) :
    panelPoint a b N m ∈ Icc a b := by
  have hmono := panelPoint_mono hab N
  constructor
  · simpa only [panelPoint_zero] using hmono (Nat.zero_le m)
  · simpa only [panelPoint_last a b hN] using hmono hm

/-- Every selected panel stays inside the original support and avoids denominator endpoints. -/
theorem clipped_panel_bounds (r : Fin 4) (k j : Fin 9) {N m : ℕ}
    (hN : 0 < N) (hm : m ≤ N)
    (hab : max (upperLeft k) (xi2PieceInterval (gamma5OriginalRow r) j).1 ≤
      min (upperNode k) (xi2PieceInterval (gamma5OriginalRow r) j).2) :
    let t := panelPoint (max (upperLeft k) (xi2PieceInterval (gamma5OriginalRow r) j).1)
      (min (upperNode k) (xi2PieceInterval (gamma5OriginalRow r) j).2) N m
    t ∈ Icc (xi2PieceInterval (gamma5OriginalRow r) j).1
      (xi2PieceInterval (gamma5OriginalRow r) j).2 ∧ 0 < t ∧ t < (gamma5OriginalRow r).S := by
  have ht := panelPoint_mem hab hN hm
  have hl := (le_max_right (upperLeft k) (xi2PieceInterval (gamma5OriginalRow r) j).1).trans ht.1
  have hu := ht.2.trans (min_le_right (upperNode k) (xi2PieceInterval (gamma5OriginalRow r) j).2)
  have hg := original_piece_support_bounds r j
  exact ⟨⟨hl, hu⟩, (by linarith [hg.1]), hu.trans_lt hg.2.2.2⟩

end WuPaper.R2Xi
#print axioms WuPaper.R2Xi.clipped_panel_bounds
