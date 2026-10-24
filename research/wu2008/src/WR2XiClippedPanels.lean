import WR2XiPieceGeometry
import WR2XiPieceRegularity

/-! Assemble lower integral payments on clipped original supports. -/
noncomputable section
namespace WuPaper.R2Xi
open Set MeasureTheory Wu2008DoubleSieve NodeExtension MotherPair
open WuPaper.RMapMMatrix
open scoped Interval BigOperators

theorem original_subinterval_integrable (r : Fin 4) (j : Fin 9) {a b : ℝ}
    (hab : a ≤ b)
    (ha : (xi2PieceInterval (gamma5OriginalRow r) j).1 ≤ a)
    (hb : b ≤ (xi2PieceInterval (gamma5OriginalRow r) j).2) :
    IntervalIntegrable (fun t => xi2PieceKernel (gamma5OriginalRow r) t j) volume a b := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hab]
  exact (original_piece_continuous r j).mono (fun t ht => ⟨ha.trans ht.1, ht.2.trans hb⟩)

/-- Strict clipping agrees with the closed clipping convention, including a singleton. -/
theorem clipped_panel_sum_lower (r : Fin 4) (k j : Fin 9) {N : ℕ} (hN : 0 < N)
    (payment : ℝ → ℝ → ℝ)
    (hp : ∀ a b, a ≤ b →
      (xi2PieceInterval (gamma5OriginalRow r) j).1 ≤ a →
      b ≤ (xi2PieceInterval (gamma5OriginalRow r) j).2 →
      payment a b ≤ ∫ t in a..b, xi2PieceKernel (gamma5OriginalRow r) t j) :
    let a := max (upperLeft k) (xi2PieceInterval (gamma5OriginalRow r) j).1
    let b := min (upperNode k) (xi2PieceInterval (gamma5OriginalRow r) j).2
    (if a < b then ∑ m ∈ Finset.range N,
      payment (panelPoint a b N m) (panelPoint a b N (m+1)) else 0) ≤
      clippedIntegral (fun t => xi2PieceKernel (gamma5OriginalRow r) t j)
        (upperLeft k) (upperNode k) (xi2PieceInterval (gamma5OriginalRow r) j).1
        (xi2PieceInterval (gamma5OriginalRow r) j).2 := by
  dsimp only
  generalize ha : max (upperLeft k) (xi2PieceInterval (gamma5OriginalRow r) j).1 = a
  generalize hb : min (upperNode k) (xi2PieceInterval (gamma5OriginalRow r) j).2 = b
  unfold clippedIntegral
  rw [ha, hb]
  by_cases hab : a < b
  · simp only [hab, hab.le, ↓reduceIte]
    have hlo : (xi2PieceInterval (gamma5OriginalRow r) j).1 ≤ a := ha ▸ le_max_right _ _
    have hhi : b ≤ (xi2PieceInterval (gamma5OriginalRow r) j).2 := hb ▸ min_le_right _ _
    have hm := panelPoint_mono hab.le N
    have bounds (m : ℕ) (h : m ≤ N) := panelPoint_mem hab.le hN h
    have hi (m : ℕ) (h : m < N) := original_subinterval_integrable r j
      (hm (Nat.le_succ m)) (hlo.trans (bounds m h.le).1)
      ((bounds (m+1) (Nat.succ_le_of_lt h)).2.trans hhi)
    have he := intervalIntegral.sum_integral_adjacent_intervals hi
    rw [panelPoint_zero, panelPoint_last a b hN] at he
    rw [← he]
    apply Finset.sum_le_sum
    intro m h
    have hmn := Finset.mem_range.mp h
    exact hp _ _ (hm (Nat.le_succ m)) (hlo.trans (bounds m hmn.le).1)
      ((bounds (m+1) (Nat.succ_le_of_lt hmn)).2.trans hhi)
  · simp only [hab, ↓reduceIte]
    split_ifs with hle
    · have he : a = b := le_antisymm hle (le_of_not_gt hab)
      simp [he]
    · exact le_rfl

end WuPaper.R2Xi
#print axioms WuPaper.R2Xi.clipped_panel_sum_lower
