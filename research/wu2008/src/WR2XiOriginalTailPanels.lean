import WR2XiPieceDomain
import WR2XiClippedPanels
import WR2XiScaledKernelPanels

/-! One panel interface for the three original tail pieces. -/
noncomputable section
namespace WuPaper.R2Xi
open Real Set MeasureTheory Wu2008DoubleSieve MotherPair
open scoped Interval

def tailScale (p : SecondFunctionalParameters) : Fin 3 → ℝ :=
  ![p.kappa1, p.S, p.S]
def tailFactor (p : SecondFunctionalParameters) : Fin 3 → ℝ :=
  ![p.kappa2, p.kappa3, p.s]
def tailIndex (i : Fin 3) : Fin 9 := ⟨i.val + 1, by omega⟩

theorem original_tail_domain (r : Fin 4) (i : Fin 3) {t : ℝ}
    (ht : t ∈ Icc (xi2PieceInterval (gamma5OriginalRow r) (tailIndex i)).1
      (xi2PieceInterval (gamma5OriginalRow r) (tailIndex i)).2) :
    t < tailScale (gamma5OriginalRow r) i - 1 ∧
    1 < tailFactor (gamma5OriginalRow r) i ∧
    (tailFactor (gamma5OriginalRow r) i - 1) *
      (tailScale (gamma5OriginalRow r) i - 1 - t) ≤ t + 1 := by
  have h := original_piece_domain r (tailIndex i) ht
  fin_cases i <;> simpa [tailIndex, tailScale, tailFactor, xi2PieceDomain] using h

theorem original_tail_kernel (p : SecondFunctionalParameters) (i : Fin 3) (t : ℝ) :
    xi2PieceKernel p t (tailIndex i) =
      log ((t+1)/((tailFactor p i-1)*(tailScale p i-1-t))) / (5*t) := by
  fin_cases i <;> rfl

/-- Literal support endpoints supply every positivity premise of the tail comparison. -/
theorem original_tail_panel (r : Fin 4) (i : Fin 3) {a b : ℝ}
    (hab : a ≤ b)
    (ha : (xi2PieceInterval (gamma5OriginalRow r) (tailIndex i)).1 ≤ a)
    (hb : b ≤ (xi2PieceInterval (gamma5OriginalRow r) (tailIndex i)).2) :
    (b-a) * (cellLogLower ((a+1)/((tailFactor (gamma5OriginalRow r) i-1)*
      (tailScale (gamma5OriginalRow r) i-1-a))) / (5*b)) ≤
      ∫ t in a..b, xi2PieceKernel (gamma5OriginalRow r) t (tailIndex i) := by
  have hda := original_tail_domain r i ⟨ha, hab.trans hb⟩
  have hdb := original_tail_domain r i ⟨ha.trans hab, hb⟩
  have hs := original_piece_support_bounds r (tailIndex i)
  have hap : 0 < a := by linarith [hs.1]
  have hi := original_subinterval_integrable r (tailIndex i) hab ha hb
  simp_rw [original_tail_kernel] at hi ⊢
  apply scaled_tail_kernel_panel hap hab hdb.1 hda.2.1 _ hi
  apply (one_le_div (mul_pos (by linarith [hda.2.1]) (by linarith [hda.1]))).mpr
  exact hda.2.2

end WuPaper.R2Xi
#print axioms WuPaper.R2Xi.original_tail_panel
