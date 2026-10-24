import WR2XiOriginalTailPanels
import WR2XiOriginalLastPanels
import WR2XiOriginalMiddlePanels
import WR2XiOriginalProductPanels

/-! A uniform lower payment for every original Xi2 piece and every clipped cell. -/
noncomputable section
namespace WuPaper.R2Xi
open Real Set MeasureTheory Wu2008DoubleSieve MotherPair NodeExtension
open scoped Interval BigOperators

def originalPiecePayment (p : SecondFunctionalParameters) (a b : ℝ) : Fin 9 → ℝ := ![
  (b-a)*(productLogLower (xi2Factors p) a/(5*b)),
  (b-a)*(cellLogLower ((a+1)/((p.kappa2-1)*(p.kappa1-1-a)))/(5*b)),
  (b-a)*(cellLogLower ((a+1)/((p.kappa3-1)*(p.S-1-a)))/(5*b)),
  (b-a)*(cellLogLower ((a+1)/((p.s-1)*(p.S-1-a)))/(5*b)),
  (b-a)*(productLogLower (middleFactors p) a/(5*b)),
  (b-a)*(cellLogLower (p.S^2/((p.kappa1*p.S-p.S-p.kappa1*a)*
    (p.kappa3*p.S-p.S-p.kappa3*a)))/(5*quadraticDenominatorMax p.S a b)),
  (b-a)*(cellLogLower (p.S*(p.S-1-a)/(p.kappa1*p.S-p.S-p.kappa1*a))/
    (5*quadraticDenominatorMax p.S a b)),
  (b-a)*(cellLogLower (p.S/(p.kappa2*p.S-p.S-p.kappa2*a))/
    (5*quadraticDenominatorMax p.S a b)),
  (b-a)*(cellLogLower (p.S-1-b)/(5*quadraticDenominatorMax p.S a b))]

theorem original_piece_panel (r : Fin 4) (j : Fin 9) {a b : ℝ} (hab : a ≤ b)
    (ha : (xi2PieceInterval (gamma5OriginalRow r) j).1 ≤ a)
    (hb : b ≤ (xi2PieceInterval (gamma5OriginalRow r) j).2) :
    originalPiecePayment (gamma5OriginalRow r) a b j ≤
      ∫ t in a..b, xi2PieceKernel (gamma5OriginalRow r) t j := by
  fin_cases j
  · exact original_five_factor_panel r hab ha hb
  · exact original_tail_panel r 0 hab ha hb
  · exact original_tail_panel r 1 hab ha hb
  · exact original_tail_panel r 2 hab ha hb
  · exact original_two_factor_panel r hab ha hb
  · exact original_rectangular_panel r hab ha hb
  · exact original_mixed_panel r hab ha hb
  · exact original_triangular_panel r hab ha hb
  · exact original_final_panel r hab ha hb

def originalPieceLower (r : Fin 4) (k j : Fin 9) (N : ℕ) : ℝ :=
  let a := max (upperLeft k) (xi2PieceInterval (gamma5OriginalRow r) j).1
  let b := min (upperNode k) (xi2PieceInterval (gamma5OriginalRow r) j).2
  if a < b then ∑ m ∈ Finset.range N,
    originalPiecePayment (gamma5OriginalRow r) (panelPoint a b N m)
      (panelPoint a b N (m+1)) j else 0

theorem original_piece_lower (r : Fin 4) (k j : Fin 9) {N : ℕ} (hN : 0 < N) :
    originalPieceLower r k j N ≤
      clippedIntegral (fun t => xi2PieceKernel (gamma5OriginalRow r) t j)
        (upperLeft k) (upperNode k) (xi2PieceInterval (gamma5OriginalRow r) j).1
        (xi2PieceInterval (gamma5OriginalRow r) j).2 :=
  clipped_panel_sum_lower r k j hN (fun a b => originalPiecePayment (gamma5OriginalRow r) a b j)
    (fun _ _ hab ha hb => original_piece_panel r j hab ha hb)

end WuPaper.R2Xi
#print axioms WuPaper.R2Xi.original_piece_lower
