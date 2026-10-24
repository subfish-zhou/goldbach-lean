import WR2XiPieceDomain
import WR2XiClippedPanels
import WR2XiScaledKernelPanels

/-! Original triangular and final mother-region panel payments. -/
noncomputable section
namespace WuPaper.R2Xi
open Real Set MeasureTheory Wu2008DoubleSieve MotherPair
open scoped Interval

theorem original_final_panel (r : Fin 4) {a b : ℝ} (hab : a ≤ b)
    (ha : (xi2PieceInterval (gamma5OriginalRow r) 8).1 ≤ a)
    (hb : b ≤ (xi2PieceInterval (gamma5OriginalRow r) 8).2) :
    (b-a) * (cellLogLower ((gamma5OriginalRow r).S-1-b) /
      (5*quadraticDenominatorMax (gamma5OriginalRow r).S a b)) ≤
      ∫ t in a..b, xi2PieceKernel (gamma5OriginalRow r) t 8 := by
  have hs := original_piece_support_bounds r 8
  have hap : 0 < a := by linarith [hs.1]
  have hbS := hb.trans_lt hs.2.2.2
  have hd := original_piece_domain r 8 ⟨ha.trans hab, hb⟩
  have hx : 1 ≤ (gamma5OriginalRow r).S-1-b := by simpa [xi2PieceDomain] using hd
  have hi := original_subinterval_integrable r 8 hab ha hb
  exact scaled_quadratic_rectangle hap hab hbS hx hi (fun t ht => by linarith [ht.2])

theorem original_triangular_panel (r : Fin 4) {a b : ℝ} (hab : a ≤ b)
    (ha : (xi2PieceInterval (gamma5OriginalRow r) 7).1 ≤ a)
    (hb : b ≤ (xi2PieceInterval (gamma5OriginalRow r) 7).2) :
    let p := gamma5OriginalRow r
    (b-a) * (cellLogLower (p.S/(p.kappa2*p.S-p.S-p.kappa2*a)) /
      (5*quadraticDenominatorMax p.S a b)) ≤
      ∫ t in a..b, xi2PieceKernel p t 7 := by
  dsimp only
  have hs := original_piece_support_bounds r 7
  have hap : 0 < a := by linarith [hs.1]
  have hbS := hb.trans_lt hs.2.2.2
  have hda := original_piece_domain r 7 ⟨ha, hab.trans hb⟩
  have hdb := original_piece_domain r 7 ⟨ha.trans hab, hb⟩
  simp only [xi2PieceDomain] at hda hdb
  have hi := original_subinterval_integrable r 7 hab ha hb
  apply scaled_quadratic_rectangle hap hab hbS ((one_le_div hda.2.1).mpr hda.2.2) hi
  intro t ht
  apply triangular_argument_mono (by linarith) hda.1 ht.1
  nlinarith [mul_nonneg hda.1 (sub_nonneg.mpr ht.2), hdb.2.1]

end WuPaper.R2Xi
#print axioms WuPaper.R2Xi.original_final_panel
#print axioms WuPaper.R2Xi.original_triangular_panel
