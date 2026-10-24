import WR2XiPieceDomain
import WR2XiClippedPanels
import WR2XiScaledKernelPanels

/-! Original rectangular and mixed mother-region panel payments. -/
noncomputable section
namespace WuPaper.R2Xi
open Real Set MeasureTheory Wu2008DoubleSieve MotherPair
open scoped Interval

theorem original_mixed_panel (r : Fin 4) {a b : ℝ} (hab : a ≤ b)
    (ha : (xi2PieceInterval (gamma5OriginalRow r) 6).1 ≤ a)
    (hb : b ≤ (xi2PieceInterval (gamma5OriginalRow r) 6).2) :
    let p := gamma5OriginalRow r
    (b-a) * (cellLogLower (p.S*(p.S-1-a)/(p.kappa1*p.S-p.S-p.kappa1*a)) /
      (5*quadraticDenominatorMax p.S a b)) ≤
      ∫ t in a..b, xi2PieceKernel p t 6 := by
  dsimp only
  have hs := original_piece_support_bounds r 6
  have hap : 0 < a := by linarith [hs.1]
  have hbS := hb.trans_lt hs.2.2.2
  have hda := original_piece_domain r 6 ⟨ha, hab.trans hb⟩
  have hdb := original_piece_domain r 6 ⟨ha.trans hab, hb⟩
  simp only [xi2PieceDomain] at hda hdb
  rcases hda with ⟨hk, hkS, hDa, harg⟩
  have hi := original_subinterval_integrable r 6 hab ha hb
  apply scaled_quadratic_rectangle hap hab hbS ((one_le_div hDa).mpr harg) hi
  intro t ht
  apply mixed_argument_mono (by linarith) hkS ht.1 hDa
  nlinarith [mul_nonneg hk (sub_nonneg.mpr ht.2), hdb.2.2.1]

theorem original_rectangular_panel (r : Fin 4) {a b : ℝ} (hab : a ≤ b)
    (ha : (xi2PieceInterval (gamma5OriginalRow r) 5).1 ≤ a)
    (hb : b ≤ (xi2PieceInterval (gamma5OriginalRow r) 5).2) :
    let p := gamma5OriginalRow r
    (b-a) * (cellLogLower (p.S^2/((p.kappa1*p.S-p.S-p.kappa1*a)*
      (p.kappa3*p.S-p.S-p.kappa3*a))) /
      (5*quadraticDenominatorMax p.S a b)) ≤
      ∫ t in a..b, xi2PieceKernel p t 5 := by
  dsimp only
  have hs := original_piece_support_bounds r 5
  have hap : 0 < a := by linarith [hs.1]
  have hbS := hb.trans_lt hs.2.2.2
  have hda := original_piece_domain r 5 ⟨ha, hab.trans hb⟩
  have hdb := original_piece_domain r 5 ⟨ha.trans hab, hb⟩
  simp only [xi2PieceDomain] at hda hdb
  rcases hda with ⟨hk, hl, hDa, hEa, harg⟩
  have hi := original_subinterval_integrable r 5 hab ha hb
  apply scaled_quadratic_rectangle hap hab hbS ((one_le_div (mul_pos hDa hEa)).mpr harg) hi
  intro t ht
  apply reciprocal_product_le (sq_nonneg (gamma5OriginalRow r).S)
  · nlinarith [mul_nonneg hk (sub_nonneg.mpr ht.1)]
  · nlinarith [mul_nonneg hl (sub_nonneg.mpr ht.1)]
  · nlinarith [mul_nonneg hk (sub_nonneg.mpr ht.2), hdb.2.2.1]
  · nlinarith [mul_nonneg hl (sub_nonneg.mpr ht.2), hdb.2.2.2.1]

end WuPaper.R2Xi
#print axioms WuPaper.R2Xi.original_mixed_panel
#print axioms WuPaper.R2Xi.original_rectangular_panel
