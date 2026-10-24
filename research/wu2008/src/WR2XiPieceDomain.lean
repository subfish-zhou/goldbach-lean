import WR2XiPieceGeometry
import WR2XiSigmaBudget

/-! Polynomial domain certificates on the nine original kernel supports. -/
noncomputable section
namespace WuPaper.R2Xi
open Real Set Wu2008DoubleSieve MotherPair SecondFunctionalParameters
open WuPaper.RMapMMatrix

def xi2PieceDomain (p : SecondFunctionalParameters) (t : ℝ) : Fin 9 → Prop := ![
  (∀ i, 0 < xi2Factors p i ∧ xi2Factors p i ≤ t + 1),
  (t < p.kappa1 - 1 ∧ 1 < p.kappa2 ∧
    (p.kappa2 - 1) * (p.kappa1 - 1 - t) ≤ t + 1),
  (t < p.S - 1 ∧ 1 < p.kappa3 ∧
    (p.kappa3 - 1) * (p.S - 1 - t) ≤ t + 1),
  (t < p.S - 1 ∧ 1 < p.s ∧ (p.s - 1) * (p.S - 1 - t) ≤ t + 1),
  (0 < p.kappa1 - 1 ∧ p.kappa1 - 1 ≤ t + 1 ∧
    0 < p.kappa2 - 1 ∧ p.kappa2 - 1 ≤ t + 1),
  (0 ≤ p.kappa1 ∧ 0 ≤ p.kappa3 ∧
    0 < p.kappa1*p.S-p.S-p.kappa1*t ∧
    0 < p.kappa3*p.S-p.S-p.kappa3*t ∧
    (p.kappa1*p.S-p.S-p.kappa1*t) * (p.kappa3*p.S-p.S-p.kappa3*t) ≤ p.S^2),
  (0 ≤ p.kappa1 ∧ p.kappa1 ≤ p.S ∧
    0 < p.kappa1*p.S-p.S-p.kappa1*t ∧
    p.kappa1*p.S-p.S-p.kappa1*t ≤ p.S*(p.S-1-t)),
  (0 ≤ p.kappa2 ∧ 0 < p.kappa2*p.S-p.S-p.kappa2*t ∧
    p.kappa2*p.S-p.S-p.kappa2*t ≤ p.S),
  (1 ≤ p.S-1-t)]

set_option maxHeartbeats 1600000 in
theorem original_piece_domain (r : Fin 4) (j : Fin 9) {t : ℝ}
    (ht : t ∈ Icc (xi2PieceInterval (gamma5OriginalRow r) j).1
      (xi2PieceInterval (gamma5OriginalRow r) j).2) :
    xi2PieceDomain (gamma5OriginalRow r) t j := by
  rcases ht with ⟨hl, hu⟩
  fin_cases r <;> fin_cases j <;>
    norm_num [xi2PieceDomain, xi2PieceInterval, xi2Factors, gamma5OriginalRow,
      row1, row2, row3, row4, alpha1, alpha2, alpha3, alpha5, alpha6,
      alpha7, alpha8, alpha9, Fin.forall_fin_succ] at hl hu ⊢ <;>
    (repeat' constructor) <;> nlinarith

end WuPaper.R2Xi
#print axioms WuPaper.R2Xi.original_piece_domain
