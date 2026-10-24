import WR2XiCellIntegral
import WR2XiClippedIntegral

/-! The original Xi2 formula as one sigma term and nine clipped logarithmic pieces. -/
noncomputable section
namespace WuPaper.R2Xi
open Real Set MeasureTheory Wu2008DoubleSieve NodeExtension
open WuPaper.RMapMSigma WuPaper.RMapMMatrix
open scoped Interval BigOperators

def xi2ParameterProduct (p : SecondFunctionalParameters) : ℝ :=
  (p.s - 1) * (p.S - 1) * (p.kappa1 - 1) * (p.kappa2 - 1) * (p.kappa3 - 1)

def xi2SigmaKernel (p : SecondFunctionalParameters) (t : ℝ) : ℝ :=
  sigma0 t / (5 * t) * log (1024 / xi2ParameterProduct p)

def xi2PieceInterval (p : SecondFunctionalParameters) : Fin 9 → ℝ × ℝ := ![
  (alpha2 p, 3), (alpha9 p, alpha1 p), (alpha5 p, alpha2 p),
  (alpha3 p, alpha2 p), (alpha1 p, alpha2 p), (alpha7 p, alpha5 p),
  (alpha5 p, alpha8 p), (alpha6 p, alpha8 p), (alpha8 p, alpha2 p)]

def xi2PieceKernel (p : SecondFunctionalParameters) (t : ℝ) : Fin 9 → ℝ := ![
  log ((t + 1)^5 / xi2ParameterProduct p) / (5 * t),
  log ((t + 1) / ((p.kappa2 - 1) * (p.kappa1 - 1 - t))) / (5 * t),
  log ((t + 1) / ((p.kappa3 - 1) * (p.S - 1 - t))) / (5 * t),
  log ((t + 1) / ((p.s - 1) * (p.S - 1 - t))) / (5 * t),
  log ((t + 1)^2 / ((p.kappa1 - 1) * (p.kappa2 - 1))) / (5 * t),
  log (p.S^2 / ((p.kappa1*p.S - p.S - p.kappa1*t) *
    (p.kappa3*p.S - p.S - p.kappa3*t))) / (5*t*(1-t/p.S)),
  log (p.S*(p.S-1-t)/(p.kappa1*p.S-p.S-p.kappa1*t)) / (5*t*(1-t/p.S)),
  log (p.S/(p.kappa2*p.S-p.S-p.kappa2*t)) / (5*t*(1-t/p.S)),
  log (p.S-1-t) / (5*t*(1-t/p.S))]

def xi2Piece (p : SecondFunctionalParameters) (j : Fin 9) : ℝ → ℝ :=
  (Icc (xi2PieceInterval p j).1 (xi2PieceInterval p j).2).indicator
    (fun t => xi2PieceKernel p t j)

private theorem xi2Piece_indicator (p : SecondFunctionalParameters) (j : Fin 9) (t : ℝ) :
    xi2Piece p j t =
      (Icc (xi2PieceInterval p j).1 (xi2PieceInterval p j).2).indicator (fun _ => (1:ℝ)) t *
        xi2PieceKernel p t j := by
  unfold xi2Piece
  by_cases h : t ∈ Icc (xi2PieceInterval p j).1 (xi2PieceInterval p j).2 <;> simp [h]

theorem Xi2_eq_pieces (p : SecondFunctionalParameters) (t : ℝ) :
    Xi2 p t = xi2SigmaKernel p t + ∑ j : Fin 9, xi2Piece p j t := by
  simp_rw [xi2Piece_indicator]
  simp only [Xi2, xi2SigmaKernel, xi2ParameterProduct,
    xi2PieceInterval, xi2PieceKernel, Fin.sum_univ_succ,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.sum_univ_zero, add_zero]
  ring

/-- Exact cell assembly; each displayed integrability premise concerns an original piece. -/
theorem Xi2Coefficient_eq_clipped (p : SecondFunctionalParameters) (k : Fin 9)
    (hs : IntervalIntegrable (xi2SigmaKernel p) volume (upperLeft k) (upperNode k))
    (hi : ∀ j, IntervalIntegrable (xi2Piece p j) volume (upperLeft k) (upperNode k)) :
    Xi2Coefficient p k =
      (∫ t in upperLeft k..upperNode k, xi2SigmaKernel p t) +
      ∑ j : Fin 9, clippedIntegral (fun t => xi2PieceKernel p t j)
        (upperLeft k) (upperNode k) (xi2PieceInterval p j).1 (xi2PieceInterval p j).2 := by
  have hab : upperLeft k ≤ upperNode k := by
    fin_cases k <;> norm_num [upperLeft, upperNode]
  have hsum : IntervalIntegrable (fun t => ∑ j : Fin 9, xi2Piece p j t)
      volume (upperLeft k) (upperNode k) := by
    have he : (fun t => ∑ j : Fin 9, xi2Piece p j t) = ∑ j : Fin 9, xi2Piece p j := by
      ext t
      simp
    rw [he]
    apply IntervalIntegrable.sum
    intro j _
    exact hi j
  rw [Xi2Coefficient_eq_cell]
  simp_rw [Xi2_eq_pieces]
  rw [intervalIntegral.integral_add hs hsum,
    intervalIntegral.integral_finsetSum (fun j _ => hi j)]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  exact indicator_integral_eq_clipped _ hab

end WuPaper.R2Xi
#print axioms WuPaper.R2Xi.Xi2_eq_pieces

#print axioms WuPaper.R2Xi.Xi2Coefficient_eq_clipped
