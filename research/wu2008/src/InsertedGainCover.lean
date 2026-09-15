import InsertedGainRange
import MathlibNt.Wu2008DoubleSieve.PhiBuchstab

namespace InsertedGain
open Finset Real Wu2008DoubleSieve HighBoxRecovery
open scoped Classical
noncomputable section

/-- Occupied cells of the existing full source grid at the classical endpoint
three. The index r is its original symbolic terminal, never a numerical mesh. -/
def occupiedCells (N : ℕ) (δ Δ : ℝ) (V : Fin 2 → ℝ) (s : ℝ) (r : ℕ) : Finset ℕ :=
  (range (r+2)).filter fun j =>
    ∃ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
    ∃ p ∈ primeWindow N (wuLocalCutoff N δ d 3) (wuLocalCutoff N δ d s),
      p ∈ HighOmega2.cell N ((N : ℝ)^(1/2-δ)/(∏ l, V l)) Δ 3 j

/-- The actual full insertion mass; both count and quadrature consumers use
this single literal carrier, including the two endpoint cells when occupied. -/
def coverTheta (N : ℕ) (δ Δ : ℝ) (V : Fin 2 → ℝ) (s : ℝ) (r : ℕ) : ℝ :=
  ∑ j ∈ occupiedCells N δ Δ V s r,
    boxTheta N ((N : ℝ)^(1/2-δ))
      (convolutionWuWindows N Δ
        (Fin.cons (reboxingAlpha ((N : ℝ)^(1/2-δ)/(∏ l, V l)) Δ 3 (j+1)) V))

end
end InsertedGain
