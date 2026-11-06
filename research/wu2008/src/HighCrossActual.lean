import HighCrossTransport
import MathlibNt.Wu2008DoubleSieve.ReboxingSorted

namespace HighCross
open Finset Real Wu2008DoubleSieve HighTheta HighBoxRecovery Filter
open scoped Classical
noncomputable section

/-- Same-mother finite cross lower, before normalization to a universal h.
The inserted gains are actual signed-count candidates from HighCrossFinite. -/
def crossMain {i : ℕ} {β : Type*} [DecidableEq β]
    (N : ℕ) (δ ε ρ C t : ℝ) (W : Fin i → Finset ℕ)
    (B : Finset β) (P : β → Finset ℕ) (u v : β → ℝ) : ℝ :=
  convolutionRosserMain N W false (wuVariableRosserLevel N δ)
      (fun d => wuLocalCutoff N δ d t) - C*N/log (N : ℝ)^(18 : ℝ) -
    (∑ b ∈ B, rosserUpper N δ (u b) (Fin.cons (P b) W)) +
    ∑ b ∈ B, finiteGain N δ ε ρ (u b) (v b) (Fin.cons (P b) W)




end
end HighCross
