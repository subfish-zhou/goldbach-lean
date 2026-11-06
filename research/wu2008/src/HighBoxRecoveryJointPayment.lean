import HighBoxRecoveryActualBoxes

namespace HighBoxRecovery
open Finset Real Wu2008DoubleSieve Filter
open scoped Classical Topology
noncomputable section

/-- Literal actual residual bounds; no prime-count/li substitution is hidden here. -/
def RemainderBounds {i : ℕ} (N : ℕ) (δ A C K s t : ℝ) (W : Fin i → Finset ℕ) : Prop :=
  let Q := (N : ℝ)^(1/2-δ)
  omega3SieveR1 N (⌊Q⌋₊+1) δ s t (sqrt Q) W ≤ C*N/log (N : ℝ)^A ∧
  omega3SieveR2 N (⌊Q⌋₊+1) δ s t (sqrt Q) W ≤
    K*N*((1+log N)*log N^4/((N : ℝ)^highEta*log 2))


end
end HighBoxRecovery
