import HighThetaLowerSource

namespace HighTheta
open Finset Real Wu2008DoubleSieve HighBoxRecovery
open scoped Classical
noncomputable section

/-- A single actual box carries all paid terminals, with one C and threshold.
No claim of a positive h gain or arbitrary-depth feedback is included. -/
def ActualTerminal {i : ℕ} (N : ℕ) (δ ε ρ C s t : ℝ) (W : Fin i → Finset ℕ) : Prop :=
  RelativeRemainders N δ ε s t W ∧ MainMassPaid N δ ε s t W ∧
    PhiEndpointPaid N δ ε s W ∧ PhiEndpointPaid N δ ε t W ∧
    SwitchedUpperPaid N δ ε ρ s t W ∧
    LowerSourcePaid N δ ε C s W ∧ LowerSourcePaid N δ ε C t W


end
end HighTheta
