import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighNonunitDensity
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighUnitThetaJoinedSource

open scoped BigOperators Classical
namespace Wu2008DoubleSieve
open Finset Real FourthRowPhiOmega2 HighUnitSource

/-- Remaining terms after paying the high unit sources and applying the high
nonunit sieve. The old four nonunit envelopes and Gamma 5--15 are unchanged. -/
noncomputable def secondFunctionalLowerGammaLedger (p : SecondFunctionalParameters)
    {i : ℕ} (N : ℕ) (δ : ℝ) (W : Fin i → Finset ℕ) : ℝ :=
  (∑ j ∈ Icc 5 15, secondFunctionalMotherGammaSum p N δ W j) +
    ∑ j : Fin 4, FourPrimeNonunit.actualEnvelope N δ p W j


end Wu2008DoubleSieve
