import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiCaseIIEndpointQuantitative

namespace MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne

/-- Suzuki's source cutoff from Claim 14.5 (p.82):
`σ(D) = (log D)^(1/d) log(log(27D))`. -/
noncomputable def sourceSigma (D d : ℝ) : ℝ :=
  (Real.log D) ^ (1 / d) * Real.log (Real.log (27 * D))


end MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne
