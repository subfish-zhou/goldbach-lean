import MathlibNt.Wu2008DoubleSieve.SecondFunctionalFourPrimeFiniteDensity
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalFourPrimeClosedQuadrature
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighKernelPayloads

namespace Wu2008DoubleSieve.FourPrimeNonunit
open FourPrimeContinuous

/-- Four original closed domains in the original word order, at one common phi. -/
noncomputable def legalK (b c e f phi : ℝ) : Fin 4 → ℝ :=
  vec (K16 c e phi) (K17 c e f phi) (K18 c e f phi) (K19 b c e f phi)

noncomputable def closedK (R b c e f phi : ℝ) : Fin 4 → ℝ :=
  vec (closedPrimeK16 R c e phi) (closedPrimeK17 R c e f phi)
    (closedPrimeK18 R c e f phi) (closedPrimeK19 R b c e f phi)

/-- No supremum or averaging: keep the actual supported d, scale, and phi. -/
noncomputable def sourceClosedK (N d : ℕ) (δ : ℝ)
    (p : SecondFunctionalParameters) (j : Fin 4) : ℝ :=
  closedK ((N:ℝ)^(1/2-δ)/d) (1/p.kappa1) (1/p.kappa2) (1/p.kappa3)
    (1/p.s) (omega3XPhi N d δ) j

noncomputable def sourceLegalK (N d : ℕ) (δ : ℝ)
    (p : SecondFunctionalParameters) (j : Fin 4) : ℝ :=
  legalK (1/p.kappa1) (1/p.kappa2) (1/p.kappa3) (1/p.s) (omega3XPhi N d δ) j

/-- The original sigma times N/(d log(Q/d)), once per supported d. -/
noncomputable def sourceClosedKMass (N : ℕ) (δ Δ : ℝ) {i : ℕ} (V : Fin i → ℝ)
    (p : SecondFunctionalParameters) (j : Fin 4) : ℝ :=
  HighSourcePayload.mass N δ Δ V (fun d => sourceClosedK N d δ p j)

noncomputable def sourceLegalKMass (N : ℕ) (δ Δ : ℝ) {i : ℕ} (V : Fin i → ℝ)
    (p : SecondFunctionalParameters) (j : Fin 4) : ℝ :=
  HighSourcePayload.mass N δ Δ V (fun d => sourceLegalK N d δ p j)

/-- True li(N), original sigma*C(dN)/(totient(d)*log(Q/d)), and the same actual phi. -/
noncomputable def sourceKTheta (N : ℕ) (δ Δ : ℝ) {i : ℕ} (V : Fin i → ℝ)
    (p : SecondFunctionalParameters) (j : Fin 4) : ℝ :=
  HighSourcePayload.theta N δ Δ V (fun d => sourceLegalK N d δ p j)

end Wu2008DoubleSieve.FourPrimeNonunit
