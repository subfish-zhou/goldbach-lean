import MathlibNt.Wu2008DoubleSieve.SecondFunctionalMotherPairClassicalPorts
import MathlibNt.Wu2008DoubleSieve.Gamma5GainKernel

namespace Wu2008DoubleSieve.MotherPair
open Set Real
open scoped Classical

noncomputable def upperP (p : SecondFunctionalParameters) : Term → ℝ
  | .gammaFive => 1/p.kappa2
  | _ => 1/p.kappa1

noncomputable def lowerQ (p : SecondFunctionalParameters) : Term → ℝ
  | .gammaSix => 1/p.kappa2
  | .gammaEight => 1/p.kappa1
  | _ => 1/p.S

noncomputable def upperQ (p : SecondFunctionalParameters) : Term → ℝ
  | .gammaSix => 1/p.kappa3
  | .gammaSeven => 1/p.kappa1
  | _ => 1/p.kappa2

def gainRegion (p : SecondFunctionalParameters) (j : Term) : Set (ℝ × ℝ) :=
  {v | PairRegion p j v.1 v.2 ∧ gamma5GainLegal v.1 v.2}

noncomputable def gainLiteral (p : SecondFunctionalParameters) (j : Term)
    (δ t u : ℝ) : ℝ :=
  if gamma5GainLegal t u then
    wuImprovementLimit true δ (Hratio p j t u)/(t*u*(1-t-u)) else 0

noncomputable def gainIntegral (p : SecondFunctionalParameters) (j : Term) (δ : ℝ) : ℝ :=
  ∫ t in (1/p.S)..(upperP p j),
    ∫ u in (min (upperQ p j) (max (lowerQ p j) t))..(upperQ p j), gainLiteral p j δ t u

noncomputable def gainKernel (p : SecondFunctionalParameters) (j : Term)
    (δ : ℝ) (v : ℝ × ℝ) : ℝ :=
  if v ∈ gainRegion p j then
    gamma5GainH δ (Hratio p j v.1 v.2)/(v.1*v.2*(1-v.1-v.2)) else 0

/-- Only strict scalar geometry and a right-endpoint H sample, not an analytic bound. -/
structure GainRectangle (p : SecondFunctionalParameters) (j : Term) where
  A : ℝ
  B : ℝ
  C : ℝ
  D : ℝ
  sample : ℝ
  lowerP_lt_A : 1/p.S < A
  A_lt_B : A < B
  B_lt_C : B < C
  C_lt_D : C < D
  B_lt_upperP : B < upperP p j
  lowerQ_lt_C : lowerQ p j < C
  D_lt_upperQ : D < upperQ p j
  twiceD_lt_one : 2*D < 1
  D_twiceB_lt_one : D+2*B < 1
  sample_lower : 1 < sample
  sample_upper : sample < 3
  ratio_lt_sample : Hratio p j A C < sample

end Wu2008DoubleSieve.MotherPair
