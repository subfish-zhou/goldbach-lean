import MathlibNt.Wu2008DoubleSieve.SecondFunctionalMotherSource
import MathlibNt.Wu2008DoubleSieve.Gamma5MassMain

/-! Shared literal data for the four mother pair terms. No analytic conclusion
is stored in a structure field. The source identification is a separate proof. -/
namespace Wu2008DoubleSieve.MotherPair
open Finset Real
open scoped Classical Interval

inductive Term where
  | gammaFive | gammaSix | gammaSeven | gammaEight
  deriving DecidableEq

instance termFintype : Fintype Term where
  elems := {.gammaFive, .gammaSix, .gammaSeven, .gammaEight}
  complete := by intro j; cases j <;> simp

def Term.index : Term → ℕ
  | .gammaFive => 5 | .gammaSix => 6 | .gammaSeven => 7 | .gammaEight => 8

structure AnalyticParameters (p : SecondFunctionalParameters) : Prop where
  mother : p.MotherAdmissible
  two_lt_s : 2 < p.s
  s_le_three : p.s ≤ 3
  three_le_S : 3 ≤ p.S
  S_le_five : p.S ≤ 5

structure FullHParameters (p : SecondFunctionalParameters) : Prop
    extends AnalyticParameters p where
  insertion_gap : 2/p.kappa1 + 1/p.kappa3 < 1

structure CapAdmissible (S U : ℝ) : Prop where
  three_le_S : 3 ≤ S
  S_le_five : S ≤ 5
  lower_le_cap : 1/S ≤ U
  cap_lt_half : U < 1/2

/-- Complete physical labels, not a product image. -/
noncomputable def capLabels {i : ℕ} (S U : ℝ) (N : ℕ) (δ : ℝ)
    (W : Fin i → Finset ℕ) : Finset Gamma5ClassicalLabel :=
  (boxConvolutionSupport W ×ˢ (range (N+1) ×ˢ range (N+1))).filter fun x =>
    x.2.1.Prime ∧ x.2.2.Prime ∧ x.2.1.Coprime N ∧ x.2.2.Coprime N ∧
    wuLocalCutoff N δ x.1 S ≤ (x.2.1:ℝ) ∧ x.2.1 < x.2.2 ∧
    (x.2.2:ℝ) < ((N:ℝ)^(1/2-δ)/x.1)^U

noncomputable def fixedCount {i : ℕ} (S : ℝ) (N : ℕ) (δ : ℝ)
    (W : Fin i → Finset ℕ) (X : Finset Gamma5ClassicalLabel) : ℝ :=
  ∑ x ∈ X, (convolutionCoeff W x.1:ℝ) *
    (sourceSieveCount N (gamma5ClassicalProduct x) (x.1*N)
      (wuLocalCutoff N δ x.1 S) : ℝ)

/-- All four endpoints are exponents; upper endpoints are strictly excluded. -/
noncomputable def rectLabels {i : ℕ} (N : ℕ) (δ : ℝ)
    (W : Fin i → Finset ℕ) (A B C D : ℝ) : Finset Gamma5ClassicalLabel :=
  (boxConvolutionSupport W ×ˢ (range (N+1) ×ˢ range (N+1))).filter fun x =>
    x.2.1.Prime ∧ x.2.2.Prime ∧ x.2.1.Coprime N ∧ x.2.2.Coprime N ∧
    ((N:ℝ)^(1/2-δ)/x.1)^A ≤ (x.2.1:ℝ) ∧
    (x.2.1:ℝ) < ((N:ℝ)^(1/2-δ)/x.1)^B ∧
    ((N:ℝ)^(1/2-δ)/x.1)^C ≤ (x.2.2:ℝ) ∧
    (x.2.2:ℝ) < ((N:ℝ)^(1/2-δ)/x.1)^D ∧ x.2.1 < x.2.2

noncomputable def termLabels {i : ℕ} (p : SecondFunctionalParameters)
    (j : Term) (N : ℕ) (δ : ℝ) (W : Fin i → Finset ℕ) : Finset Gamma5ClassicalLabel :=
  match j with
  | .gammaFive => rectLabels N δ W (1/p.S) (1/p.kappa2) (1/p.S) (1/p.kappa2)
  | .gammaSix => rectLabels N δ W (1/p.S) (1/p.kappa1) (1/p.kappa2) (1/p.kappa3)
  | .gammaSeven => rectLabels N δ W (1/p.S) (1/p.kappa1) (1/p.S) (1/p.kappa1)
  | .gammaEight => rectLabels N δ W (1/p.S) (1/p.kappa1) (1/p.kappa1) (1/p.kappa2)

noncomputable def termCount {i : ℕ} (p : SecondFunctionalParameters)
    (j : Term) (N : ℕ) (δ : ℝ) (W : Fin i → Finset ℕ)
    (X : Finset Gamma5ClassicalLabel) : ℝ :=
  match j with
  | .gammaFive => fixedCount p.S N δ W X
  | .gammaSix => fixedCount p.S N δ W X
  | .gammaSeven => ∑ x ∈ X, (convolutionCoeff W x.1:ℝ) *
      (sourceSieveCount N (gamma5ClassicalProduct x) (x.1*N) (x.2.1:ℝ) : ℝ)
  | .gammaEight => ∑ x ∈ X, (convolutionCoeff W x.1:ℝ) *
      (sourceSieveCount N (gamma5ClassicalProduct x) (x.1*N) (x.2.1:ℝ) : ℝ)

noncomputable def rectIntegral (A B C D : ℝ) : ℝ :=
  ∫ t in A..B, ∫ u in min D (max C t)..D, 1/(t*u*(1-t-u))

end Wu2008DoubleSieve.MotherPair
