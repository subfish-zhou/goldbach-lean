import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiFiniteLowerBoundaryLimit

/-!
# Suzuki Proposition 11.8(ii) at `κ = 1`, `β = 2`: the boundary-adjoint algebra

The source formulas frozen here are:

* Proposition 10.8(ii): `q(s) = r_{1,1}(s) = s - 1`;
* hence its largest positive zero is `ρ = 1` and §15.2 takes `β = ρ + 1 = 2`;
* Proposition 11.8(ii):
  `B = 2 (β-1)^(1-κ) q(β-1) / (β^(1-κ) D(β))`;
* Proposition 11.8(iii), evaluated from the initial history:
  `⟨Q,q⟩ = -β^(1-κ) q(β) B
    + A (β-1)^(1-κ) q(β-1)`.

At `κ=1, β=2`, the source adjoint has `q(β-1)=q(1)=0` and
`q(β)=q(2)=1`.  Thus both the explicit Proposition-11.8 boundary formula and
its pairing numerator vanish without taking `B=0` as a definition or premise.

The final section deliberately records the earliest remaining production edge:
one must identify the genuine layer-series pairing with the scalar evaluated
below and prove its vanishing by the Section-10 adjoint conservation route.  No
conclusion-shaped hypothesis is used to claim `suzukiLowerBoundaryLimit = 0`.
-/

open scoped Classical BigOperators Interval
open Set Filter Topology MeasureTheory intervalIntegral

namespace MathlibNt.SieveTheory

open SuzukiFiniteContinuousLayers
open SwitchingPrinciple
open SwitchingPrinciple.SuzukiLemma144KappaOne

set_option autoImplicit false

/-- Proposition 10.8(ii), specialized source adjoint
`q=q₁=r_{1,+1}`. -/
def suzukiProposition118KappaOneSourceAdjoint (s : ℝ) : ℝ := s - 1


/-- The §15.2 values `ρ=1` and `β=ρ+1=2`. -/
def suzukiProposition118KappaOneRho : ℝ := 1

def suzukiProposition118KappaOneBeta : ℝ :=
  suzukiProposition118KappaOneRho + 1


/-- Proposition 11.8(iii)'s boundary evaluation of `⟨Q,q⟩`, specialized to
`κ=1, β=2`, but with the genuine production boundary constant inserted.
The source formula is
`-q(β) B + A q(β-1)` after the zero exponents are removed. -/
noncomputable def suzukiProposition118LowerBoundaryPairingScalar (A : ℝ) : ℝ :=
  -suzukiProposition118KappaOneSourceAdjoint
      suzukiProposition118KappaOneBeta * suzukiLowerBoundaryLimit +
    A * suzukiProposition118KappaOneSourceAdjoint
      (suzukiProposition118KappaOneBeta - 1)

/-- At the source endpoint, the genuine boundary pairing scalar is exactly
`-B`: `q(2)=1` and `q(1)=0`. -/
theorem suzukiProposition118LowerBoundaryPairingScalar_eq_neg (A : ℝ) :
    suzukiProposition118LowerBoundaryPairingScalar A =
      -suzukiLowerBoundaryLimit := by
  simp [suzukiProposition118LowerBoundaryPairingScalar,
    suzukiProposition118KappaOneSourceAdjoint,
    suzukiProposition118KappaOneBeta,
    suzukiProposition118KappaOneRho]


end MathlibNt.SieveTheory
