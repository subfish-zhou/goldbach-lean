import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiFiniteLowerBoundaryLimit
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiSection13PairingComparison

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

@[simp] theorem suzukiProposition118KappaOneSourceAdjoint_eq (s : ℝ) :
    suzukiProposition118KappaOneSourceAdjoint s = s - 1 := rfl

/-- The source adjoint has exactly the positive zero `ρ=1`. -/
theorem suzukiProposition118KappaOneSourceAdjoint_eq_zero_iff
    {s : ℝ} (_hs : 0 < s) :
    suzukiProposition118KappaOneSourceAdjoint s = 0 ↔ s = 1 := by
  constructor <;> intro h <;>
    simp only [suzukiProposition118KappaOneSourceAdjoint] at h ⊢ <;> linarith

/-- The §15.2 values `ρ=1` and `β=ρ+1=2`. -/
def suzukiProposition118KappaOneRho : ℝ := 1

def suzukiProposition118KappaOneBeta : ℝ :=
  suzukiProposition118KappaOneRho + 1

@[simp] theorem suzukiProposition118KappaOneBeta_eq_two :
    suzukiProposition118KappaOneBeta = 2 := by
  norm_num [suzukiProposition118KappaOneBeta,
    suzukiProposition118KappaOneRho]

@[simp] theorem suzukiProposition118KappaOneSourceAdjoint_at_rho :
    suzukiProposition118KappaOneSourceAdjoint
      suzukiProposition118KappaOneRho = 0 := by
  norm_num [suzukiProposition118KappaOneSourceAdjoint,
    suzukiProposition118KappaOneRho]

@[simp] theorem suzukiProposition118KappaOneSourceAdjoint_at_beta :
    suzukiProposition118KappaOneSourceAdjoint
      suzukiProposition118KappaOneBeta = 1 := by
  norm_num [suzukiProposition118KappaOneSourceAdjoint,
    suzukiProposition118KappaOneBeta,
    suzukiProposition118KappaOneRho]

/-- Source equation (11.1) for `q=r_{1,1}`:
`(s q(s))' = q(s) + q(s+1)`. -/
theorem suzukiProposition118KappaOneSourceAdjoint_dde (s : ℝ) :
    HasDerivAt
      (fun u => u * suzukiProposition118KappaOneSourceAdjoint u)
      (suzukiProposition118KappaOneSourceAdjoint s +
        suzukiProposition118KappaOneSourceAdjoint (s + 1)) s := by
  have h := (hasDerivAt_id s).mul ((hasDerivAt_id s).sub_const 1)
  apply h.congr_deriv
  simp only [suzukiProposition118KappaOneSourceAdjoint, id_eq, one_mul, mul_one]
  ring

/-- Suzuki's `D₁(s)` from §11, retaining the companion adjoint `p` as a
parameter.  Since `1-κ=0`, both source power factors are one. -/
def suzukiProposition118KappaOneD (p : ℝ → ℝ) (s : ℝ) : ℝ :=
  p (s - 1) * suzukiProposition118KappaOneSourceAdjoint s +
    suzukiProposition118KappaOneSourceAdjoint (s - 1) * p s

/-- Proposition 11.8(ii)'s explicit `B` formula, specialized to
`κ=1, β=2`.  This is the source formula, not a definition of the production
boundary constant. -/
noncomputable def suzukiProposition118KappaOneBoundaryFormula (p : ℝ → ℝ) : ℝ :=
  2 * suzukiProposition118KappaOneSourceAdjoint
      (suzukiProposition118KappaOneBeta - 1) /
    suzukiProposition118KappaOneD p suzukiProposition118KappaOneBeta

/-- The Proposition-11.8 formula itself evaluates to zero: its numerator is
`2 q(β-1)=2 q(1)=0`.  No nonvanishing denominator is needed in Lean's field
semantics, and no `B=0` premise is present. -/
theorem suzukiProposition118KappaOneBoundaryFormula_eq_zero (p : ℝ → ℝ) :
    suzukiProposition118KappaOneBoundaryFormula p = 0 := by
  simp [suzukiProposition118KappaOneBoundaryFormula,
    suzukiProposition118KappaOneSourceAdjoint,
    suzukiProposition118KappaOneBeta,
    suzukiProposition118KappaOneRho]

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

/-- Exact algebraic form of the last Proposition-11.8 step.  Once the genuine
source-series Iwaniec pairing is proved to vanish, its boundary constant is
forced to equal the explicit source formula (and hence zero). -/
theorem suzukiLowerBoundaryLimit_eq_boundaryFormula_of_pairing_zero
    (p : ℝ → ℝ) (A : ℝ)
    (hpair : suzukiProposition118LowerBoundaryPairingScalar A = 0) :
    suzukiLowerBoundaryLimit =
      suzukiProposition118KappaOneBoundaryFormula p := by
  rw [suzukiProposition118LowerBoundaryPairingScalar_eq_neg] at hpair
  rw [suzukiProposition118KappaOneBoundaryFormula_eq_zero]
  linarith

/-- The earliest still-unproved source edge, stated literally rather than used
as a hidden field: the genuine source-series pairing at `β=2` must be shown to
vanish by Section-10 adjoint conservation and tail decay. -/
noncomputable def SuzukiProposition118LowerBoundaryPairingZero : Prop :=
  suzukiProposition118LowerBoundaryPairingScalar
    SuzukiFiniteContinuousLayers.suzukiLowerSieveAmplitude = 0



end MathlibNt.SieveTheory
