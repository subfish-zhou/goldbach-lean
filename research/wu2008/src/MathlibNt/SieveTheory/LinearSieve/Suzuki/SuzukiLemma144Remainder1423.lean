import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144CaseIAbsorption

open scoped Classical BigOperators Interval
open Filter Finset MeasureTheory Set Topology

namespace MathlibNt.SieveTheory

open LinearSieve SwitchingPrinciple SuzukiFiniteContinuousLayers
open SwitchingPrinciple.SuzukiLemma144KappaOne

set_option autoImplicit false

/-!
# Case I, (14.23): source-faithful remainder interface

The paper does not replace the two Lemma-8.7 endpoints by an arbitrary fixed
quotient.  Claim 14.6(ii) licenses Lemma 8.7, Claim 14.6(iii) supplies the main
contraction, and the two remaining endpoint terms retain the literal coefficient
`3 * (κ + 1) * K^2`, hence `6 * K^2` in the production specialization `κ = 1`.

The paper's subsequent estimates contain `σ^3 log (e σ)`.  Consequently the
already accepted `σ^2` scalar decay is necessary normalization data but is not,
by itself, the source estimate.  The predicates below freeze the exact additional
source inequalities without choosing numerical constants hidden by the paper's
`O` notation.
-/

/-- Exact normalized unit used by every side remainder in (14.23). -/
noncomputable def caseI1423RemainderUnit (B D σ : ℝ) : ℝ :=
  B / (Real.log (Real.log D) * σ)

/-- The literal `Σ₁₁` Lemma-8.7 endpoint at `τ=s`, `κ=1`, `β=2`. -/
noncomputable def caseI1423Sigma11Endpoint
    (S : BoundingSieve) (N D z : ℕ) (K s σ : ℝ) : ℝ :=
  suzukiVProduct S (z : ℝ) *
    (6 * K ^ 2 * finiteSourceLayer 1 2 (N - 1) (s - 1) /
      Real.log ((D : ℝ) ^ (1 / σ)))

/-- The literal `Σ₁₂` Lemma-8.7 endpoint at `τ=s`, `κ=1`.
This is definitionally the existing endpoint after cancelling `s/s`. -/
noncomputable def caseI1423Sigma12Endpoint
    (S : BoundingSieve) (H : Section13HatLayers)
    (N D z : ℕ) (C K d Δ s σ : ℝ) : ℝ :=
  C * Real.exp (Real.sqrt K) * suzukiVProduct S (z : ℝ) *
    (Real.log (D : ℝ)) ^ (-Δ) *
      (6 * K ^ 2 * qD H (ErrorSign.ofDepth N).opposite
        (D : ℝ) d Δ s / Real.log ((D : ℝ) ^ (1 / σ)))

/-- Exact source scalar left in the `Σ₁₁` endpoint calculation on p.87.
The existential coefficient is the honest interpretation of `≪`; it is fixed
before `D` and works eventually. -/
def CaseI1423Sigma11SourceScalar (K d Δ : ℝ) : Prop :=
  ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ D : ℝ in atTop,
    K ^ 2 * sourceSigma D d ^ 3 *
        Real.log (Real.exp 1 * sourceSigma D d) *
        Real.log (Real.log D) /
        (Real.log D) ^ (1 - Δ) ≤ A

/-- Exact source scalar left in the `Σ₁₂` endpoint calculation on p.93.
It is deliberately not weakened to a fixed signed-layer quotient. -/
def CaseI1423Sigma12SourceScalar (K d Δ : ℝ) : Prop :=
  ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ D : ℝ in atTop,
    K ^ 2 * sourceSigma D d ^ 3 *
        Real.log (Real.exp 1 * sourceSigma D d) *
        Real.log (Real.log D) /
        (Real.log D) ^ (1 - Δ) ≤ A

/-- Uniform Claim-14.6 source contract actually consumed before (14.19).
One threshold is chosen before the sign and the moving coordinate.  Part (ii)
is the monotonicity input to Lemma 8.7; part (iii) is the strict integral bound
which creates the main multiplier in (14.23). -/
def CaseI1423Claim146iiiiiSource
    (H : Section13HatLayers) (d Δ : ℝ) : Prop :=
  ∃ D₀ : ℝ, ∀ D : ℝ, D₀ ≤ D →
    let σ := sourceSigma D d
    (∀ sign : ErrorSign,
      AntitoneOn
        (fun t => qD H sign.opposite D d Δ t * t)
        (Set.Ioc (2 + sign.epsilon) σ)) ∧
    (∀ (sign : ErrorSign) (s : ℝ),
      2 + sign.epsilon ≤ s → s ≤ σ →
      (∫ t in s..σ, qD H sign.opposite D d Δ t) <
        (1 - 1 / σ) ^ (1 - Δ) * lambda H sign D d 0 s)

/-- A numerical `O`-coefficient package for the two endpoint estimates.
The constants are selected before `D`; this is the uniformity needed in (14.23).
The hypotheses are the exact inequalities obtained after applying Claim 14.6(ii)
to Lemma 8.7 and then estimating the displayed endpoints on pp.87 and 93. -/
def CaseI1423EndpointSourceBounds : Prop :=
  ∀ (S : BoundingSieve) (H : Section13HatLayers)
      (N : ℕ) (C K d Δ s : ℝ),
    ∃ A11 A12 : ℝ, 0 ≤ A11 ∧ 0 ≤ A12 ∧ ∀ᶠ D : ℕ in atTop,
      let σ := sourceSigma (D : ℝ) d
      let z := ⌈(D : ℝ) ^ (1 / s)⌉₊
      let B := sigma12InheritedBudget S H N D z C K d Δ s
      caseI1423Sigma11Endpoint S N D z K s σ ≤
          A11 * caseI1423RemainderUnit B (D : ℝ) σ ∧
        caseI1423Sigma12Endpoint S H N D z C K d Δ s σ ≤
          A12 * caseI1423RemainderUnit B (D : ℝ) σ

/-- Exact finite algebra behind the endpoint part of (14.23): the two source
remainders combine with coefficient `A11 + A12`, with no generic quotient and
no absorption premise. -/
theorem caseI1423_sigma11_sigma12_endpoints_add
    {R11 R12 A11 A12 B D σ : ℝ}
    (h11 : R11 ≤ A11 * caseI1423RemainderUnit B D σ)
    (h12 : R12 ≤ A12 * caseI1423RemainderUnit B D σ) :
    R11 + R12 ≤
      (A11 + A12) * caseI1423RemainderUnit B D σ := by
  calc
    R11 + R12 ≤
        A11 * caseI1423RemainderUnit B D σ +
          A12 * caseI1423RemainderUnit B D σ := add_le_add h11 h12
    _ = (A11 + A12) * caseI1423RemainderUnit B D σ := by ring

/-- Eventual endpoint combination with all source quantifiers in their required
order.  In particular `A11,A12` are independent of `D`. -/
theorem caseI1423_endpointSourceBounds_combined
    (hsrc : CaseI1423EndpointSourceBounds)
    (S : BoundingSieve) (H : Section13HatLayers)
    (N : ℕ) (C K d Δ s : ℝ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ D : ℕ in atTop,
      let σ := sourceSigma (D : ℝ) d
      let z := ⌈(D : ℝ) ^ (1 / s)⌉₊
      let B := sigma12InheritedBudget S H N D z C K d Δ s
      caseI1423Sigma11Endpoint S N D z K s σ +
          caseI1423Sigma12Endpoint S H N D z C K d Δ s σ ≤
        A * caseI1423RemainderUnit B (D : ℝ) σ := by
  obtain ⟨A11, A12, hA11, hA12, hD⟩ := hsrc S H N C K d Δ s
  refine ⟨A11 + A12, add_nonneg hA11 hA12, ?_⟩
  filter_upwards [hD] with D h
  dsimp only at h ⊢
  exact caseI1423_sigma11_sigma12_endpoints_add h.1 h.2


end MathlibNt.SieveTheory
