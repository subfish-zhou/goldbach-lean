import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiClaim145CaseAssembly

open scoped Classical BigOperators
open MeasureTheory Set

namespace MathlibNt.SieveTheory.SwitchingPrinciple
namespace SuzukiLemma144KappaOne

set_option maxHeartbeats 800000

/-!
# Claim 14.5: exact Case-I/Case-II publication interface

This module is intentionally only a branch dispatcher.  It does not turn a
region-series identity, a `mainSum` estimate, or a source decomposition into a
hypothesis.  Those constructions belong inside the concrete branch proofs.

The current Case-I result closes the Lemma-8.7 contraction component, while the
latest Case-II development closes the direct double-rounded source endpoint and
its eventual relative bracket.  Neither currently exports the same final
`Claim14_5Bound` declaration.  Consequently the interface below is the honest
consumer boundary until both branches publish that common conclusion.
-/

/-- A tagged, exact split.  The two source cases remain different constructors;
in particular the odd short interval is never weakened into or merged with
Case I. -/
inductive Claim14_5ExactBranch (β : ℝ) (N : ℕ) (s σ : ℝ) : Prop where
  | caseI (lower : β + (N % 2 : ℕ) ≤ s) (upper : s ≤ σ)
  | caseII (odd : Odd N) (lower : β - 1 < s) (upper : s ≤ β + 1)

/-- The tagged split is definitionally equivalent to the existing production
Case-I/Case-II predicates. -/
theorem claim14_5ExactBranch_iff
    {β s σ : ℝ} {N : ℕ} :
    Claim14_5ExactBranch β N s σ ↔
      Claim14_5CaseI β N s σ ∨ Claim14_5CaseII β N s := by
  constructor
  · intro h
    cases h with
    | caseI hlo hhi => exact Or.inl ⟨hlo, hhi⟩
    | caseII hodd hlo hhi => exact Or.inr ⟨hodd, hlo, hhi⟩
  · rintro (hI | hII)
    · exact .caseI hI.1 hI.2
    · exact .caseII hII.1 hII.2.1 hII.2.2

/-- Exact branch elimination.  Each branch consumer sees only its own full
range certificate. -/
theorem Claim14_5ExactBranch.elim
    {β s σ : ℝ} {N : ℕ} {P : Prop}
    (h : Claim14_5ExactBranch β N s σ)
    (caseI : β + (N % 2 : ℕ) ≤ s → s ≤ σ → P)
    (caseII : Odd N → β - 1 < s → s ≤ β + 1 → P) : P := by
  cases h with
  | caseI hlo hhi => exact caseI hlo hhi
  | caseII hodd hlo hhi => exact caseII hodd hlo hhi

/-- Common eventual conclusion required from both concrete branches.  The
cutoff `z` may depend on `D`; all other parameters and the Claim-14.5 constant
are fixed before the eventual threshold is chosen. -/
def Claim14_5EventualAt
    (Tdisc : ℕ → ℝ → ℝ → ℝ) (S : BoundingSieve)
    (H : Section13HatLayers) (z : ℝ → ℝ)
    (N : ℕ) (d Δ σ K s C145 : ℝ) : Prop :=
  ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ D : ℝ, D₀ ≤ D →
    Claim14_5Bound Tdisc S H N D (z D) d Δ σ K s C145

/-- Case-I producer interface, with its exact range quantified explicitly. -/
def Claim14_5CaseIEventualConsumer
    (Tdisc : ℕ → ℝ → ℝ → ℝ) (S : BoundingSieve)
    (H : Section13HatLayers) (z : ℝ → ℝ)
    (β d Δ σ K C145 : ℝ) : Prop :=
  ∀ (N : ℕ) (s : ℝ),
    β + (N % 2 : ℕ) ≤ s → s ≤ σ →
      Claim14_5EventualAt Tdisc S H z N d Δ σ K s C145

/-- Case-II producer interface, retaining the oddness and open lower endpoint. -/
def Claim14_5CaseIIEventualConsumer
    (Tdisc : ℕ → ℝ → ℝ → ℝ) (S : BoundingSieve)
    (H : Section13HatLayers) (z : ℝ → ℝ)
    (β d Δ σ K C145 : ℝ) : Prop :=
  ∀ (N : ℕ) (s : ℝ),
    Odd N → β - 1 < s → s ≤ β + 1 →
      Claim14_5EventualAt Tdisc S H z N d Δ σ K s C145

/-- Consumer of an already tagged exact split.  No analytic or discrete
internal premise is added to the public call surface. -/
theorem claim14_5_eventual_of_exact_branch
    {Tdisc : ℕ → ℝ → ℝ → ℝ} {S : BoundingSieve}
    {H : Section13HatLayers} {z : ℝ → ℝ}
    {β d Δ σ K s C145 : ℝ} {N : ℕ}
    (hbranch : Claim14_5ExactBranch β N s σ)
    (hI : Claim14_5CaseIEventualConsumer
      Tdisc S H z β d Δ σ K C145)
    (hII : Claim14_5CaseIIEventualConsumer
      Tdisc S H z β d Δ σ K C145) :
    Claim14_5EventualAt Tdisc S H z N d Δ σ K s C145 := by
  exact hbranch.elim
    (fun hlo hhi => hI N s hlo hhi)
    (fun hodd hlo hhi => hII N s hodd hlo hhi)

/-- Final exact dispatcher on Suzuki's parity domain.  The production split
selects one of the two distinct proof interfaces (kept separate even at their
shared boundary), and the selected branch returns the same eventual
Claim-14.5 bound. -/
theorem claim14_5_eventual_exact_case_split
    {Tdisc : ℕ → ℝ → ℝ → ℝ} {S : BoundingSieve}
    {H : Section13HatLayers} {z : ℝ → ℝ}
    {β D d Δ σ C1 K ΘK s C145 : ℝ} {N : ℕ}
    (hdom : s ∈ SuzukiFiniteContinuousLayers.suzukiParityDomainOne β N)
    (hsσ : s ≤ σ) (hlarge : C1 * K ^ ΘK < Real.log D)
    (hI : Claim14_5CaseIEventualConsumer
      Tdisc S H z β d Δ σ K C145)
    (hII : Claim14_5CaseIIEventualConsumer
      Tdisc S H z β d Δ σ K C145) :
    Claim14_5EventualAt Tdisc S H z N d Δ σ K s C145 := by
  apply claim14_5_eventual_of_exact_branch
    (claim14_5ExactBranch_iff.mpr
      (claim14_5_exact_case_split hdom hsσ hlarge)) hI hII

/-!
## Remaining bridge to Lemma 14.4

The dispatcher is complete, but entering Lemma 14.4 still requires production
proofs of the two consumer predicates above for one identical `Tdisc`, cutoff
function `z`, normalization, and fixed admissible `C145`:

* Case I: promote the existing eventual Lemma-8.7 contraction component to the
  full discrete Claim-14.5 bound.
* Case II: combine the direct double-rounded source endpoint theorem, source
  geometry threshold, and eventual relative-bracket contraction, then transport
  that source-native conclusion to `Claim14_5Bound`.
* Common endpoint: verify the resulting constant has the uniform dependence
  required by Claim 14.5 and connect the common bound to the induction/source
  recurrence consumed by Lemma 14.4.
-/


end SuzukiLemma144KappaOne
end MathlibNt.SieveTheory.SwitchingPrinciple
