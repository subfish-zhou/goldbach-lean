import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144FiniteInductionBoundary
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144CaseISuccessorFinal
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144CaseIIDispatcher

open scoped Classical BigOperators Interval
open Filter Finset MeasureTheory Set

namespace MathlibNt.SieveTheory

open LinearSieve SwitchingPrinciple
open SuzukiFiniteContinuousLayers
open SwitchingPrinciple.SuzukiLemma144Equation1410
open SwitchingPrinciple.SuzukiLemma144KappaOne

set_option maxHeartbeats 1200000

/-!
# Lemma 14.4: finite-depth global-IH assembly

The induction invariant below is the production
`GlobalDepthLemma144InductionHypothesis`, specialized to the actual discrete
quantity, Euler product, and Section-13 error envelope.  Thus one cutoff is
uniform in `D`, `z`, and every legal parity coordinate.  No abstract error
function is introduced.
-/

/-- The concrete global Lemma-14.4 assertion at one depth and one cutoff. -/
def Lemma144GlobalDepthAt
    (S : BoundingSieve) (H : Section13HatLayers)
    (C K d Δ : ℝ) (N Dmin : ℕ) : Prop :=
  GlobalDepthLemma144InductionHypothesis
    (suzukiActualT S) (fun z => suzukiVProduct S z)
    (fun n D x => errorEnvelope H n (D : ℝ) d x)
    2 C K Δ N Dmin

/-- The concrete natural-ceiling form of Lemma 14.4 with one cutoff placed
before `D` and the parity coordinate. -/
def Lemma144UniformNatCeilAt
    (S : BoundingSieve) (H : Section13HatLayers)
    (C K d Δ : ℝ) (N Dmin : ℕ) : Prop :=
  ∀ D : ℕ, Dmin ≤ D → 2 ≤ D →
    ∀ x : ℝ, x ∈ KappaOneModel.parityDomain 2 N →
    2 ≤ ⌈(D : ℝ) ^ (1 / x)⌉₊ →
    suzukiActualT S N D ⌈(D : ℝ) ^ (1 / x)⌉₊ ≤
      suzukiVProduct S (⌈(D : ℝ) ^ (1 / x)⌉₊ : ℝ) *
        (finiteSourceLayer 1 2 N x +
          C * Real.exp (Real.sqrt K) *
            errorEnvelope H N (D : ℝ) d x *
              (Real.log (D : ℝ)) ^ (-Δ))

/-- Raising the common cutoff preserves the concrete global induction
hypothesis. -/
theorem lemma144GlobalDepthAt_mono_cutoff
    {S : BoundingSieve} {H : Section13HatLayers}
    {C K d Δ : ℝ} {N Dmin Dmin' : ℕ}
    (hcut : Dmin ≤ Dmin')
    (h : Lemma144GlobalDepthAt S H C K d Δ N Dmin) :
    Lemma144GlobalDepthAt S H C K d Δ N Dmin' := by
  intro D z hDmin' hD2 hz2 x hx hpower
  exact h D z (hcut.trans hDmin') hD2 hz2 x hx hpower

/-- A natural-ceiling estimate with all quantifiers behind one cutoff implies
production's exact-power global IH.  The exact-power hypothesis identifies its
natural ceiling with `z`; this is the bridge needed by the successor theorem's
global IH rather than a pointwise surrogate. -/
theorem lemma144GlobalDepthAt_of_uniform_natCeil
    (S : BoundingSieve) (H : Section13HatLayers)
    (C K d Δ : ℝ) (N Dmin : ℕ)
    (hceil : Lemma144UniformNatCeilAt S H C K d Δ N Dmin) :
    Lemma144GlobalDepthAt S H C K d Δ N Dmin := by
  intro D z hDmin hD2 hz2 x hx hpower
  have hceilz : ⌈(D : ℝ) ^ (1 / x)⌉₊ = z := by
    rw [hpower]
    exact Nat.ceil_natCast z
  have hc := hceil D hDmin hD2 x hx
  rw [hceilz] at hc
  exact hc hz2

/-- Complete finite-depth induction assembler for the concrete Lemma-14.4
invariant.

The successor consumes the genuine global depth-`N` IH at the current common
cutoff and returns the depth-`N+1` assertion at a (possibly larger) cutoff.
Because the new cutoff is required to dominate the old one, all earlier depths
are transported to it.  The conclusion therefore has one cutoff before the
quantifiers over depth, `D`, `z`, and the parity coordinate. -/
theorem lemma14_4_finiteDepth_induction_final
    (S : BoundingSieve) (H : Section13HatLayers)
    (C K d Δ : ℝ) (depth : ℕ)
    (hbase : ∃ Dmin : ℕ, 2 ≤ Dmin ∧
      Lemma144UniformNatCeilAt S H C K d Δ 1 Dmin)
    (hsuccessor : ∀ N Dmin : ℕ,
      1 ≤ N → N < depth → 2 ≤ Dmin →
      Lemma144GlobalDepthAt S H C K d Δ N Dmin →
      ∃ Dnext : ℕ, Dmin ≤ Dnext ∧
        Lemma144UniformNatCeilAt S H C K d Δ (N + 1) Dnext) :
    ∃ Dmin : ℕ, 2 ≤ Dmin ∧
      ∀ N : ℕ, 1 ≤ N → N ≤ depth →
        Lemma144GlobalDepthAt S H C K d Δ N Dmin := by
  let P : ℕ → Prop := fun upper =>
    ∃ Dmin : ℕ, 2 ≤ Dmin ∧
      ∀ N : ℕ, 1 ≤ N → N ≤ upper →
        Lemma144GlobalDepthAt S H C K d Δ N Dmin
  have hPbase : P 1 := by
    obtain ⟨Dmin, hDmin, h1ceil⟩ := hbase
    have h1 := lemma144GlobalDepthAt_of_uniform_natCeil
      S H C K d Δ 1 Dmin h1ceil
    refine ⟨Dmin, hDmin, ?_⟩
    intro N hN1 hNle
    have hN : N = 1 := by omega
    simpa [hN] using h1
  have hPstep : ∀ N, 1 ≤ N → N < depth → P N → P (N + 1) := by
    intro N hN1 hNdepth hPN
    obtain ⟨Dmin, hDmin, hall⟩ := hPN
    have hN := hall N hN1 le_rfl
    obtain ⟨Dnext, hmono, hnextCeil⟩ :=
      hsuccessor N Dmin hN1 hNdepth hDmin hN
    have hnext := lemma144GlobalDepthAt_of_uniform_natCeil
      S H C K d Δ (N + 1) Dnext hnextCeil
    refine ⟨Dnext, hDmin.trans hmono, ?_⟩
    intro M hM1 hMle
    by_cases hMN : M = N + 1
    · simpa [hMN] using hnext
    · have hMleN : M ≤ N := by omega
      exact lemma144GlobalDepthAt_mono_cutoff hmono
        (hall M hM1 hMleN)
  by_cases hdepth : depth = 0
  · obtain ⟨Dmin, hDmin, _h1⟩ := hbase
    refine ⟨Dmin, hDmin, ?_⟩
    intro N hN1 hNdepth
    omega
  · exact finiteDepth_induction_from_one depth P hPbase hPstep depth
      (by omega) le_rfl


end MathlibNt.SieveTheory
