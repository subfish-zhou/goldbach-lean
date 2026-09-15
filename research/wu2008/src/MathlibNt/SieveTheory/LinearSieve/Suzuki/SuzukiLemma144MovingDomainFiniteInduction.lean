import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144CaseIIFinalProducer

open scoped Classical BigOperators Interval
open Filter Finset MeasureTheory Set Topology

namespace MathlibNt.SieveTheory

open LinearSieve SwitchingPrinciple SuzukiFiniteContinuousLayers
open SwitchingPrinciple.SuzukiLemma144Equation1410
open SwitchingPrinciple.SuzukiLemma144KappaOne

set_option maxHeartbeats 1200000

/-!
# Lemma 14.4: source-faithful moving-domain finite-depth contract

The source producer is only asserted while the continuous coordinate lies below
`sourceSigma D d`.  Accordingly, every clause quantified over `D` and a
coordinate carries the pointwise hypothesis

`x ≤ sourceSigma (D : ℝ) d`.

No theorem in this file promotes this moving-domain statement to the legacy
all-coordinate contract `Lemma144UniformNatCeilAt` or to
`GlobalDepthLemma144InductionHypothesis`.
-/

/-- The exact-power form of Lemma 14.4 on its source-native moving domain. -/
def Lemma144MovingDomainGlobalDepthAt
    (S : BoundingSieve) (H : Section13HatLayers)
    (C K d Δ : ℝ) (N Dmin : ℕ) : Prop :=
  ∀ D z : ℕ, Dmin ≤ D → 2 ≤ D → 2 ≤ z →
    ∀ x : ℝ, x ∈ KappaOneModel.parityDomain 2 N →
      x ≤ sourceSigma (D : ℝ) d →
      (D : ℝ) ^ (1 / x) = (z : ℝ) →
      suzukiActualT S N D z ≤
        suzukiVProduct S z *
          (finiteSourceLayer 1 2 N x +
            C * Real.exp (Real.sqrt K) *
              errorEnvelope H N (D : ℝ) d x *
                (Real.log (D : ℝ)) ^ (-Δ))

/-- Natural-ceiling form of the same moving-domain assertion.  The common
cutoff precedes `D`; the source endpoint is evaluated at that `D`. -/
def Lemma144MovingDomainNatCeilAt
    (S : BoundingSieve) (H : Section13HatLayers)
    (C K d Δ : ℝ) (N Dmin : ℕ) : Prop :=
  ∀ D : ℕ, Dmin ≤ D → 2 ≤ D →
    ∀ x : ℝ, x ∈ KappaOneModel.parityDomain 2 N →
      x ≤ sourceSigma (D : ℝ) d →
      2 ≤ ⌈(D : ℝ) ^ (1 / x)⌉₊ →
      suzukiActualT S N D ⌈(D : ℝ) ^ (1 / x)⌉₊ ≤
        suzukiVProduct S (⌈(D : ℝ) ^ (1 / x)⌉₊ : ℝ) *
          (finiteSourceLayer 1 2 N x +
            C * Real.exp (Real.sqrt K) *
              errorEnvelope H N (D : ℝ) d x *
                (Real.log (D : ℝ)) ^ (-Δ))

/-- Restriction of the natural-ceiling moving-domain contract to one side of a
Case-I/Case-II partition. -/
def Lemma144MovingDomainNatCeilRestrictedAt
    (S : BoundingSieve) (H : Section13HatLayers)
    (C K d Δ : ℝ) (N Dmin : ℕ) (Q : ℝ → Prop) : Prop :=
  ∀ D : ℕ, Dmin ≤ D → 2 ≤ D →
    ∀ x : ℝ, x ∈ KappaOneModel.parityDomain 2 N →
      x ≤ sourceSigma (D : ℝ) d → Q x →
      2 ≤ ⌈(D : ℝ) ^ (1 / x)⌉₊ →
      suzukiActualT S N D ⌈(D : ℝ) ^ (1 / x)⌉₊ ≤
        suzukiVProduct S (⌈(D : ℝ) ^ (1 / x)⌉₊ : ℝ) *
          (finiteSourceLayer 1 2 N x +
            C * Real.exp (Real.sqrt K) *
              errorEnvelope H N (D : ℝ) d x *
                (Real.log (D : ℝ)) ^ (-Δ))

/-- Raising the common cutoff preserves the source-faithful exact-power
contract. -/
theorem lemma144MovingDomainGlobalDepthAt_mono_cutoff
    {S : BoundingSieve} {H : Section13HatLayers}
    {C K d Δ : ℝ} {N Dmin Dmin' : ℕ}
    (hcut : Dmin ≤ Dmin')
    (h : Lemma144MovingDomainGlobalDepthAt S H C K d Δ N Dmin) :
    Lemma144MovingDomainGlobalDepthAt S H C K d Δ N Dmin' := by
  intro D z hDmin' hD2 hz2 x hx hxSigma hpower
  exact h D z (hcut.trans hDmin') hD2 hz2 x hx hxSigma hpower

/-- The natural ceiling gives the exact-power form without changing the moving
coordinate domain. -/
theorem lemma144MovingDomainGlobalDepthAt_of_natCeil
    (S : BoundingSieve) (H : Section13HatLayers)
    (C K d Δ : ℝ) (N Dmin : ℕ)
    (hceil : Lemma144MovingDomainNatCeilAt S H C K d Δ N Dmin) :
    Lemma144MovingDomainGlobalDepthAt S H C K d Δ N Dmin := by
  intro D z hDmin hD2 hz2 x hx hxSigma hpower
  have hceilz : ⌈(D : ℝ) ^ (1 / x)⌉₊ = z := by
    rw [hpower]
    exact Nat.ceil_natCast z
  have hc := hceil D hDmin hD2 x hx hxSigma
  rw [hceilz] at hc
  exact hc hz2

/-- Case-I and Case-II packets combine pointwise at one cutoff.  The moving
source-domain premise is retained in both branches. -/
theorem lemma144MovingDomainNatCeilAt_of_restricted_cases
    {S : BoundingSieve} {H : Section13HatLayers}
    {C K d Δ : ℝ} {N DI DII : ℕ} {QI QII : ℝ → Prop}
    (hcover : ∀ x, x ∈ KappaOneModel.parityDomain 2 N → QI x ∨ QII x)
    (hI : Lemma144MovingDomainNatCeilRestrictedAt
      S H C K d Δ N DI QI)
    (hII : Lemma144MovingDomainNatCeilRestrictedAt
      S H C K d Δ N DII QII) :
    Lemma144MovingDomainNatCeilAt S H C K d Δ N (max DI DII) := by
  intro D hD hD2 x hx hxSigma hz
  rcases hcover x hx with hxI | hxII
  · exact hI D ((le_max_left DI DII).trans hD) hD2 x hx hxSigma hxI hz
  · exact hII D ((le_max_right DI DII).trans hD) hD2 x hx hxSigma hxII hz

/-- Source-faithful finite-depth induction.  Each successor consumes only the
moving-domain predecessor assertion, not the legacy all-coordinate global IH. -/
theorem lemma14_4_movingDomain_finiteDepth_induction
    (S : BoundingSieve) (H : Section13HatLayers)
    (C K d Δ : ℝ) (depth : ℕ)
    (hbase : ∃ Dmin : ℕ, 2 ≤ Dmin ∧
      Lemma144MovingDomainNatCeilAt S H C K d Δ 1 Dmin)
    (hsuccessor : ∀ N Dmin : ℕ,
      1 ≤ N → N < depth → 2 ≤ Dmin →
      Lemma144MovingDomainGlobalDepthAt S H C K d Δ N Dmin →
      ∃ Dnext : ℕ, Dmin ≤ Dnext ∧
        Lemma144MovingDomainNatCeilAt S H C K d Δ (N + 1) Dnext) :
    ∃ Dmin : ℕ, 2 ≤ Dmin ∧
      ∀ N : ℕ, 1 ≤ N → N ≤ depth →
        Lemma144MovingDomainGlobalDepthAt S H C K d Δ N Dmin := by
  let P : ℕ → Prop := fun upper =>
    ∃ Dmin : ℕ, 2 ≤ Dmin ∧
      ∀ N : ℕ, 1 ≤ N → N ≤ upper →
        Lemma144MovingDomainGlobalDepthAt S H C K d Δ N Dmin
  have hPbase : P 1 := by
    obtain ⟨Dmin, hDmin, h1ceil⟩ := hbase
    have h1 := lemma144MovingDomainGlobalDepthAt_of_natCeil
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
    have hnext := lemma144MovingDomainGlobalDepthAt_of_natCeil
      S H C K d Δ (N + 1) Dnext hnextCeil
    refine ⟨Dnext, hDmin.trans hmono, ?_⟩
    intro M hM1 hMle
    by_cases hMN : M = N + 1
    · simpa [hMN] using hnext
    · have hMleN : M ≤ N := by omega
      exact lemma144MovingDomainGlobalDepthAt_mono_cutoff hmono
        (hall M hM1 hMleN)
  by_cases hdepth : depth = 0
  · obtain ⟨Dmin, hDmin, _⟩ := hbase
    refine ⟨Dmin, hDmin, ?_⟩
    intro N hN1 hNdepth
    omega
  · exact finiteDepth_induction_from_one depth P hPbase hPstep depth
      (by omega) le_rfl

/-- The Case-II successor packet at the quantifier order consumed by the
moving-domain finite-depth assembler. -/
def Lemma144MovingDomainCaseIIHCase
    (S : BoundingSieve) (H : Section13HatLayers)
    (C K d Δ : ℝ) (depth : ℕ) : Prop :=
  ∀ N Dmin : ℕ,
    1 ≤ N → N < depth → 2 ≤ Dmin →
    Lemma144MovingDomainGlobalDepthAt S H C K d Δ N Dmin →
    ∃ DII : ℕ, Dmin ≤ DII ∧
      Lemma144MovingDomainNatCeilRestrictedAt
        S H C K d Δ (N + 1) DII (Lemma144CaseIIFinalSide (N + 1))

/-- Total finite-depth assembly using the exact Case-II moving-domain packet.
Case I is the logical complement of the odd low strip. -/
theorem lemma14_4_movingDomain_full_finiteDepth
    (S : BoundingSieve) (H : Section13HatLayers)
    (C K d Δ : ℝ) (depth : ℕ)
    (hbase : ∃ Dmin : ℕ, 2 ≤ Dmin ∧
      Lemma144MovingDomainNatCeilAt S H C K d Δ 1 Dmin)
    (hcaseI : ∀ N Dmin : ℕ,
      1 ≤ N → N < depth → 2 ≤ Dmin →
      Lemma144MovingDomainGlobalDepthAt S H C K d Δ N Dmin →
      ∃ DI : ℕ, Dmin ≤ DI ∧
        Lemma144MovingDomainNatCeilRestrictedAt S H C K d Δ (N + 1) DI
          (fun x => ¬ Lemma144CaseIIFinalSide (N + 1) x))
    (hcaseII : Lemma144MovingDomainCaseIIHCase S H C K d Δ depth) :
    ∃ Dmin : ℕ, 2 ≤ Dmin ∧
      ∀ N : ℕ, 1 ≤ N → N ≤ depth →
        Lemma144MovingDomainGlobalDepthAt S H C K d Δ N Dmin := by
  apply lemma14_4_movingDomain_finiteDepth_induction
    S H C K d Δ depth hbase
  intro N Dmin hN hNdepth hDmin hIH
  obtain ⟨DI, hIDI, hI⟩ := hcaseI N Dmin hN hNdepth hDmin hIH
  obtain ⟨DII, hIDII, hII⟩ := hcaseII N Dmin hN hNdepth hDmin hIH
  refine ⟨max DI DII, hIDI.trans (le_max_left _ _), ?_⟩
  apply lemma144MovingDomainNatCeilAt_of_restricted_cases
    (QI := fun x => ¬ Lemma144CaseIIFinalSide (N + 1) x)
    (QII := Lemma144CaseIIFinalSide (N + 1))
  · intro x _hx
    by_cases hxII : Lemma144CaseIIFinalSide (N + 1) x
    · exact Or.inr hxII
    · exact Or.inl hxII
  · exact hI
  · exact hII


end MathlibNt.SieveTheory
