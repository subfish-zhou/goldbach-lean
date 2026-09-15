import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144CaseIIDispatcher

open scoped Classical BigOperators Interval
open Filter Finset MeasureTheory Set Topology

namespace MathlibNt.SieveTheory

open LinearSieve SwitchingPrinciple SuzukiFiniteContinuousLayers
open SwitchingPrinciple.SuzukiLemma144Equation1410
open SwitchingPrinciple.SuzukiLemma144KappaOne

/-!
# Lemma 14.4 Case II: exact final dispatcher boundary

The accepted double-rounded endpoint starts at `2 ≤ N`; for odd depths this is
the range `3 ≤ N`.  The source-native base theorem instead gives the depth-one
bound with local remainder `9 K / (s log D)`.  This file records the exact common
same-`C` eventual conclusion and proves that these two disjoint producers are
sufficient.  It also names the first producer still absent from the accepted
chain: absorption of the depth-one local remainder into the same `C` envelope.
-/

/-- The natural-ceiling Lemma-14.4 estimate at one parameter value.  The
constant `C` occurs literally in the conclusion and is therefore shared by the
base and odd-successor branches. -/
def Lemma144CaseIISameCAt
    (S : BoundingSieve) (H : Section13HatLayers)
    (N D : ℕ) (d Δ C K s : ℝ) : Prop :=
  let z : ℕ := ⌈(D : ℝ) ^ (1 / s)⌉₊
  (∑ n ∈ (Finset.Icc 1 N).filter (fun n => n % 2 = N % 2),
      suzukiSourceV S n D z) ≤
    suzukiVProduct S (z : ℝ) *
      (finiteSourceLayer 1 2 N s +
        C * Real.exp (Real.sqrt K) * errorEnvelope H N (D : ℝ) d s *
          (Real.log (D : ℝ)) ^ (-Δ))

/-- Eventual source-parameter form of the same-`C` Case-II conclusion.  The
moving analytic endpoint used by the successor proof is literally
`sourceSigma D d`; it is exposed here so the producer cannot silently revert to
a fixed `σ`. -/
def Lemma144CaseIISameCEventuallyAtSourceSigma
    (S : BoundingSieve) (H : Section13HatLayers)
    (N : ℕ) (d Δ C K s : ℝ) : Prop :=
  ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ D : ℕ, D₀ ≤ (D : ℝ) →
    let σ : ℝ := sourceSigma (D : ℝ) d
    3 ≤ σ ∧ Lemma144CaseIISameCAt S H N D d Δ C K s

/-- Exact missing base producer.  `lemma14_4_base_one_natCeil` proves only the
antecedent displayed here.  Closing this implication eventually is precisely
the required absorption of `9 K/(s log D)` into the *same* `C` error envelope;
no endpoint, recurrence, or main-sum estimate is hidden in the signature. -/
def Lemma144CaseIIBaseOneSameCProducer
    (S : BoundingSieve) (H : Section13HatLayers)
    (d Δ C K s : ℝ) : Prop :=
  ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ D : ℕ, D₀ ≤ (D : ℝ) →
    let z : ℕ := ⌈(D : ℝ) ^ (1 / s)⌉₊
    3 ≤ sourceSigma (D : ℝ) d ∧
    (suzukiSourceV S 1 D z ≤ suzukiVProduct S (z : ℝ) *
      (finiteSourceLayer 1 2 1 s + 9 * K / (s * Real.log (D : ℝ))) →
      Lemma144CaseIISameCAt S H 1 D d Δ C K s)

/-- The accepted Case-II endpoint must ultimately export this restricted
producer.  Restricting it to `3 ≤ N` exactly matches its premise `2 ≤ N` on odd
natural depths and avoids demanding a false depth-one instance. -/
def Lemma144CaseIIOddSuccessorSameCProducer
    (S : BoundingSieve) (H : Section13HatLayers)
    (d Δ C K s : ℝ) : Prop :=
  ∀ N : ℕ, Odd N → 3 ≤ N →
    Lemma144CaseIISameCEventuallyAtSourceSigma S H N d Δ C K s

/-- Complete Case-II logical assembly.  Both branches use the identical fixed
`C`, and both thresholds precede the natural source parameter `D`. -/
theorem lemma14_4_caseII_sameC_eventually_at_sourceSigma_of_base_successor
    {S : BoundingSieve} {H : Section13HatLayers}
    {N : ℕ} {d Δ C K s : ℝ}
    (hD : ∀ᶠ D : ℕ in atTop, 1 < (D : ℝ))
    (hdom : s ∈ suzukiParityDomainOne 2 N)
    (hs3 : s ≤ 3)
    (hroot2 : ∀ᶠ D : ℕ in atTop, 2 ≤ (D : ℝ) ^ (1 / s))
    (hK : 0 ≤ K)
    (hlocal : HasDimensionOneLocalProductBound S K)
    (hbase : Lemma144CaseIIBaseOneSameCProducer S H d Δ C K s)
    (hsuccessor : Lemma144CaseIIOddSuccessorSameCProducer S H d Δ C K s)
    (hN : Odd N) :
    Lemma144CaseIISameCEventuallyAtSourceSigma S H N d Δ C K s := by
  rcases odd_eq_one_or_three_le N hN with rfl | hN3
  · rcases hbase with ⟨D₀, hD₀, hb⟩
    rcases (eventually_atTop.1 hD) with ⟨D₁, hD₁⟩
    rcases (eventually_atTop.1 hroot2) with ⟨D₂, hD₂⟩
    refine ⟨max D₀ (max D₁ D₂),
      hD₀.trans_le (le_max_left _ _), ?_⟩
    intro D hDmax
    have hD0D : D₀ ≤ (D : ℝ) := (le_max_left D₀ _).trans hDmax
    have hD12real : max (D₁ : ℝ) (D₂ : ℝ) ≤ (D : ℝ) :=
      (le_max_right D₀ _).trans hDmax
    have hD1nat : D₁ ≤ D := by
      exact_mod_cast ((le_max_left (D₁ : ℝ) (D₂ : ℝ)).trans hD12real)
    have hD2nat : D₂ ≤ D := by
      exact_mod_cast ((le_max_right (D₁ : ℝ) (D₂ : ℝ)).trans hD12real)
    have hdom1 : s ∈ suzukiParityDomainOne 2 1 := by simpa using hdom
    refine ⟨(hb D hD0D).1, (hb D hD0D).2 ?_⟩
    exact lemma14_4_base_one_natCeil rfl (hD₁ D hD1nat)
      hdom1 hs3 (hD₂ D hD2nat) hK hlocal
  · exact hsuccessor N hN hN3


end MathlibNt.SieveTheory
