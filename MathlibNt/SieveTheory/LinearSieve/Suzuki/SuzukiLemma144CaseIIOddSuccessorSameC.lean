import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144CaseIIFinalBoundary
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiSourceCaseIIFinalEventual
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiRoundedConcreteRelativeAssembly

open scoped Classical BigOperators Interval
open Filter Finset MeasureTheory Set Topology

namespace MathlibNt.SieveTheory

open LinearSieve SwitchingPrinciple SuzukiFiniteContinuousLayers
open SwitchingPrinciple.SuzukiLemma144Equation1410
open SwitchingPrinciple.SuzukiLemma144KappaOne

set_option maxHeartbeats 1200000

/-!
# Case II, odd depth at least three: the remaining same-`C` normalization

The accepted rounded source chain ends with a relative bracket and an additive
recursive endpoint term `B₀ N D`.  The target `Lemma144CaseIISameCAt` contains
neither that endpoint term nor a larger constant.  The exact missing comparison
is therefore the absorption of `B₀ N D` by the strict bracket gap
`1 - caseIIConcreteRoundedRelativeBracket ...`.

The definitions below keep the large-`D` cutoff before `s`, and permit the
cutoff to depend on the fixed finite depth `N`.  The final theorem proves that
this comparison, together with the accepted rounded-relative output, is exactly
sufficient to construct `Lemma144CaseIIOddSuccessorSameCProducer`.
-/

private noncomputable def caseIISameCScale
    (H : Section13HatLayers) (N : ℕ) (D : ℝ)
    (d Δ C K s : ℝ) : ℝ :=
  C * Real.exp (Real.sqrt K) * errorEnvelope H N D d s *
    (Real.log D) ^ (-Δ)

private noncomputable def caseIISourceBracket
    (N : ℕ) (D d Δ C K : ℝ) : ℝ :=
  caseIIConcreteRoundedRelativeBracket N D d Δ (sourceSigma D d) C K

/-- Exact output shape of the accepted rounded Case-II source assembly, with a
threshold uniform in `s ∈ (1,3]` (but allowed to depend on the fixed depth). -/
def Lemma144CaseIIOddRoundedRelativeProducer
    (S : BoundingSieve) (H : Section13HatLayers)
    (B₀ : ℕ → ℕ → ℝ) (d Δ C K : ℝ) : Prop :=
  ∀ N : ℕ, Odd N → 3 ≤ N →
    ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ D : ℕ, D₀ ≤ (D : ℝ) →
      ∀ s : ℝ, 1 < s → s ≤ 3 →
        3 ≤ sourceSigma (D : ℝ) d ∧
        caseIISourceBracket N (D : ℝ) d Δ C K < 1 ∧
        let z : ℕ := ⌈(D : ℝ) ^ (1 / s)⌉₊
        (∑ n ∈ (Finset.Icc 1 N).filter (fun n => n % 2 = N % 2),
            suzukiSourceV S n D z) ≤
          B₀ N D + suzukiVProduct S (z : ℝ) *
            (finiteSourceLayer 1 2 N s +
              caseIISameCScale H N (D : ℝ) d Δ C K s *
                caseIISourceBracket N (D : ℝ) d Δ C K)

/-- Earliest missing normalization after the accepted rounded-relative
assembly.  It does not assume the desired successor inequality: it compares
only the recursive endpoint term with the unused strict-bracket margin. -/
def Lemma144CaseIIOddEndpointGapNormalization
    (S : BoundingSieve) (H : Section13HatLayers)
    (B₀ : ℕ → ℕ → ℝ) (d Δ C K : ℝ) : Prop :=
  ∀ N : ℕ, Odd N → 3 ≤ N →
    ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ D : ℕ, D₀ ≤ (D : ℝ) →
      ∀ s : ℝ, 1 < s → s ≤ 3 →
        let z : ℕ := ⌈(D : ℝ) ^ (1 / s)⌉₊
        B₀ N D ≤ suzukiVProduct S (z : ℝ) *
          (caseIISameCScale H N (D : ℝ) d Δ C K s *
            (1 - caseIISourceBracket N (D : ℝ) d Δ C K))

/-- Terminal algebra: the endpoint-gap comparison removes `B₀` without
changing `C`. -/
theorem caseII_sameC_of_relative_and_endpoint_gap
    {sourceSum V B₀ finiteLayer scale bracket : ℝ}
    (hB₀ : B₀ ≤ V * (scale * (1 - bracket)))
    (hrelative : sourceSum ≤ B₀ + V * (finiteLayer + scale * bracket)) :
    sourceSum ≤ V * (finiteLayer + scale) := by
  calc
    sourceSum ≤ B₀ + V * (finiteLayer + scale * bracket) := hrelative
    _ ≤ V * (scale * (1 - bracket)) +
          V * (finiteLayer + scale * bracket) := add_le_add_left hB₀ _
    _ = V * (finiteLayer + scale) := by ring

/-- A uniform-in-`s` rounded-relative producer plus the exact endpoint-gap
normalization constructs the actual dispatcher producer.  The threshold may
still depend on the fixed finite odd depth `N`, which is all the producer
interface requires. -/
theorem lemma14_4_caseII_odd_successor_sameC_producer_of_endpoint_gap
    {S : BoundingSieve} {H : Section13HatLayers}
    {B₀ : ℕ → ℕ → ℝ} {d Δ C K s : ℝ}
    (hrelative : Lemma144CaseIIOddRoundedRelativeProducer S H B₀ d Δ C K)
    (hnormalize : Lemma144CaseIIOddEndpointGapNormalization S H B₀ d Δ C K)
    (hs1 : 1 < s) (hs3 : s ≤ 3) :
    Lemma144CaseIIOddSuccessorSameCProducer S H d Δ C K s := by
  intro N hN hN3
  obtain ⟨Dr, hDr1, hr⟩ := hrelative N hN hN3
  obtain ⟨Dn, hDn1, hn⟩ := hnormalize N hN hN3
  refine ⟨max Dr Dn, hDr1.trans_le (le_max_left _ _), ?_⟩
  intro D hD
  have hDrD : Dr ≤ (D : ℝ) := (le_max_left Dr Dn).trans hD
  have hDnD : Dn ≤ (D : ℝ) := (le_max_right Dr Dn).trans hD
  obtain ⟨hσ, _hb, hrel⟩ := hr D hDrD s hs1 hs3
  refine ⟨hσ, ?_⟩
  let z : ℕ := ⌈(D : ℝ) ^ (1 / s)⌉₊
  have hgap := hn D hDnD s hs1 hs3
  dsimp [Lemma144CaseIISameCAt]
  exact caseII_sameC_of_relative_and_endpoint_gap hgap hrel


end MathlibNt.SieveTheory
