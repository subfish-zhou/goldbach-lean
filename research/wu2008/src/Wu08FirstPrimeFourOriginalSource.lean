import Wu08FirstPrimeFourGlobal
import MathlibNt.Wu2008DoubleSieve.TruncatedFourPayment
import Wu08RecoveredInputs

noncomputable section
open Finset Real
open scoped Classical
open Wu2008DoubleSieve
namespace Wu08FirstPrimeFour

/-- A literal original-source amount; all remaining costs are functions of the
actual finite carriers. No smaller integral is substituted by fiat. -/
def originalPairAmount (N : ℕ) (ξ ρ δ η : ℝ) (A : ℕ)
    (P : Bool → Key → Finset ℕ) (z : Bool → Key → ℝ) : ℝ :=
  ((large N false).card : ℝ)+(large N true).card+
  (smallPrefix N false ξ).card+(smallPrefix N true ξ).card+
  (∑ k ∈ occupied N false ξ ρ, cellAmount N false ξ ρ δ η (z false k) A (P false k) k)+
  (∑ k ∈ occupied N true ξ ρ, cellAmount N true ξ ρ δ η (z true k) A (P true k) k)

/-- The new finite switching source reaches the ORIGINAL two negative count
slots with the pre-existing exceptional payment, each used exactly once.
This is not yet the assertion original10+original11+epsilon. -/
theorem original_pair_global_level_upper (A : ℕ) {ξ ε δ η κ : ℝ}
    (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) (hε : 0 < ε)
    (hεa : ε < truncatedSixthLowerAlpha) (hεδ : ε < δ) (hδ : δ < 1/2)
    (hη : 0 < η) (hηu : η < 1/8) (hκ : 0 < κ) :
    ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ (N : ℝ) → Even N → ∀ ρ : ℝ,
      1 < ρ → ρ ≤ 5/4 → ∀ P : Bool → Key → Finset ℕ, ∀ z : Bool → Key → ℝ,
      (∀ e k, k ∈ occupied N e ξ ρ → ∀ p ∈ P e k, p.Prime) →
      (∀ e k, k ∈ occupied N e ξ ρ → ∀ p ∈ P e k, p.Coprime N) →
      (∀ e k, k ∈ occupied N e ξ ρ → ∀ p ∈ P e k, (p : ℝ) < z e k) →
      (TruncatedFourPhysical.Q10 N : ℝ)+(TruncatedFourPhysical.Q11 N : ℝ) ≤
        originalPairAmount N ξ ρ δ η A P z+κ*wuSingularSeries N*N/log N^2 := by
  obtain ⟨Ns,hs⟩ := small_global_level_upper A hξ hξ1 hε hεa hεδ hδ hη hηu
  obtain ⟨T,_,ht⟩ := TruncatedFourPhysical.original_tenth_eleventh_upper hκ
  refine ⟨max Ns (T : ℝ),?_⟩
  intro N hN he ρ hρ hρu P z hP hPN hcut
  have hNs := (le_max_left _ _).trans hN
  have hT : T ≤ N := by exact_mod_cast (le_max_right _ _).trans hN
  have h10 := hs N hNs false ρ hρ hρu (P false) (z false) (hP false) (hPN false) (hcut false)
  have h11 := hs N hNs true ρ hρ hρu (P true) (z true) (hP true) (hPN true) (hcut true)
  have hraw := ht N hT he
  have hsplit10 : ((small N false).card : ℝ)+(large N false).card =
      (TruncatedFourPhysical.Physical10 N).card := by exact_mod_cast original_card_split N false
  have hsplit11 : ((small N true).card : ℝ)+(large N true).card =
      (TruncatedFourPhysical.Physical11 N).card := by exact_mod_cast original_card_split N true
  unfold originalPairAmount
  linarith only [h10,h11,hraw,hsplit10,hsplit11]

/-- Exact sign gate at the same two negative slots. The residual amount is
kept, so this does not manufacture a new ordinaryP2 coefficient. -/
theorem negative_pair_of_actual_upper {N : ℕ} {B : ℝ}
    (h : (TruncatedFourPhysical.Q10 N : ℝ)+(TruncatedFourPhysical.Q11 N : ℝ) ≤ B) :
    -B ≤ -(TruncatedFourPhysical.Q10 N : ℝ)-(TruncatedFourPhysical.Q11 N : ℝ) := by
  linarith only [h]

#print axioms original_pair_global_level_upper
#print axioms negative_pair_of_actual_upper
#check Wu08RecoveredInputs.original10_literal
#check Wu08RecoveredInputs.original11_literal
#check PositiveTwoPayment.ordinary_P2
end Wu08FirstPrimeFour
