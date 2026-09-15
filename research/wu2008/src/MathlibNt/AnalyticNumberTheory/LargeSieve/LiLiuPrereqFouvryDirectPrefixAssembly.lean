import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryDirectJoinedTerms
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryDirectAnalyticLosses

/-! Finite assembly of actual coprime prefixes. These assembly lemmas explicitly
consume cell bounds; the analytic producer must instantiate them. -/
noncomputable section
open Classical Finset
namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

theorem direct_prefix_coprime_commute (x S : ℝ) (N : Finset ℕ)
    (U : Finset (WExtractedTuple × ℤ)) (c : Finset (ℕ × ℕ)) (cap : Fin 5 → ℕ) :
    wAnalyticPrefix (wCoprimeFiber x N S U c) cap =
      wCoprimeFiber x N S (wAnalyticPrefix U cap) c := by
  ext t
  simp only [wAnalyticPrefix, wCoprimeFiber, mem_filter]
  tauto

theorem direct_block_prefix_assembly
    (x S : ℝ) (N : Finset ℕ) (U : Finset (WExtractedTuple × ℤ))
    (K : WExtractedKey) (j : Fin 5 → ℕ) (positive : Bool)
    (β c₁ γ ζ : ℕ → ℝ) (a : ℤ) (B C : ℝ)
    (hcard : (((wAnalyticDyadicBlock U j positive).image (wCoprimeLabel x N S)).card : ℝ) ≤ C)
    (hB : 0 ≤ B)
    (hcell : ∀ c ∈ (wAnalyticDyadicBlock U j positive).image (wCoprimeLabel x N S),
      ∀ cap ∈ _root_.LiLiuPrereqFouvry.Rectangle.box (wAnalyticBoxLo j) (wAnalyticBoxHi j),
      wBlockAmplitude K j *
        ‖wAnalyticPrefixSum (wCoprimeFiber x N S (wAnalyticDyadicBlock U j positive) c)
          β c₁ γ ζ a cap‖ ≤ B) :
    wBlockAmplitude K j * wAnalyticBlockPrefixMax (wAnalyticDyadicBlock U j positive)
      j β c₁ γ ζ a ≤ C*B := by
  have hA : 0 ≤ wBlockAmplitude K j := by unfold wBlockAmplitude; positivity
  apply (mul_le_mul_of_nonneg_left
    (wAnalyticBlockPrefixMax_le_coprime x N S _ j β c₁ γ ζ a) hA).trans
  unfold wCoprimeBlockPrefixMajorant
  rw [mul_sum]
  calc
    _ ≤ ∑ _c ∈ (wAnalyticDyadicBlock U j positive).image (wCoprimeLabel x N S), B := by
      apply sum_le_sum
      intro c hc
      obtain ⟨cap, hcap, he⟩ := wAnalyticBlockPrefixMax_attained
        (wCoprimeFiber x N S (wAnalyticDyadicBlock U j positive) c) j β c₁ γ ζ a
      rw [he]
      exact hcell c hc cap hcap
    _ = (((wAnalyticDyadicBlock U j positive).image (wCoprimeLabel x N S)).card : ℝ)*B := by simp
    _ ≤ C*B := mul_le_mul_of_nonneg_right hcard hB

theorem direct_key_prefix_assembly
    (U : Finset (WExtractedTuple × ℤ)) (K : WExtractedKey)
    (β c₁ γ ζ : ℕ → ℝ) (a : ℤ) (B D : ℝ)
    (hB : 0 ≤ B) (hD : ((U.image wAnalyticDyadicKey).card : ℝ) ≤ D)
    (hblock : ∀ j ∈ U.image wAnalyticDyadicKey, ∀ positive : Bool,
      wBlockAmplitude K j * wAnalyticBlockPrefixMax (wAnalyticDyadicBlock U j positive)
        j β c₁ γ ζ a ≤ B) :
    wAnalyticKeyPrefixMajorant U K β c₁ γ ζ a ≤ 2*D*B := by
  unfold wAnalyticKeyPrefixMajorant
  calc
    _ ≤ ∑ _j ∈ U.image wAnalyticDyadicKey, (B+B) := by
      apply sum_le_sum
      intro j hj
      rw [mul_add]
      exact add_le_add (hblock j hj true) (hblock j hj false)
    _ = 2*((U.image wAnalyticDyadicKey).card : ℝ)*B := by simp; ring
    _ ≤ 2*D*B := by gcongr

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
