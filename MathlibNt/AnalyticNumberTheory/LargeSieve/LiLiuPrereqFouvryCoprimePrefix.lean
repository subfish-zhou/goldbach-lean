import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryActualCoprimePartition
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryAnalyticPartialSummation

/-!
# The actual coprimality partition back at the original distribution error

Only the triangle inequality between Lemma 7 cells is used. Every cell
contains the original signed coefficients, tuple multiplicities, arithmetic
phases and remaining filters. This is not an unweighted Weil estimate.
-/

noncomputable section
open Classical Finset Filter

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

theorem wAnalyticPrefixSum_eq_coprimeFibers
    (x : ℝ) (N : Finset ℕ) (S : ℝ) (B : Finset (WExtractedTuple × ℤ))
    (β c₁ γ ζ : ℕ → ℝ) (a : ℤ) (cap : Fin 5 → ℕ) :
    wAnalyticPrefixSum B β c₁ γ ζ a cap =
      ∑ c ∈ B.image (wCoprimeLabel x N S),
        wAnalyticPrefixSum (wCoprimeFiber x N S B c) β c₁ γ ζ a cap := by
  have he := sum_fiberwise_of_maps_to
    (s := wAnalyticPrefix B cap) (t := B.image (wCoprimeLabel x N S))
    (g := wCoprimeLabel x N S)
    (fun t ht => mem_image.mpr ⟨t, (mem_filter.mp ht).1, rfl⟩)
    (fun t => (wExtractedCoefficient β c₁ γ ζ t.1 : ℂ) *
      wExtractedArithmeticPhase a t.2 t.1)
  unfold wAnalyticPrefixSum
  rw [← he]
  apply sum_congr rfl
  intro c _
  apply sum_congr
  · ext t
    simp only [wAnalyticPrefix, wCoprimeFiber, mem_filter]
    tauto
  · intro _ _
    rfl

def wCoprimeBlockPrefixMajorant (x : ℝ) (N : Finset ℕ) (S : ℝ)
    (B : Finset (WExtractedTuple × ℤ)) (j : Fin 5 → ℕ)
    (β c₁ γ ζ : ℕ → ℝ) (a : ℤ) : ℝ :=
  ∑ c ∈ B.image (wCoprimeLabel x N S),
    wAnalyticBlockPrefixMax (wCoprimeFiber x N S B c) j β c₁ γ ζ a


/-- The attained prefix is split into genuine coprimality cells. Different
cells may choose different attaining caps, which only increases this bound. -/
theorem wAnalyticBlockPrefixMax_le_coprime
    (x : ℝ) (N : Finset ℕ) (S : ℝ) (B : Finset (WExtractedTuple × ℤ))
    (j : Fin 5 → ℕ) (β c₁ γ ζ : ℕ → ℝ) (a : ℤ) :
    wAnalyticBlockPrefixMax B j β c₁ γ ζ a ≤
      wCoprimeBlockPrefixMajorant x N S B j β c₁ γ ζ a := by
  obtain ⟨cap, hcap, he⟩ := wAnalyticBlockPrefixMax_attained B j β c₁ γ ζ a
  rw [he, wAnalyticPrefixSum_eq_coprimeFibers x N S]
  exact (norm_sum_le _ _).trans
    (sum_le_sum (fun c _ => wAnalyticPrefixSum_norm_le_max
      (wCoprimeFiber x N S B c) j β c₁ γ ζ a cap hcap))


end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
