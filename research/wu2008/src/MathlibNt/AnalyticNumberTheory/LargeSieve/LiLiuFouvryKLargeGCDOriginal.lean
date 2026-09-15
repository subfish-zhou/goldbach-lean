import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuFouvryKDivisor

noncomputable section
open Classical Finset
namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

/-- The fixed shift enlargement changes only the constant in the original
large-gcd estimate. The pair carrier and its cutoff remain unchanged. -/
theorem wMaskedOriginal_abs_le_largeGCD_kscale
    {k : ℕ} (hk : 1 ≤ k) (j : ℕ) {ε Cscale : ℝ}
    (hε : 0 < ε) (hCscale : 1 ≤ Cscale) :
    ∃ C : ℝ, 0 < C ∧ ∀ M T Y x : ℝ,
      1 ≤ M → 1 ≤ T → 0 < Y → 1 ≤ x → M * T ≤ x →
      ∀ N Q : Finset ℕ, N ⊆ Ioc 0 ⌊T⌋₊ →
      ∀ β c : ℕ → ℝ, (∀ n ∈ N, |β n| ≤ (fouvryTau k n : ℝ)) →
        (∀ q ∈ Q, |c q| ≤ (fouvryTau j q : ℝ)) →
      ∀ a : ℤ, |(a : ℝ)| ≤ Cscale * x →
      (∀ n ∈ N, β n ≠ 0 → ¬(n : ℤ) ∣ a) →
      ∀ P : WOriginalTuple → Prop,
        (∀ t ∈ wOriginalTuples N Q a, P t → Y < (t.2.1.gcd t.2.2 : ℝ)) →
      |wMaskedOriginal M N Q β c a P| ≤ C * M * x ^ ε *
        (T ^ 2 * (1 + Real.log T) ^ (k ^ 2 - 1) *
          Real.sqrt ((1 + Real.log T) / Y)) := by
  obtain ⟨C, hC, hb⟩ := wMaskedOriginal_abs_le_largeGCD_pair_mass_kscale j hε hCscale
  refine ⟨C, hC, ?_⟩
  intro M T Y x hM hT hY hx hMT N Q hN β c hβ hc a ha hs P hP
  exact (hb M T x hM hT hx hMT N Q hN β c hc a ha hs Y P hP).trans
    (mul_le_mul_of_nonneg_left (sum_abs_largeGCDPairs_le hk hT hY N hN β hβ)
      (by positivity))

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
