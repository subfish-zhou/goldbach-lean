import MathlibNt.SieveTheory.LiLiuFouvryG9RectanglePrefixPNT

noncomputable section
open Finset
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- Exact pair-fibre decomposition of the actual rectangle mass. -/
theorem fouvryG9WeightedPrefix_mass_fibres {N : ℕ} {e ρ : ℝ}
    (hN : 1 ≤ N) (hρ : 1 < ρ) (hρu : ρ ≤ 5/4)
    (k : ℕ × ℕ × ℕ) (hbig : 3 ≤ ρ^k.1)
    (hne : (fouvryG9GridCell N e ρ k).Nonempty) :
    fouvryG9RectangleMass N ρ k =
      ∑ rs ∈ fouvryG9RelaxedPairs N ρ,
        ((fouvryG9RectanglePrefixThirds N ρ rs.1 rs.2 k).card : ℝ) := by
  classical
  rw [fouvryG9RectanglePrefix_mass_eq_card hN hρ hρu k hbig hne]
  have hc : (fouvryG9LongShortLabels N ρ k ×ˢ fouvryG9LongLabels N ρ k).card =
      ((fouvryG9RelaxedPairs N ρ).sigma
        (fun rs => fouvryG9RectanglePrefixThirds N ρ rs.1 rs.2 k)).card := by
    apply card_bij (fun q _ => ⟨(q.1, q.2.1), q.2.2⟩)
    · intro q hq
      obtain ⟨hn, hz⟩ := mem_product.mp hq
      apply mem_sigma.mpr
      refine ⟨(fouvryG9RectanglePrefix_pair_and_prefix hρ hne hn hz).1, ?_⟩
      apply mem_filter.mpr
      exact ⟨(mem_product.mp (mem_filter.mp hz).1).2, hn, hz⟩
    · intro q hq r hr he
      have h1 : (q.1, q.2.1) = (r.1, r.2.1) := congrArg Sigma.fst he
      have h2 : q.2.2 = r.2.2 := congrArg (fun x : (rs : ℕ × ℕ) × ℕ => x.2) he
      have hn : q.1 = r.1 := congrArg (fun p : ℕ × ℕ => p.1) h1
      have hs : q.2.1 = r.2.1 := congrArg (fun p : ℕ × ℕ => p.2) h1
      exact Prod.ext hn (Prod.ext hs h2)
    · intro q hq
      obtain ⟨_, ht⟩ := mem_sigma.mp hq
      obtain ⟨_, hn, hz⟩ := mem_filter.mp ht
      exact ⟨(q.1.1, q.1.2, q.2), mem_product.mpr ⟨hn, hz⟩, rfl⟩
  rw [hc, card_sigma, Nat.cast_sum]

/-- Signed cell weights are transported locally to a nonnegative pair weight.
The occupied third-label families are paid by one prime prefix per pair. -/
theorem fouvryG9WeightedPrefix_le_primePi {N : ℕ} {e ρ : ℝ}
    (hN : 1 ≤ N) (hρ : 1 < ρ) (hρu : ρ ≤ 5/4)
    (hbig : ∀ k ∈ fouvryG9GridUsed N e ρ, 3 ≤ ρ^k.1)
    (W : (ℕ × ℕ × ℕ) → ℝ) (V : ℕ → ℝ)
    (hV : ∀ rs ∈ fouvryG9RelaxedPairs N ρ, 0 ≤ V rs.1)
    (hWV : ∀ k ∈ fouvryG9GridUsed N e ρ,
      ∀ n ∈ fouvryG9LongShortLabels N ρ k, W k ≤ V n) :
    (∑ k ∈ fouvryG9GridUsed N e ρ, W k * fouvryG9RectangleMass N ρ k) ≤
      ∑ rs ∈ fouvryG9RelaxedPairs N ρ,
        V rs.1 * LiLiuPrereqBuchstab.primePi (ρ^3*(N : ℝ)/((rs.1 : ℝ)*rs.2)) := by
  classical
  calc
    _ = ∑ k ∈ fouvryG9GridUsed N e ρ,
        ∑ rs ∈ fouvryG9RelaxedPairs N ρ,
          W k * ((fouvryG9RectanglePrefixThirds N ρ rs.1 rs.2 k).card : ℝ) := by
      apply sum_congr rfl
      intro k hk
      rw [fouvryG9WeightedPrefix_mass_fibres hN hρ hρu k (hbig k hk)
        (fouvryG9GridCell_nonempty_iff.mpr hk), mul_sum]
    _ ≤ ∑ k ∈ fouvryG9GridUsed N e ρ,
        ∑ rs ∈ fouvryG9RelaxedPairs N ρ,
          V rs.1 * ((fouvryG9RectanglePrefixThirds N ρ rs.1 rs.2 k).card : ℝ) := by
      apply sum_le_sum
      intro k hk
      apply sum_le_sum
      intro rs _
      by_cases ht : (fouvryG9RectanglePrefixThirds N ρ rs.1 rs.2 k).Nonempty
      · obtain ⟨t, ht⟩ := ht
        have hn := (mem_filter.mp ht).2.1
        exact mul_le_mul_of_nonneg_right (hWV k hk rs.1 hn) (Nat.cast_nonneg _)
      · rw [not_nonempty_iff_eq_empty.mp ht]
        simp
    _ = ∑ rs ∈ fouvryG9RelaxedPairs N ρ,
        V rs.1 * ((∑ k ∈ fouvryG9GridUsed N e ρ,
          (fouvryG9RectanglePrefixThirds N ρ rs.1 rs.2 k).card : ℕ) : ℝ) := by
      rw [sum_comm]
      apply sum_congr rfl
      intro rs _
      rw [Nat.cast_sum, mul_sum]
    _ ≤ _ := by
      apply sum_le_sum
      intro rs hrs
      exact mul_le_mul_of_nonneg_left
        (fouvryG9RectanglePrefix_thirds_le_primePi hρ rs.1 rs.2) (hV rs hrs)

#print axioms fouvryG9WeightedPrefix_mass_fibres
#print axioms fouvryG9WeightedPrefix_le_primePi
end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
