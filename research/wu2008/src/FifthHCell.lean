import FifthHRaw

namespace Wu2008DoubleSieve
open Finset Real
open scoped Classical

/-- Exact reversal of the descending source tuple into the original (p,q) label. -/
theorem fifthH_tuple_pair_sum (N : ℕ) (Δ : ℝ) (V : Fin 2 → ℝ) (z : ℝ) :
    (∑ t ∈ Fintype.piFinset (convolutionWuWindows N Δ V),
      (sieveCount N (∏ j, t j) N z : ℝ)) =
    ∑ t ∈ (primeWindow N (V 1 / Δ) (V 1)) ×ˢ
      (primeWindow N (V 0 / Δ) (V 0)), (sieveCount N (t.1 * t.2) N z : ℝ) := by
  apply sum_bij (fun t _ => (t 1, t 0))
  · intro t ht
    exact mem_product.mpr ⟨Fintype.mem_piFinset.mp ht 1, Fintype.mem_piFinset.mp ht 0⟩
  · intro t ht u hu htu
    have h0 : t 0 = u 0 := congrArg Prod.snd htu
    have h1 : t 1 = u 1 := congrArg Prod.fst htu
    funext j
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl
    · exact h0
    · exact h1
  · intro t ht
    refine ⟨![t.2, t.1], ?_, by simp⟩
    apply Fintype.mem_piFinset.mpr
    intro j
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl
    · simpa [convolutionWuWindows] using (mem_product.mp ht).2
    · simpa [convolutionWuWindows] using (mem_product.mp ht).1
  · intro t ht
    simp only [Fin.prod_univ_two, mul_comm]

/-- A source cell stays in the full original F5 triangle, including lower endpoints. -/
theorem fifthH_cell_subset {N : ℕ} {Δ : ℝ} {V : Fin 2 → ℝ}
    (hz : ∀ j, (N : ℝ) ^ truncatedSixthLowerAlpha ≤ V j / Δ)
    (hsep : V 1 ≤ V 0 / Δ)
    (hhi : V 0 ≤ (N : ℝ) ^ truncatedSixthLowerBeta) :
    (primeWindow N (V 1 / Δ) (V 1)) ×ˢ
      (primeWindow N (V 0 / Δ) (V 0)) ⊆ fifthPairLabels N := by
  intro t ht
  obtain ⟨hp, hq⟩ := mem_product.mp ht
  have hp' := mem_primeWindow.mp hp
  have hq' := mem_primeWindow.mp hq
  have hpq : (t.1 : ℝ) < t.2 := hp'.2.2.2.trans_le (hsep.trans hq'.2.2.1)
  apply mem_filter.mpr
  refine ⟨mem_product.mpr ⟨?_, ?_⟩, by exact_mod_cast hpq⟩
  · exact mem_primeWindow.mpr ⟨hp'.1, hp'.2.1, (hz 1).trans hp'.2.2.1,
      hpq.trans (hq'.2.2.2.trans_le hhi)⟩
  · exact mem_primeWindow.mpr ⟨hq'.1, hq'.2.1, (hz 0).trans hq'.2.2.1,
      hq'.2.2.2.trans_le hhi⟩

/-- Fixed delta, fixed s, then one T for every legal original ordered cell.
The actual limiting gain is used inside its raw source comparison, not added
onto a pre-existing classical count lower bound. -/
theorem fifthH_original_cell_raw {δ s ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hs : 1 ≤ s) (hs10 : s ≤ 10)
    (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (Δ : ℝ) (V : Fin 2 → ℝ), wuSourceBox 2 δ N 2 Δ V →
      (∀ j, (N : ℝ) ^ truncatedSixthLowerAlpha ≤ V j / Δ) →
      V 1 ≤ V 0 / Δ → V 0 ≤ (N : ℝ) ^ truncatedSixthLowerBeta →
      ((N : ℝ) ^ truncatedSixthLowerAlpha) ^ s * (V 0 * V 1) ≤
        (N : ℝ) ^ (1 / 2 - δ) →
      let S := (primeWindow N (V 1 / Δ) (V 1)) ×ˢ
        (primeWindow N (V 0 / Δ) (V 0))
      S ⊆ fifthPairLabels N ∧
      (wuLowerCoefficient s + (wuImprovementLimit false δ s - ε)) *
        boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) ≤
        ∑ t ∈ S, (sieveCount N (t.1 * t.2) N
          ((N : ℝ) ^ truncatedSixthLowerAlpha) : ℝ) := by
  obtain ⟨T, hT4, hT⟩ := fifthH_pair_raw hδ hδhi hs hs10 hε
  refine ⟨T, hT4, ?_⟩
  intro N hN he Δ V hb hz hsep hhi hbudget
  refine ⟨fifthH_cell_subset hz hsep hhi, ?_⟩
  have h := hT N hN he Δ V hb hz hbudget
  rwa [fifthH_tuple_pair_sum] at h

end Wu2008DoubleSieve
