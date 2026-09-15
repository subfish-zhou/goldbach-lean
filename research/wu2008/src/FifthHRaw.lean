import MathlibNt.Wu2008DoubleSieve.SecondFunctionalSmallDelta
import MathlibNt.Wu2008DoubleSieve.FifthPairProducer

namespace Wu2008DoubleSieve
open Finset Real
open scoped Classical

/-- Transport the full unscaled dN-source, not a squarefree surrogate. -/
theorem fifthH_source_to_ordinary {N d : ℕ} {z w : ℝ}
    (hselected : Sifted N d z) (hzw : z ≤ w) :
    sourceSieveCount N d (d * N) w ≤ sieveCount N d N z := by
  apply Int.ofNat_le.mpr
  apply card_le_card
  intro p hp
  obtain ⟨hp, hprime, hd, hs⟩ := mem_filter.mp hp
  refine mem_filter.mpr ⟨hp, hprime, hd, ?_⟩
  intro q hq hc hz hdiv
  have hqd : ¬ q ∣ d := hselected q hq hc hz
  have hcop : q.Coprime (d * N) :=
    (hq.coprime_iff_not_dvd.mpr hqd).mul_right hc
  exact hs q hq hcop (hz.trans_le hzw)
    (hdiv.trans (Nat.div_dvd_of_dvd hd))

/-- A literal two-window product gives the required moving-cutoff direction. -/
theorem fifthH_pair_cutoff {N : ℕ} {δ s z Δ : ℝ} {V : Fin 2 → ℝ}
    (hs : 0 < s) (hz : 0 ≤ z)
    (hbudget : z ^ s * (V 0 * V 1) ≤ (N : ℝ) ^ (1 / 2 - δ))
    {t : Fin 2 → ℕ} (ht : t ∈ Fintype.piFinset (convolutionWuWindows N Δ V)) :
    z ≤ wuLocalCutoff N δ (∏ j, t j) s := by
  have h0 := mem_convolutionWuWindows.mp ((Fintype.mem_piFinset.mp ht) 0)
  have h1 := mem_convolutionWuWindows.mp ((Fintype.mem_piFinset.mp ht) 1)
  have ht0 : (0 : ℝ) < t 0 := by exact_mod_cast h0.1.pos
  have ht1 : (0 : ℝ) < t 1 := by exact_mod_cast h1.1.pos
  have hprod : (0 : ℝ) < (∏ j, t j : ℕ) := by
    simp only [Fin.prod_univ_two, Nat.cast_mul]
    exact mul_pos ht0 ht1
  have hle : ((∏ j, t j : ℕ) : ℝ) ≤ V 0 * V 1 := by
    simp only [Fin.prod_univ_two, Nat.cast_mul]
    exact mul_le_mul h0.2.2.2.le h1.2.2.2.le ht1.le (ht0.trans h0.2.2.2).le
  unfold wuLocalCutoff
  simp only [one_div] at hbudget ⊢
  apply (le_rpow_inv_iff_of_pos hz (div_nonneg (rpow_nonneg (Nat.cast_nonneg N) _) hprod.le) hs).2
  apply (le_div_iff₀ hprod).2
  exact (mul_le_mul_of_nonneg_left hle (rpow_nonneg hz s)).trans hbudget

/-- The fixed-s actual h gain is consumed by the original fixed-cutoff pair count.
The threshold precedes all admissible moving boxes; hypotheses after N are
only source/endpoint geometry, never a sieve estimate. Tuple multiplicity is literal. -/
theorem fifthH_pair_raw {δ s ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hs : 1 ≤ s) (hs10 : s ≤ 10)
    (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (Δ : ℝ) (V : Fin 2 → ℝ), wuSourceBox 2 δ N 2 Δ V →
      (∀ j, (N : ℝ) ^ truncatedSixthLowerAlpha ≤ V j / Δ) →
      ((N : ℝ) ^ truncatedSixthLowerAlpha) ^ s * (V 0 * V 1) ≤
        (N : ℝ) ^ (1 / 2 - δ) →
      (wuLowerCoefficient s + (wuImprovementLimit false δ s - ε)) *
        boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) ≤
      ∑ t ∈ Fintype.piFinset (convolutionWuWindows N Δ V),
        (sieveCount N (∏ j, t j) N ((N : ℝ) ^ truncatedSixthLowerAlpha) : ℝ) := by
  obtain ⟨M, hM⟩ := wuImprovementLimit_sub_mem false 1 hδ hδhi hs hs10 hε
  refine ⟨max 4 M, le_max_left _ _, ?_⟩
  intro N hN he Δ V hb hz hbudget
  have h := hM N ((le_max_right _ _).trans hN) ((le_max_left _ _).trans hN)
    he 2 Δ V hb
  change (wuLowerCoefficient s + (wuImprovementLimit false δ s - ε)) *
    boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) ≤
    wuBoxPhi N δ (convolutionWuWindows N Δ V) s at h
  refine h.trans ?_
  rw [wuBoxPhi_eq_tuple_sum]
  apply sum_le_sum
  intro t ht
  have h0 := mem_convolutionWuWindows.mp ((Fintype.mem_piFinset.mp ht) 0)
  have h1 := mem_convolutionWuWindows.mp ((Fintype.mem_piFinset.mp ht) 1)
  have hselected : Sifted N (∏ j, t j) ((N : ℝ) ^ truncatedSixthLowerAlpha) := by
    rw [Fin.prod_univ_two, sifted_mul_iff]
    exact ⟨sifted_prime_of_le h0.1 ((hz 0).trans h0.2.2.1),
      sifted_prime_of_le h1.1 ((hz 1).trans h1.2.2.1)⟩
  exact_mod_cast fifthH_source_to_ordinary hselected
    (fifthH_pair_cutoff (by linarith) (rpow_nonneg (Nat.cast_nonneg N) _) hbudget ht)

/-- Strict positive improvement is actually paid at every fixed s in the seed domain.
No numerical table and no delta-continuity assertion enter this statement. -/
theorem fifthH_pair_raw_positive {δ s : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 1000) (hs : 2 ≤ s) (hsHi : s < 7 / 2) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (Δ : ℝ) (V : Fin 2 → ℝ), wuSourceBox 2 δ N 2 Δ V →
      (∀ j, (N : ℝ) ^ truncatedSixthLowerAlpha ≤ V j / Δ) →
      ((N : ℝ) ^ truncatedSixthLowerAlpha) ^ s * (V 0 * V 1) ≤
        (N : ℝ) ^ (1 / 2 - δ) →
      (wuLowerCoefficient s + (7 / 2 - s) / 750) *
        boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) ≤
      ∑ t ∈ Fintype.piFinset (convolutionWuWindows N Δ V),
        (sieveCount N (∏ j, t j) N ((N : ℝ) ^ truncatedSixthLowerAlpha) : ℝ) := by
  have hgap := SecondFunctionalSmallDelta.h_strict hδ hδhi hs hsHi
  have h := fifthH_pair_raw hδ (by linarith) (by linarith : 1 ≤ s)
    (by linarith : s ≤ 10) (sub_pos.mpr hgap)
  simpa only [sub_sub_cancel] using h

end Wu2008DoubleSieve
