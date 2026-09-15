import MathlibNt.Wu2008DoubleSieve.ReboxingBlockSum
import MathlibNt.Wu2008DoubleSieve.ReboxingBoundaryR1
import MathlibNt.Wu2008DoubleSieve.ReboxingRawTransport

/-!
# The actual Buchstab sum consumes both R1 and R2

The strict selected-prime carrier is unchanged by adjoining that prime
to the sifting modulus. The original P(dN) window is majorized by the
literal geometric blocks plus the terminal R1, with all tuple weights.
-/

namespace Wu2008DoubleSieve

open Finset Real
open scoped Classical

theorem reboxing_source_count_prime_modulus_eq (N d : ℕ) {p : ℕ} (hp : p.Prime) :
    sourceSieveCount N (d * p) ((d * p) * N) p =
      sourceSieveCount N (d * p) (d * N) p := by
  have hprod : ordinarySievePrimeProduct ((d * p) * N) p =
      ordinarySievePrimeProduct (d * N) p := by
    unfold ordinarySievePrimeProduct
    rw [show (d * p) * N = p * (d * N) by ring,
      primeWindow_mul_of_prime_above (d * N) hp le_rfl]
  have hc : sourceSieveCarrier N (d * p) ((d * p) * N) p =
      sourceSieveCarrier N (d * p) (d * N) p := by
    ext n
    simp only [sourceSieveCarrier, mem_filter, sifted_iff_product_coprime, hprod]
  exact congrArg (fun S : Finset ℕ => (S.card : ℤ)) hc

/-- The finite source (3.15) majorant, before any analytic payment.
No equality between P(N) and P(dN) is asserted. -/
theorem reboxingRawPrimeSum_le_blocks_add_R1 {i k N : ℕ} {δ Δ s t : ℝ}
    {V : Fin i → ℝ} (hN : 4 ≤ N)
    (hb : wuSourceBox k δ N i Δ V) (ht : 0 < t) (r : ℕ) :
    reboxingRawPrimeSum true N δ s t (convolutionWuWindows N Δ V) ≤
      reboxingGeometricRaw N δ Δ V t r + reboxingR1 N δ Δ V s t r := by
  let W := convolutionWuWindows N Δ V
  let Q := (N : ℝ) ^ (1 / 2 - δ)
  let q := Q / (∏ l, V l)
  have hNreal : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hΔ : 1 < Δ := by
    have hL := log_pos hNreal
    have hpow := rpow_pos_of_pos hL (-4 : ℝ)
    linarith [hb.2.1]
  have hV : ∀ j, 0 < V j := fun j =>
    (rpow_pos_of_pos (by linarith : (0 : ℝ) < N) _).trans_le (hb.2.2.2.2.1 j)
  have hQ : 0 < Q := rpow_pos_of_pos (by linarith) _
  have hq : 0 < q := div_pos hQ (prod_pos (fun j _ => hV j))
  have hpart := reboxingAlpha_convolution_sum_partition (t := t) hq hΔ N r W
    (fun d p => (sourceSieveCount N (d * p) ((d * p) * N) p : ℝ))
  change _ = reboxingGeometricRaw N δ Δ V t r at hpart
  rw [← hpart]
  unfold reboxingRawPrimeSum reboxingR1 reboxingBoundaryCount
  simp only [if_true, W, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro d hd
  rw [← mul_add]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  let A := primeWindow N (reboxingAlpha q Δ t 0) (reboxingAlpha q Δ t r)
  let B := primeWindow N (reboxingAlpha q Δ t r) (wuLocalCutoff N δ d s)
  let S := primeWindow (d * N) (wuLocalCutoff N δ d t) (wuLocalCutoff N δ d s)
  let F : ℕ → ℝ := fun p => sourceSieveCount N (d * p) ((d * p) * N) p
  have hlo := (reboxing_support_cutoff_bounds hQ.le (by linarith : 0 < Δ) hV ht hd).1
  have hsub : S ⊆ A ∪ B := by
    intro p hp
    obtain ⟨hpp, hpc, hpl, hpu⟩ := mem_primeWindow.mp hp
    have hpN := (Nat.coprime_mul_iff_right.mp hpc).2
    have hlow : reboxingAlpha q Δ t 0 ≤ (p : ℝ) := by
      rw [reboxingAlpha_zero]
      exact hlo.trans hpl
    by_cases hc : (p : ℝ) < reboxingAlpha q Δ t r
    · exact mem_union_left _ (mem_primeWindow.mpr ⟨hpp, hpN, hlow, hc⟩)
    · exact mem_union_right _ (mem_primeWindow.mpr ⟨hpp, hpN, le_of_not_gt hc, hpu⟩)
  have hdis : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro p hp hp'
    have h1 := (mem_primeWindow.mp hp).2.2.2
    have h2 := (mem_primeWindow.mp hp').2.2.1
    linarith
  have hsum : (∑ p ∈ S, F p) ≤ (∑ p ∈ A, F p) + ∑ p ∈ B, F p := by
    rw [← Finset.sum_union hdis]
    apply Finset.sum_le_sum_of_subset_of_nonneg hsub
    intro p _ _
    dsimp [F]
    simp only [sourceSieveCount, Int.cast_natCast]
    positivity
  have hBsum : (∑ p ∈ B, F p) =
      ∑ p ∈ B, (sourceSieveCount N (d * p) (d * N) p : ℝ) := by
    apply Finset.sum_congr rfl
    intro p hp
    change (sourceSieveCount N (d * p) ((d * p) * N) p : ℝ) = _
    rw [reboxing_source_count_prime_modulus_eq N d (mem_primeWindow.mp hp).1]
  rw [hBsum] at hsum
  exact hsum

/-- One threshold before N0 and every box, with one epsilon ledger for
the genuine R1 and R2. The main term still retains exact inserted Theta;
prime normalization and integration are the next consumer. -/
theorem reboxingRawPrimeSum_upper_geometric (k : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N0 : ℕ, T ≤ N0 → ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → t ≤ 10 →
      let q := (N : ℝ) ^ (1 / 2 - δ) / (∏ l, V l)
      ∃ r : ℕ, reboxingAlpha q Δ t r ≤ q ^ (1 / s) ∧
        q ^ (1 / s) < reboxingAlpha q Δ t (r + 1) ∧
        reboxingRawPrimeSum true N δ s t (convolutionWuWindows N Δ V) ≤
          reboxingGeometricMain true k N0 N δ Δ V t r
            (fun j => reboxingS1 q Δ t (j + 1)) +
          ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  obtain ⟨T1, hT14, hupper⟩ := reboxingGeometricRaw_upper_s1 k hδ hδhi (half_pos hε)
  obtain ⟨T2, hR1⟩ := reboxingR1_relative k hδ hδhi (half_pos hε)
  refine ⟨max T1 T2, hT14.trans (le_max_left _ _), ?_⟩
  intro N0 hN0 N hN he i Δ V hb s t hs hst ht
  have h1 : T1 ≤ N0 := (le_max_left _ _).trans hN0
  have h2 : T2 ≤ N := (le_max_right _ _).trans (hN0.trans hN)
  have hN4 : 4 ≤ N := hT14.trans (h1.trans hN)
  obtain ⟨r, hrlo, hrhi, hmain⟩ := hupper N0 h1 N hN he i Δ V hb s t hs hst ht
  refine ⟨r, hrlo, hrhi, ?_⟩
  have hfinite := reboxingRawPrimeSum_le_blocks_add_R1 (s := s) hN4 hb
    (show 0 < t by linarith) r
  have herror := (hR1 N h2 he i Δ V hb s t hs hst ht r ⟨hrlo, hrhi⟩).2
  linarith

end Wu2008DoubleSieve
