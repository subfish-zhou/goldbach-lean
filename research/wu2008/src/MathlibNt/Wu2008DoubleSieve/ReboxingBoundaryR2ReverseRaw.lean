import MathlibNt.Wu2008DoubleSieve.ReboxingBoundaryR2ReverseBlock
import MathlibNt.Wu2008DoubleSieve.ReboxingRawUpper

/-!
# The actual lower raw Buchstab sum consumes reverse R2

The geometric sum can extend below the actual fibre's lower endpoint.
This left raw boundary is exactly the already paid `R1(t,t,0)`.
After its removal the separate raw `P(N)/P(dN)` transport is paid.
Thus all three errors are consumed before normalizing the block mains.
-/

namespace Wu2008DoubleSieve

open Finset Real
open scoped Classical

/-- The geometric raw sum exceeds the actual `P(N)` raw sum by at
most the genuine left raw boundary. This is a finite carrier inclusion;
no effective coefficient or assumed raw comparison enters it. -/
theorem reboxingGeometricRaw_le_raw_add_left_R1 {i k N r : ℕ} {δ Δ s t : ℝ}
    {V : Fin i → ℝ} (hN : 4 ≤ N)
    (hb : wuSourceBox k δ N i Δ V) (hs : 0 < s)
    (hr : reboxingAlpha ((N : ℝ) ^ (1 / 2 - δ) / (∏ l, V l)) Δ t r ≤
      ((N : ℝ) ^ (1 / 2 - δ) / (∏ l, V l)) ^ (1 / s)) :
    reboxingGeometricRaw N δ Δ V t r ≤
      reboxingRawPrimeSum false N δ s t (convolutionWuWindows N Δ V) +
        reboxingR1 N δ Δ V t t 0 := by
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
  simp only [Bool.false_eq_true, if_false, W, Nat.cast_zero, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro d hd
  rw [← mul_add]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  let A := primeWindow N (reboxingAlpha q Δ t 0) (reboxingAlpha q Δ t r)
  let B := primeWindow N (reboxingAlpha q Δ t 0) (wuLocalCutoff N δ d t)
  let S := primeWindow N (wuLocalCutoff N δ d t) (wuLocalCutoff N δ d s)
  let F : ℕ → ℝ := fun p => sourceSieveCount N (d * p) ((d * p) * N) p
  have hupper := (reboxing_support_cutoff_bounds hQ.le (by linarith : 0 < Δ) hV hs hd).1
  have hsub : A ⊆ S ∪ B := by
    intro p hp
    obtain ⟨hpp, hpc, hpl, hpu⟩ := mem_primeWindow.mp hp
    by_cases hc : (p : ℝ) < wuLocalCutoff N δ d t
    · exact mem_union_right _ (mem_primeWindow.mpr ⟨hpp, hpc, hpl, hc⟩)
    · exact mem_union_left _ (mem_primeWindow.mpr
        ⟨hpp, hpc, le_of_not_gt hc, hpu.trans_le (hr.trans hupper)⟩)
  have hdis : Disjoint S B := by
    apply Finset.disjoint_left.mpr
    intro p hp hp'
    have h1 := (mem_primeWindow.mp hp).2.2.1
    have h2 := (mem_primeWindow.mp hp').2.2.2
    linarith
  have hsum : (∑ p ∈ A, F p) ≤ (∑ p ∈ S, F p) + ∑ p ∈ B, F p := by
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

/-- The actual `P(dN)` Buchstab sum receives the lower inserted-box
main term after a single epsilon ledger pays reverse R2, the left raw
boundary, and the raw repeated-prime lane. No term is dropped using
an unproved positivity of the lower coefficient. -/
theorem reboxingRawPrimeSum_lower_geometric (k : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N0 : ℕ, T ≤ N0 → ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → t ≤ 10 →
      let q := (N : ℝ) ^ (1 / 2 - δ) / (∏ l, V l)
      ∃ r : ℕ, reboxingAlpha q Δ t r ≤ q ^ (1 / s) ∧
        q ^ (1 / s) < reboxingAlpha q Δ t (r + 1) ∧
        reboxingGeometricMain false k N0 N δ Δ V t r
            (fun j => reboxingS2 q Δ t i (j + 1)) -
          ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) ≤
        reboxingRawPrimeSum true N δ s t (convolutionWuWindows N Δ V) := by
  have hε3 : 0 < ε / 3 := by positivity
  obtain ⟨T1, hT14, hlower⟩ := reboxingGeometricRaw_lower_s2 k hδ hδhi hε3
  obtain ⟨T2, hR1⟩ := reboxingR1_relative k hδ hδhi hε3
  obtain ⟨T3, hraw⟩ := wu_raw_prime_transport_relative k hδ
    (by linarith : δ < 1 / 2) hε3
  refine ⟨max T1 (max T2 T3), hT14.trans (le_max_left _ _), ?_⟩
  intro N0 hN0 N hN he i Δ V hb s t hs hst ht
  have h1 : T1 ≤ N0 := (le_max_left _ _).trans hN0
  have h2 : T2 ≤ N :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (hN0.trans hN))
  have h3 : T3 ≤ N :=
    (le_max_right _ _).trans ((le_max_right _ _).trans (hN0.trans hN))
  have hN4 : 4 ≤ N := hT14.trans (h1.trans hN)
  let q := (N : ℝ) ^ (1 / 2 - δ) / (∏ l, V l)
  obtain ⟨r, hrlo, hrhi, hmain⟩ := hlower N0 h1 N hN he i Δ V hb s t hs hst ht
  refine ⟨r, hrlo, hrhi, ?_⟩
  have hfinite := reboxingGeometricRaw_le_raw_add_left_R1 hN4 hb
    (show 0 < s by linarith) hrlo
  have hNreal : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hΔ : 1 < Δ := by
    have hpow := rpow_pos_of_pos (log_pos hNreal) (-4 : ℝ)
    linarith [hb.2.1]
  have hV : ∀ j, 0 < V j := fun j =>
    (rpow_pos_of_pos (by linarith : (0 : ℝ) < N) _).trans_le (hb.2.2.2.2.1 j)
  have hq : 0 < q := div_pos (rpow_pos_of_pos (by linarith : (0 : ℝ) < N) _)
    (prod_pos (fun j _ => hV j))
  have hzero : reboxingAlpha q Δ t (0 : ℕ) ≤ q ^ (1 / t) ∧
      q ^ (1 / t) < reboxingAlpha q Δ t ((0 : ℕ) + 1) := by
    constructor
    · simp [reboxingAlpha]
    · simpa [reboxingAlpha] using
        mul_lt_mul_of_pos_left hΔ (rpow_pos_of_pos hq (1 / t))
  have hleft := (hR1 N h2 he i Δ V hb t t (hs.trans hst) le_rfl ht 0 hzero).2
  have hrepeat := (hraw N h3 he i Δ V hb s t hs hst ht).2
  linarith

end Wu2008DoubleSieve
