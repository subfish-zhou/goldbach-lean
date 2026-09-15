import MathlibNt.Wu2008DoubleSieve.OmegaTerms
import MathlibNt.Wu2008DoubleSieve.ElevenTermAssembly
import MathlibNt.Wu2008DoubleSieve.ReboxingPrimeTransport

/-!
# Actual finite first weighted comparison

The accepted finite three-prime weight retains distinct divisor multiplicities
without a squarefreeness restriction. Its selected-window realization gives
the conclusion of Wu04 Lemma 4.1 directly. The negative single-prime term
requires the entire `p ∣ d` lane when its window is changed to `P(N)`.
-/

namespace Wu2008DoubleSieve

open Finset Real
open scoped Classical

theorem omega_source_single_carrier (N d : ℕ) {p : ℕ} {z : ℝ}
    (hp : p.Prime) (hz : z ≤ (p : ℝ)) :
    sourceSieveCarrier N (d * p) (d * N) z =
      sieveCarrier N (d * p) (d * N) z := by
  rw [sourceSieveCarrier_eq_ite, if_pos]
  exact (sifted_mul_iff _ _ _ _).mpr
    ⟨fun q hq hcop hqz =>
      siftedLE_of_dvd_modulus (dvd_mul_right d N) z q hq hcop hqz.le,
      sifted_prime_of_le hp hz⟩

theorem omega_source_triple_carrier (N d a : ℕ) {b c : ℕ}
    (hb : b.Prime) (hc : c.Prime) (hbc : b ≤ c) :
    sourceSieveCarrier N (d * a * b * c) (d * a * N) (b : ℝ) =
      sieveCarrier N (d * a * b * c) (d * a * N) (b : ℝ) := by
  simpa only [Nat.mul_comm N (d * a)] using
    (source_strict_triple_carrier (N := N) (a := d * a) hb hc hbc)

/-- Exact selected-window weight, on the literal unscaled carriers. -/
theorem omega_selected_weight (N d : ℕ) {z w : ℝ} (hzw : z ≤ w) :
    2 * (sourceSieveCount N d (d * N) w : ℝ) ≤
      2 * (sourceSieveCount N d (d * N) z : ℝ) -
        (∑ p ∈ primeWindow (d * N) z w,
          (sourceSieveCount N (d * p) (d * N) z : ℝ)) +
        ∑ t ∈ orderedTriples (primeWindow (d * N) z w),
          (sourceSieveCount N (d * t.1 * t.2.1 * t.2.2)
            (d * t.1 * N) (t.2.1 : ℝ) : ℝ) := by
  have h := goldbach_three_prime_upper_weight N d (d * N) hzw
  have hbase (v : ℝ) : sieveCount N d (d * N) v =
      sourceSieveCount N d (d * N) v := by
    unfold sieveCount sourceSieveCount
    rw [sourceSieveCarrier_of_dvd_modulus N (dvd_mul_right d N)]
  have hsingle :
      (∑ p ∈ primeWindow (d * N) z w, sieveCount N (d * p) (d * N) z) =
        ∑ p ∈ primeWindow (d * N) z w, sourceSieveCount N (d * p) (d * N) z := by
    apply sum_congr rfl
    intro p hp
    unfold sieveCount sourceSieveCount
    rw [omega_source_single_carrier N d (mem_primeWindow.mp hp).1
      (mem_primeWindow.mp hp).2.2.1]
  have htriple :
      (∑ t ∈ orderedTriples (primeWindow (d * N) z w),
        sieveCount N (d * (t.1 * t.2.1 * t.2.2)) (d * N * t.1) (t.2.1 : ℝ)) =
      ∑ t ∈ orderedTriples (primeWindow (d * N) z w),
        sourceSieveCount N (d * t.1 * t.2.1 * t.2.2)
          (d * t.1 * N) (t.2.1 : ℝ) := by
    apply sum_congr rfl
    intro t ht
    obtain ⟨_, _, _, hb, _, hc, _, _, _, hbc⟩ := mem_s3_ordered_triples.mp ht
    simpa only [sieveCount, sourceSieveCount, mul_assoc, mul_comm, mul_left_comm] using
      (congrArg (fun A : Finset ℕ => (A.card : ℤ))
        (omega_source_triple_carrier N d t.1 hb hc hbc.le)).symm
  rw [hbase w, hbase z, hsingle, htriple] at h
  exact_mod_cast h

noncomputable def wuOmegaRepeated (N d : ℕ) (δ s t : ℝ) : ℝ :=
  ∑ p ∈ (primeWindow N (wuLocalCutoff N δ d t)
      (wuLocalCutoff N δ d s)).filter (fun p => p ∣ d),
    (sourceSieveCount N (d * p) (d * N) (wuLocalCutoff N δ d t) : ℝ)

noncomputable def wuOmegaRepeatedSum {i : ℕ} (N : ℕ) (δ s t : ℝ)
    (W : Fin i → Finset ℕ) : ℝ :=
  ∑ d ∈ boxConvolutionSupport W,
    (convolutionCoeff W d : ℝ) * wuOmegaRepeated N d δ s t

theorem omega_triple_sum_eq (N d : ℕ) (δ s t : ℝ) :
    (∑ v ∈ orderedTriples (primeWindow N (wuLocalCutoff N δ d t)
        (wuLocalCutoff N δ d s)),
      (sourceSieveCount N (d * v.1 * v.2.1 * v.2.2)
        (d * v.1 * N) (v.2.1 : ℝ) : ℝ)) = wuOmega3 N d δ s t := by
  have h := sum_s3_orderedTriples_descending N (wuLocalCutoff N δ d t)
    (wuLocalCutoff N δ d s)
    (fun v => sourceSieveCount N (d * v.1 * v.2.1 * v.2.2)
      (d * v.1 * N) (v.2.1 : ℝ))
  unfold wuOmega3
  exact_mod_cast h

noncomputable def wuOmegaSelectedTriple (N d : ℕ) (δ s t : ℝ) : ℝ :=
  ∑ v ∈ orderedTriples (primeWindow (d * N) (wuLocalCutoff N δ d t)
      (wuLocalCutoff N δ d s)),
    (sourceSieveCount N (d * v.1 * v.2.1 * v.2.2)
      (d * v.1 * N) (v.2.1 : ℝ) : ℝ)

/-- The actual slack in the accepted first-two-distinct-divisor weight. -/
noncomputable def wuOmegaSelectedSlack (N d : ℕ) (δ s t : ℝ) : ℝ :=
  2 * (sourceSieveCount N d (d * N) (wuLocalCutoff N δ d t) : ℝ) -
    (∑ p ∈ primeWindow (d * N) (wuLocalCutoff N δ d t) (wuLocalCutoff N δ d s),
      (sourceSieveCount N (d * p) (d * N) (wuLocalCutoff N δ d t) : ℝ)) +
    wuOmegaSelectedTriple N d δ s t -
    2 * (sourceSieveCount N d (d * N) (wuLocalCutoff N δ d s) : ℝ)

noncomputable def wuOmegaTripleWindowGain (N d : ℕ) (δ s t : ℝ) : ℝ :=
  wuOmega3 N d δ s t - wuOmegaSelectedTriple N d δ s t

theorem wuOmegaSelectedSlack_nonneg (N d : ℕ) {δ s t : ℝ}
    (hcut : wuLocalCutoff N δ d t ≤ wuLocalCutoff N δ d s) :
    0 ≤ wuOmegaSelectedSlack N d δ s t := by
  exact sub_nonneg.mpr (omega_selected_weight N d hcut)

theorem wuOmegaTripleWindowGain_nonneg (N d : ℕ) (δ s t : ℝ) :
    0 ≤ wuOmegaTripleWindowGain N d δ s t := by
  have hsub : orderedTriples (primeWindow (d * N)
      (wuLocalCutoff N δ d t) (wuLocalCutoff N δ d s)) ⊆
      orderedTriples (primeWindow N
        (wuLocalCutoff N δ d t) (wuLocalCutoff N δ d s)) := by
    intro v hv
    obtain ⟨hv, hab, hbc⟩ := mem_filter.mp hv
    obtain ⟨ha, hbc'⟩ := mem_product.mp hv
    obtain ⟨hb, hc⟩ := mem_product.mp hbc'
    have hw : primeWindow (d * N) (wuLocalCutoff N δ d t)
        (wuLocalCutoff N δ d s) ⊆ primeWindow N
        (wuLocalCutoff N δ d t) (wuLocalCutoff N δ d s) := by
      rw [primeWindow_mul_eq_filter]
      exact filter_subset _ _
    exact mem_filter.mpr ⟨mem_product.mpr ⟨hw ha, mem_product.mpr ⟨hw hb, hw hc⟩⟩,
      hab, hbc⟩
  have htr := sum_le_sum_of_subset_of_nonneg hsub
    (fun v _ _ => (show (0 : ℝ) ≤
      (sourceSieveCount N (d * v.1 * v.2.1 * v.2.2)
        (d * v.1 * N) (v.2.1 : ℝ) : ℝ) by unfold sourceSieveCount; positivity))
  rw [omega_triple_sum_eq] at htr
  exact sub_nonneg.mpr htr

/-- Both nonnegative slacks and the entire negative-window transport remain
visible before taking an inequality. No repeated-first-prime term was erased:
the accepted distinct-divisor weight holds for all multiplicities. -/
theorem wu_omega_weighted_decomposition (N d : ℕ) (δ s t : ℝ) :
    wuOmega1 N d δ t - wuOmega2 N d δ s t + wuOmega3 N d δ s t +
        wuOmegaRepeated N d δ s t =
      2 * (sourceSieveCount N d (d * N) (wuLocalCutoff N δ d s) : ℝ) +
        wuOmegaSelectedSlack N d δ s t + wuOmegaTripleWindowGain N d δ s t := by
  have hdiff := primeWindow_modulus_sum_difference N d
    (wuLocalCutoff N δ d t) (wuLocalCutoff N δ d s)
    (fun p => (sourceSieveCount N (d * p) (d * N) (wuLocalCutoff N δ d t) : ℝ))
  dsimp only [wuOmega1, wuOmegaRepeated, wuOmega2, wuOmegaSelectedSlack,
    wuOmegaTripleWindowGain]
  linarith

/-- The exact finite weight pays only an explicitly counted repeated-d lane.
The accepted first-two-divisor argument already covers squareful complements. -/
theorem wu_omega_weighted_finite (N d : ℕ) {δ s t : ℝ}
    (hcut : wuLocalCutoff N δ d t ≤ wuLocalCutoff N δ d s) :
    2 * (sourceSieveCount N d (d * N) (wuLocalCutoff N δ d s) : ℝ) ≤
      wuOmega1 N d δ t - wuOmega2 N d δ s t + wuOmega3 N d δ s t +
        wuOmegaRepeated N d δ s t := by
  rw [wu_omega_weighted_decomposition]
  have hs := wuOmegaSelectedSlack_nonneg N d hcut
  have hg := wuOmegaTripleWindowGain_nonneg N d δ s t
  linarith

theorem wu_omega_weighted_box {i N : ℕ} {δ s t : ℝ} (W : Fin i → Finset ℕ)
    (hcut : ∀ d ∈ boxConvolutionSupport W,
      wuLocalCutoff N δ d t ≤ wuLocalCutoff N δ d s) :
    2 * wuBoxPhi N δ W s ≤ wuOmega1Sum N δ t W - wuOmega2Sum N δ s t W +
      wuOmega3Sum N δ s t W + wuOmegaRepeatedSum N δ s t W := by
  have h := sum_le_sum (fun d hd => mul_le_mul_of_nonneg_left
    (wu_omega_weighted_finite N d (hcut d hd))
    (Nat.cast_nonneg (convolutionCoeff W d) : (0 : ℝ) ≤ _))
  simpa only [wuBoxPhi, convolutionSieveCount, wuOmega1Sum, wuOmega2Sum,
    wuOmega3Sum, wuOmegaRepeatedSum, mul_add, mul_sub, sum_add_distrib,
    sum_sub_distrib, mul_left_comm (convolutionCoeff W _ : ℝ) 2,
    ← mul_sum, boxConvolutionSupport] using h

end Wu2008DoubleSieve
