import MathlibNt.Wu2008DoubleSieve.Omega2RawCutoff
import MathlibNt.Wu2008DoubleSieve.ReboxingBlockSum
import MathlibNt.Wu2008DoubleSieve.ReboxingRawUpper
import MathlibNt.Wu2008DoubleSieve.OmegaTerms

/-! # Actual sorted inserted boxes for the fixed Omega2 cutoff -/

namespace Wu2008DoubleSieve

open Finset Real
open scoped Classical

noncomputable def omega2GeometricRaw {i : ℕ} (N : ℕ) (δ Δ : ℝ)
    (V : Fin i → ℝ) (t : ℝ) (r : ℕ) : ℝ :=
  ∑ j ∈ range r, ∑ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
    (convolutionCoeff (convolutionWuWindows N Δ V) d : ℝ) *
    ∑ p ∈ primeWindow N
      (reboxingAlpha ((N : ℝ) ^ (1 / 2 - δ) / (∏ l, V l)) Δ t j)
      (reboxingAlpha ((N : ℝ) ^ (1 / 2 - δ) / (∏ l, V l)) Δ t (j + 1)),
      (sourceSieveCount N (d * p) ((d * p) * N) (wuLocalCutoff N δ d t) : ℝ)

theorem omega2GeometricRaw_eq_cutoff_sub_error {i : ℕ} (N : ℕ) (δ Δ : ℝ)
    (V : Fin i → ℝ) (t : ℝ) (r : ℕ) :
    omega2GeometricRaw N δ Δ V t r =
      reboxingGeometricCutoff N δ Δ V t r
        (fun j => omega2ParameterTransform t
          (reboxingS2 ((N : ℝ) ^ (1 / 2 - δ) / (∏ l, V l)) Δ t i (j + 1))) -
      omega2CutoffError N δ Δ V t r := by
  unfold omega2GeometricRaw reboxingGeometricCutoff omega2CutoffError
  simp only [Finset.sum_sub_distrib, mul_sub]
  ring

theorem omega2GeometricRaw_lower (k : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N0 : ℕ, T ≤ N0 → ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → 3 ≤ t → t ≤ 5 →
      let q := (N : ℝ) ^ (1 / 2 - δ) / (∏ l, V l)
      ∃ r : ℕ, reboxingAlpha q Δ t r ≤ q ^ (1 / s) ∧
        q ^ (1 / s) < reboxingAlpha q Δ t (r + 1) ∧
        reboxingGeometricMain false k N0 N δ Δ V t r
            (fun j => omega2ParameterTransform t (reboxingS2 q Δ t i (j + 1))) -
          ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) ≤
        omega2GeometricRaw N δ Δ V t r := by
  obtain ⟨T1, hT14, hblocks⟩ := wu_reboxed_block_upper_lower k hδ hδhi
  obtain ⟨T2, _, hparameters⟩ := reboxing_source_parameters k hδ hδhi
  obtain ⟨T3, herror⟩ := omega2CutoffError_relative k hδ hδhi hε
  refine ⟨max T1 (max T2 T3), hT14.trans (le_max_left _ _), ?_⟩
  intro N0 hN0 N hN he i Δ V hb s t hs hst ht3 ht5
  have h1 : T1 ≤ N0 := by omega
  have h2 : T2 ≤ N := by omega
  have h3 : T3 ≤ N := by omega
  let q := (N : ℝ) ^ (1 / 2 - δ) / (∏ l, V l)
  have ht10 : t ≤ 10 := by linarith
  obtain ⟨r, hrlo, hrhi, hp⟩ := hparameters N h2 i Δ V hb s t hs hst ht10
  refine ⟨r, hrlo, hrhi, ?_⟩
  have hcut :
      reboxingGeometricMain false k N0 N δ Δ V t r
          (fun j => omega2ParameterTransform t (reboxingS2 q Δ t i (j + 1))) ≤
        reboxingGeometricCutoff N δ Δ V t r
          (fun j => omega2ParameterTransform t (reboxingS2 q Δ t i (j + 1))) := by
    unfold reboxingGeometricCutoff reboxingGeometricMain
    apply Finset.sum_le_sum
    intro j hj
    have hpj := hp (j + 1) (by omega) (by have := mem_range.mp hj; omega)
    simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right] at hpj
    have hdom := omega2ParameterTransform_domain ht3 ht5 hpj.2.2.2.2.2.1
    have hcmp := hblocks N0 h1 N hN he i Δ V hb s t
      (reboxingAlpha q Δ t (j + 1)) hs (by linarith) ht10 hpj.1 hpj.2.1
      (omega2ParameterTransform t (reboxingS2 q Δ t i (j + 1))) hdom.1 hdom.2
    have hprev := hpj.2.2.1
    simpa only [q, hprev, wuEffectiveCoefficient, Bool.false_eq_true, ↓reduceIte,
      Nat.cast_add, Nat.cast_one] using hcmp.1
  have herr := (herror N h3 he i Δ V hb s t hs hst ht3 ht5 r hrlo).2
  rw [omega2GeometricRaw_eq_cutoff_sub_error]
  exact sub_le_sub hcut herr

theorem omega2_source_count_prime_modulus_eq (N d : ℕ) {p : ℕ} {z : ℝ}
    (hp : p.Prime) (hz : z ≤ p) :
    sourceSieveCount N (d * p) ((d * p) * N) z =
      sourceSieveCount N (d * p) (d * N) z := by
  have hprod : ordinarySievePrimeProduct ((d * p) * N) z =
      ordinarySievePrimeProduct (d * N) z := by
    unfold ordinarySievePrimeProduct
    rw [show (d * p) * N = p * (d * N) by ring,
      primeWindow_mul_of_prime_above (d * N) hp hz]
  have hc : sourceSieveCarrier N (d * p) ((d * p) * N) z =
      sourceSieveCarrier N (d * p) (d * N) z := by
    ext n
    simp only [sourceSieveCarrier, mem_filter, sifted_iff_product_coprime, hprod]
  exact congrArg (fun S : Finset ℕ => (S.card : ℤ)) hc

theorem omega2GeometricRaw_le_actual_add_left {i k N r : ℕ} {δ Δ s t : ℝ}
    {V : Fin i → ℝ} (hN : 4 ≤ N)
    (hb : wuSourceBox k δ N i Δ V) (hs : 0 < s)
    (hr : reboxingAlpha ((N : ℝ) ^ (1 / 2 - δ) / (∏ l, V l)) Δ t r ≤
      ((N : ℝ) ^ (1 / 2 - δ) / (∏ l, V l)) ^ (1 / s)) :
    omega2GeometricRaw N δ Δ V t r ≤
      wuOmega2Sum N δ s t (convolutionWuWindows N Δ V) +
        reboxingR1 N δ Δ V t t 0 := by
  let W := convolutionWuWindows N Δ V
  let Q := (N : ℝ) ^ (1 / 2 - δ)
  let q := Q / (∏ l, V l)
  have hNreal : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hΔ : 1 < Δ := by
    have hh := rpow_pos_of_pos (log_pos hNreal) (-4 : ℝ)
    linarith [hb.2.1]
  have hV : ∀ j, 0 < V j := fun j =>
    (rpow_pos_of_pos (by linarith : (0 : ℝ) < N) _).trans_le (hb.2.2.2.2.1 j)
  have hQ : 0 < Q := rpow_pos_of_pos (by linarith) _
  have hq : 0 < q := div_pos hQ (prod_pos (fun j _ => hV j))
  have hpart := reboxingAlpha_convolution_sum_partition (t := t) hq hΔ N r W
    (fun d p => (sourceSieveCount N (d * p) ((d * p) * N) (wuLocalCutoff N δ d t) : ℝ))
  change _ = omega2GeometricRaw N δ Δ V t r at hpart
  rw [← hpart]
  unfold wuOmega2Sum wuOmega2 reboxingR1 reboxingBoundaryCount
  simp only [W, Nat.cast_zero, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro d hd
  rw [← mul_add]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  let A := primeWindow N (reboxingAlpha q Δ t 0) (reboxingAlpha q Δ t r)
  let B := primeWindow N (reboxingAlpha q Δ t 0) (wuLocalCutoff N δ d t)
  let S := primeWindow N (wuLocalCutoff N δ d t) (wuLocalCutoff N δ d s)
  let F : ℕ → ℝ := fun p => sourceSieveCount N (d * p) ((d * p) * N) (wuLocalCutoff N δ d t)
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
    exact (not_lt_of_ge (mem_primeWindow.mp hp).2.2.1) (mem_primeWindow.mp hp').2.2.2
  have hsum : (∑ p ∈ A, F p) ≤ (∑ p ∈ S, F p) + ∑ p ∈ B, F p := by
    rw [← Finset.sum_union hdis]
    apply Finset.sum_le_sum_of_subset_of_nonneg hsub
    intro p _ _
    dsimp [F]
    simp only [sourceSieveCount, Int.cast_natCast]
    positivity
  have hSsum : (∑ p ∈ S, F p) =
      ∑ p ∈ S, (sourceSieveCount N (d * p) (d * N) (wuLocalCutoff N δ d t) : ℝ) := by
    apply sum_congr rfl
    intro p hp
    dsimp [F]
    rw [omega2_source_count_prime_modulus_eq N d (mem_primeWindow.mp hp).1
      (mem_primeWindow.mp hp).2.2.1]
  have hBsum : (∑ p ∈ B, F p) ≤
      ∑ p ∈ B, (sourceSieveCount N (d * p) (d * N) p : ℝ) := by
    apply sum_le_sum
    intro p hp
    have hwin := mem_primeWindow.mp hp
    rw [← reboxing_source_count_prime_modulus_eq N d hwin.1]
    have hsub' : sourceSieveCarrier N (d * p) ((d * p) * N) (wuLocalCutoff N δ d t) ⊆
        sourceSieveCarrier N (d * p) ((d * p) * N) p := by
      intro n hn
      obtain ⟨hnN, hnP, hnd, hnz⟩ := mem_filter.mp hn
      exact mem_filter.mpr ⟨hnN, hnP, hnd, fun q hq hc hz => hnz q hq hc (hz.trans hwin.2.2.2)⟩
    simpa only [F, sourceSieveCount, Int.cast_natCast] using
      (show ((sourceSieveCarrier N (d * p) ((d * p) * N) (wuLocalCutoff N δ d t)).card : ℝ) ≤
        (sourceSieveCarrier N (d * p) ((d * p) * N) p).card by exact_mod_cast card_le_card hsub')
  rw [hSsum] at hsum
  exact hsum.trans (add_le_add le_rfl hBsum)

theorem omega2Raw_lower_geometric (k : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N0 : ℕ, T ≤ N0 → ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → 3 ≤ t → t ≤ 5 →
      let q := (N : ℝ) ^ (1 / 2 - δ) / (∏ l, V l)
      ∃ r : ℕ, reboxingAlpha q Δ t r ≤ q ^ (1 / s) ∧
        q ^ (1 / s) < reboxingAlpha q Δ t (r + 1) ∧
        reboxingGeometricMain false k N0 N δ Δ V t r
            (fun j => omega2ParameterTransform t (reboxingS2 q Δ t i (j + 1))) -
          ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) ≤
        wuOmega2Sum N δ s t (convolutionWuWindows N Δ V) := by
  obtain ⟨T1, hT14, hraw⟩ := omega2GeometricRaw_lower k hδ hδhi (half_pos hε)
  obtain ⟨T2, hR1⟩ := reboxingR1_relative k hδ hδhi (half_pos hε)
  refine ⟨max T1 T2, hT14.trans (le_max_left _ _), ?_⟩
  intro N0 hN0 N hN he i Δ V hb s t hs hst ht3 ht5
  have h1 : T1 ≤ N0 := by omega
  have h2 : T2 ≤ N := by omega
  have hN4 : 4 ≤ N := by omega
  obtain ⟨r, hrlo, hrhi, hmain⟩ := hraw N0 h1 N hN he i Δ V hb s t hs hst ht3 ht5
  refine ⟨r, hrlo, hrhi, ?_⟩
  have hfinite := omega2GeometricRaw_le_actual_add_left hN4 hb (by linarith : 0 < s) hrlo
  have hNreal : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hΔ : 1 < Δ := by
    have hh := rpow_pos_of_pos (log_pos hNreal) (-4 : ℝ)
    linarith [hb.2.1]
  have hV : ∀ j, 0 < V j := fun j =>
    (rpow_pos_of_pos (by linarith : (0 : ℝ) < N) _).trans_le (hb.2.2.2.2.1 j)
  let q := (N : ℝ) ^ (1 / 2 - δ) / (∏ j, V j)
  have hq : 0 < q := div_pos (rpow_pos_of_pos (by linarith : (0 : ℝ) < N) _)
    (prod_pos (fun j _ => hV j))
  have hzero : reboxingAlpha q Δ t (0 : ℕ) ≤ q ^ (1 / t) ∧
      q ^ (1 / t) < reboxingAlpha q Δ t ((0 : ℕ) + 1) := by
    constructor
    · simp [reboxingAlpha]
    · simpa [reboxingAlpha] using mul_lt_mul_of_pos_left hΔ (rpow_pos_of_pos hq (1 / t))
  have hleft := (hR1 N h2 he i Δ V hb t t (by linarith) le_rfl
    (by linarith) 0 hzero).2
  linarith

end Wu2008DoubleSieve
