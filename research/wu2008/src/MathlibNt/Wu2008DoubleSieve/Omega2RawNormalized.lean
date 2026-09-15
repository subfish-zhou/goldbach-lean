import MathlibNt.Wu2008DoubleSieve.Omega2ReboxingBoundary
import MathlibNt.Wu2008DoubleSieve.Omega2PrimeIntegral

/-!
# Actual Omega2 lower bound by the signed normalized prime sum

Wu04 Lemma 5.1 (5.2), before the prime-to-integral limit. A single
threshold precedes the finite improvement threshold, all legal source
boxes, and every outer parameter. Both geometric prime boundaries,
the fixed-cutoff error, and the repeated-prime normalization are paid.
-/

namespace Wu2008DoubleSieve

open Finset Real Filter
open scoped Classical Topology
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418

private theorem omega2_prime_window_split (N : ℕ) {a b c : ℝ}
    (hab : a ≤ b) (hbc : b ≤ c) (f : ℕ → ℝ) :
    (∑ p ∈ primeWindow N a c, f p) =
      (∑ p ∈ primeWindow N a b, f p) + ∑ p ∈ primeWindow N b c, f p := by
  have he : primeWindow N a c = primeWindow N a b ∪ primeWindow N b c := by
    ext p
    simp only [mem_union, mem_primeWindow]
    constructor
    · rintro ⟨hp, hcop, hlo, hhi⟩
      by_cases h : (p : ℝ) < b
      · exact Or.inl ⟨hp, hcop, hlo, h⟩
      · exact Or.inr ⟨hp, hcop, le_of_not_gt h, hhi⟩
    · rintro (⟨hp, hcop, hlo, hhi⟩ | ⟨hp, hcop, hlo, hhi⟩)
      · exact ⟨hp, hcop, hlo, hhi.trans_le hbc⟩
      · exact ⟨hp, hcop, hab.trans hlo, hhi⟩
  rw [he, sum_union]
  exact disjoint_left.mpr (fun p hp hq =>
    (not_lt_of_ge (mem_primeWindow.mp hq).2.2.1) (mem_primeWindow.mp hp).2.2.2)

theorem omega2Prime_le_geometric_add_boundaries {i k N0 N r : ℕ}
    {δ Δ s t : ℝ} {V : Fin i → ℝ}
    (hN : 4 ≤ N) (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10)
    (hb : wuSourceBox k δ N i Δ V) (hs : 2 ≤ s) (hst : s ≤ t) (ht : t ≤ 10)
    (hr : reboxingAlpha ((N : ℝ) ^ (1 / 2 - δ) / (∏ l, V l)) Δ t r ≤
      ((N : ℝ) ^ (1 / 2 - δ) / (∏ l, V l)) ^ (1 / s)) :
    reboxingPrimeSum false N δ s t (convolutionWuWindows N Δ V)
        (fun d p => wuEffectiveCoefficient false (k + 1) δ N0
          (t * (1 - log p / log ((N : ℝ) ^ (1 / 2 - δ) / d)))) ≤
      omega2GeometricPrime k N0 N δ Δ V t r +
        omega2BoundaryAbsolute k N0 N δ Δ V t t 0 +
        omega2BoundaryAbsolute k N0 N δ Δ V s t r := by
  let Q := (N : ℝ) ^ (1 / 2 - δ)
  let q := Q / (∏ l, V l)
  let W := convolutionWuWindows N Δ V
  let f := fun x => wuEffectiveCoefficient false (k + 1) δ N0 (omega2ParameterTransform t x)
  let F := fun d p : ℕ => f (log (Q / d) / log p - 1) /
    (((p : ℝ) - 2) * (1 - log (p : ℝ) / log (Q / d)))
  let w := fun d : ℕ => (convolutionCoeff W d : ℝ) * wuSingularSeries (d * N) /
    ((Nat.totient d : ℝ) * log (Q / d))
  have hNreal : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hQpos : 0 < Q := rpow_pos_of_pos (by linarith) _
  have hV : ∀ l, 0 < V l := fun l =>
    (rpow_pos_of_pos (by linarith : (0 : ℝ) < N) _).trans_le (hb.2.2.2.2.1 l)
  have hΔ : 1 < Δ := by
    have hh := rpow_pos_of_pos (log_pos hNreal) (-4 : ℝ)
    linarith [hb.2.1]
  have hΔ0 : 0 < Δ := by linarith
  have hq0 : 0 < q := div_pos hQpos (prod_pos (fun l _ => hV l))
  have hsupport := fun d hd => wu_buchstab_prime_window_bounds (show 2 ≤ N by omega)
    hδ (by linarith : δ < 1 / 2) hb hs hst ht (d := d) hd
  have hw (d : ℕ) (hd : d ∈ boxConvolutionSupport W) : 0 ≤ w d :=
    div_nonneg (mul_nonneg (Nat.cast_nonneg _)
      (wuSingularSeries_pos _ (Nat.mul_pos (hsupport d hd).1 (by omega))).le)
      (mul_nonneg (Nat.cast_nonneg _) (log_pos (hsupport d hd).2.2.1).le)
  have hli : 0 ≤ 4 * logarithmicIntegral N :=
    mul_nonneg (by norm_num) ((by positivity : (0 : ℝ) ≤ N / (2 * log N)).trans
      (box_trueLi_lower hN))
  have hfibre (d : ℕ) (hd : d ∈ boxConvolutionSupport W) :
      (∑ p ∈ primeWindow N (wuLocalCutoff N δ d t) (wuLocalCutoff N δ d s), F d p) ≤
        (∑ p ∈ primeWindow N (reboxingAlpha q Δ t 0) (reboxingAlpha q Δ t r), F d p) +
        (∑ p ∈ primeWindow N (q ^ (1 / t)) (wuLocalCutoff N δ d t), |F d p|) +
        (∑ p ∈ primeWindow N (reboxingAlpha q Δ t r) (wuLocalCutoff N δ d s), |F d p|) := by
    have hA : reboxingAlpha q Δ t 0 ≤ reboxingAlpha q Δ t r :=
      (reboxingAlpha_strictMono (t := t) hq0 hΔ).monotone (by positivity)
    have hBD : reboxingAlpha q Δ t r ≤ wuLocalCutoff N δ d s :=
      hr.trans ((reboxing_support_cutoff_bounds hQpos.le hΔ0 hV
        (show 0 < s by linarith) hd).1)
    have hAC : reboxingAlpha q Δ t 0 ≤ wuLocalCutoff N δ d t := by
      rw [reboxingAlpha_zero]
      exact (reboxing_support_cutoff_bounds hQpos.le hΔ0 hV
        (show 0 < t by linarith) hd).1
    have hCD : wuLocalCutoff N δ d t ≤ wuLocalCutoff N δ d s :=
      rpow_le_rpow_of_exponent_le (hsupport d hd).2.2.1.le
        (one_div_le_one_div_of_le (by linarith : 0 < s) hst)
    have hsplit1 := omega2_prime_window_split N hA hBD (F d)
    have hsplit2 := omega2_prime_window_split N hAC hCD (F d)
    have hleft := (neg_le_abs
      (∑ p ∈ primeWindow N (reboxingAlpha q Δ t 0) (wuLocalCutoff N δ d t), F d p)).trans
      (abs_sum_le_sum_abs _ _)
    have hright : (∑ p ∈ primeWindow N (reboxingAlpha q Δ t r) (wuLocalCutoff N δ d s),
        F d p) ≤ ∑ p ∈ primeWindow N (reboxingAlpha q Δ t r) (wuLocalCutoff N δ d s),
        |F d p| := sum_le_sum (fun p _ => le_abs_self _)
    simp only [reboxingAlpha_zero] at hsplit1 hsplit2 hleft ⊢
    linarith
  unfold reboxingPrimeSum omega2GeometricPrime omega2BoundaryAbsolute
  simp only [Bool.false_eq_true, if_false, Nat.cast_zero, reboxingAlpha_zero]
  rw [← mul_add, ← mul_add]
  apply mul_le_mul_of_nonneg_left _ hli
  simp only [← sum_add_distrib]
  apply sum_le_sum
  intro d hd
  simpa only [w, F, f, W, q, Q, mul_add, wuLocalCutoff,
    omega2ParameterTransform, sub_add_cancel, one_div_div, reboxingAlpha_zero] using
    mul_le_mul_of_nonneg_left (hfibre d hd) (hw d hd)

theorem omega2Raw_lower_prime_all (k : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N0 : ℕ, T ≤ N0 → ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → 3 ≤ t → t ≤ 5 →
      reboxingPrimeSum false N δ s t (convolutionWuWindows N Δ V)
          (fun d p => wuEffectiveCoefficient false (k + 1) δ N0
            (t * (1 - log p / log ((N : ℝ) ^ (1 / 2 - δ) / d)))) -
        ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) ≤
      wuOmega2Sum N δ s t (convolutionWuWindows N Δ V) := by
  have hε4 : 0 < ε / 4 := by positivity
  obtain ⟨T1, hT14, hraw⟩ := omega2Raw_lower_geometric k hδ hδhi hε4
  obtain ⟨T2, _, hnorm⟩ := omega2GeometricPrime_le_main_add_repeated k hδ hδhi
  obtain ⟨T3, hrepeat⟩ := wu_reboxing_repeated_theta_relative k hδ
    (by linarith : δ < 1 / 2) (pow_pos hδ (k + 2))
    (show 0 < ε / 44 by positivity)
  obtain ⟨T4, _, hboundary⟩ := omega2BoundaryAbsolute_relative k hδ hδhi hε4
  refine ⟨max T1 (max T2 (max T3 T4)), hT14.trans (le_max_left _ _), ?_⟩
  intro N0 hN0 N hN he i Δ V hb s t hs hst ht3 ht5
  have h1 : T1 ≤ N0 := by omega
  have h2 : T2 ≤ N0 := by omega
  have h3 : T3 ≤ N := by omega
  have h4 : T4 ≤ N0 := by omega
  have hN4 : 4 ≤ N := hT14.trans (h1.trans hN)
  obtain ⟨r, hrlo, hrhi, hrawmain⟩ := hraw N0 h1 N hN he i Δ V hb s t hs hst ht3 ht5
  have hnormal := hnorm N0 h2 N hN i Δ V hb s t hs hst ht3 ht5 r ⟨hrlo, hrhi⟩
  have hrep := hrepeat N h3 i Δ V hb
  have hr := (hboundary N0 h4 N hN i Δ V hb s t hs hst ht3 ht5 r ⟨hrlo, hrhi⟩).2
  have hwindow := omega2Prime_le_geometric_add_boundaries (N0 := N0)
    hN4 hδ hδhi hb hs hst (by linarith : t ≤ 10) hrlo
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
  have hl := (hboundary N0 h4 N hN i Δ V hb t t (by linarith) le_rfl ht3 ht5 0 hzero).2
  linarith

theorem omega2_prime_transport_relative (k : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N0 : ℕ, T ≤ N0 → ∀ N : ℕ, N0 ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → 3 ≤ t → t ≤ 5 →
        let W := convolutionWuWindows N Δ V
        let g := fun d p : ℕ => wuEffectiveCoefficient false (k + 1) δ N0
          (t * (1 - log p / log ((N : ℝ) ^ (1 / 2 - δ) / d)))
        |reboxingPrimeSum false N δ s t W g - reboxingPrimeSum true N δ s t W g| ≤
          ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) W := by
  exact omega2_effective_prime_transport_relative false k hδ hδhi hε

/-- The literal selected-prime normalized lower estimate for actual
Omega2. This includes the source range `2≤s≤3≤t≤5`, `t-t/s≥2`. -/
theorem wuOmega2Sum_lower_normalized_prime (k : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N0 : ℕ, T ≤ N0 → ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → 3 ≤ t → t ≤ 5 →
      reboxingPrimeSum true N δ s t (convolutionWuWindows N Δ V)
          (fun d p => wuEffectiveCoefficient false (k + 1) δ N0
            (t * (1 - log p / log ((N : ℝ) ^ (1 / 2 - δ) / d)))) -
        ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) ≤
      wuOmega2Sum N δ s t (convolutionWuWindows N Δ V) := by
  obtain ⟨T1, hT14, hraw⟩ := omega2Raw_lower_prime_all k hδ hδhi (half_pos hε)
  obtain ⟨T2, _, htransport⟩ := omega2_prime_transport_relative k hδ
    (by linarith : δ < 1 / 2) (half_pos hε)
  refine ⟨max T1 T2, hT14.trans (le_max_left _ _), ?_⟩
  intro N0 hN0 N hN he i Δ V hb s t hs hst ht3 ht5
  have h1 : T1 ≤ N0 := by omega
  have h2 : T2 ≤ N0 := by omega
  have hr := hraw N0 h1 N hN he i Δ V hb s t hs hst ht3 ht5
  have hp := htransport N0 h2 N hN i Δ V hb s t hs hst ht3 ht5
  have hh := (abs_le.mp hp).1
  linarith

end Wu2008DoubleSieve
