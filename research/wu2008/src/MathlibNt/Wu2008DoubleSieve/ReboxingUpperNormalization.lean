import MathlibNt.Wu2008DoubleSieve.ReboxingRawUpper
import MathlibNt.Wu2008DoubleSieve.ReboxingBoundaryR3Absolute

/-!
# Actual upper reboxing normalization

Wu04 source lines 1080--1100. The summed inserted Theta is normalized
with its exact repeated-prime branch. Nonnegativity of the actual upper
coefficient permits the `1/p ≤ 1/(p-2)` majorant. The lower boundary is
paid by the absolute `p-2` R3, not the printed signed `φ(p)` expression.
-/

namespace Wu2008DoubleSieve

open Finset Filter Real
open scoped Classical Topology
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418

/-- Exact inserted-prime normalization followed by the upper majorant.
Only the repeated-prime branch is enlarged, from `1/p` to `1/(p-2)`. -/
theorem wu_inserted_theta_upper_coefficient {N d p : ℕ} {Q a b : ℝ}
    (hN : 0 < N) (hd : 0 < d) (hp : p.Prime) (hp2 : 2 < p)
    (hpN : p.Coprime N) (hD : 1 < Q / d)
    (hpupper : (p : ℝ) ≤ (Q / d) ^ (1 / 2 : ℝ))
    (ha : 0 ≤ a) (hab : a ≤ b) :
    a * (wuSingularSeries ((d * p) * N) /
      ((Nat.totient (d * p) : ℝ) * log (Q / (d * p)))) ≤
      (wuSingularSeries (d * N) / ((Nat.totient d : ℝ) * log (Q / d))) *
        (b / (((p : ℝ) - 2) * (1 - log (p : ℝ) / log (Q / d)))) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp2' : (2 : ℝ) < p := by exact_mod_cast hp2
  have hgap := reboxing_log_ratio_half hD hp0 hpupper
  have hgap0 : 0 < 1 - log (p : ℝ) / log (Q / d) := by linarith
  have hw : 0 ≤ wuSingularSeries (d * N) /
      ((Nat.totient d : ℝ) * log (Q / d)) :=
    div_nonneg (wuSingularSeries_pos _ (Nat.mul_pos hd hN)).le
      (mul_nonneg (Nat.cast_nonneg _) (log_pos hD).le)
  have hlane : (if p ∣ d then 1 / (p : ℝ) else 1 / ((p : ℝ) - 2)) ≤
      1 / ((p : ℝ) - 2) := by
    split_ifs
    · exact one_div_le_one_div_of_le (by linarith) (by linarith)
    · exact le_rfl
  have hweight :
      (if p ∣ d then 1 / (p : ℝ) else 1 / ((p : ℝ) - 2)) /
          (1 - log (p : ℝ) / log (Q / d)) ≤
        1 / (((p : ℝ) - 2) * (1 - log (p : ℝ) / log (Q / d))) := by
    simpa only [div_div] using div_le_div_of_nonneg_right hlane hgap0.le
  rw [wu_inserted_theta_weight hN hd hp hp2 hpN hD, mul_left_comm]
  apply mul_le_mul_of_nonneg_left _ hw
  calc
    _ ≤ a * (1 / (((p : ℝ) - 2) * (1 - log (p : ℝ) / log (Q / d)))) :=
      mul_le_mul_of_nonneg_left hweight ha
    _ ≤ b * (1 / (((p : ℝ) - 2) * (1 - log (p : ℝ) / log (Q / d)))) :=
      mul_le_mul_of_nonneg_right hab (by positivity)
    _ = _ := by ring

/-- The actual geometric main term is normalized and moved to the
actual `d`-dependent interval. The only boundary term is the absolute
`p-2` R3; nonnegative upper terms permit omission of the terminal tail. -/
theorem reboxingGeometricMain_upper_prime_add_R3 (k : ℕ) {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N0 : ℕ, T ≤ N0 → ∀ N : ℕ, N0 ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → t ≤ 10 →
      let q := (N : ℝ) ^ (1 / 2 - δ) / (∏ l, V l)
      ∀ r : ℕ, reboxingAlpha q Δ t r ≤ q ^ (1 / s) →
        q ^ (1 / s) < reboxingAlpha q Δ t (r + 1) →
        reboxingGeometricMain true k N0 N δ Δ V t r
            (fun j => reboxingS1 q Δ t (j + 1)) ≤
          reboxingPrimeSum false N δ s t (convolutionWuWindows N Δ V)
            (fun d p => wuEffectiveCoefficient true (k + 1) δ N0
              (log ((N : ℝ) ^ (1 / 2 - δ) / d) / log p - 1)) +
          reboxingR3Absolute true k N0 N δ Δ V t := by
  obtain ⟨T1, hT14, hparameters⟩ := reboxing_source_parameters k hδ hδhi
  obtain ⟨T2, hT2⟩ := eventually_atTop.mp
    (wuEffectiveCoefficient_uniform_monotone_bound true (k + 1) (by omega)
      hδ (by linarith : δ < 1 / 2))
  obtain ⟨T3, hT3⟩ := eventually_atTop.mp
    (wuEffectiveCoefficient_uniform_signed_bounds true (k + 1) (by omega)
      hδ (by linarith : δ < 1 / 2))
  obtain ⟨T4, hT4⟩ := eventually_atTop.mp
    (((tendsto_rpow_atTop (pow_pos hδ (k + 2))).comp
      tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop (4 : ℝ)))
  refine ⟨max T1 (max T2 (max T3 T4)), hT14.trans (le_max_left _ _), ?_⟩
  intro N0 hN0 N hN i Δ V hb s t hs hst ht q r hrlo hrhi
  have hN01 : T1 ≤ N0 := by omega
  have hN02 : T2 ≤ N0 := by omega
  have hN03 : T3 ≤ N0 := by omega
  have hN04 : T4 ≤ N0 := by omega
  have hN4 : 4 ≤ N := hT14.trans (hN01.trans hN)
  have hN2 : 2 ≤ N := by omega
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hNpos : (0 : ℝ) < N := by linarith
  have hΔ : 1 < Δ := by
    have hpow := rpow_pos_of_pos (log_pos hNr) (-4 : ℝ)
    linarith [hb.2.1]
  have hΔ0 : 0 < Δ := by linarith
  have hV : ∀ j, 0 < V j := fun j =>
    (rpow_pos_of_pos hNpos _).trans_le (hb.2.2.2.2.1 j)
  let Q := (N : ℝ) ^ (1 / 2 - δ)
  let W := convolutionWuWindows N Δ V
  let a := reboxingAlpha q Δ t
  let g := fun d p : ℕ => wuEffectiveCoefficient true (k + 1) δ N0
    (log (Q / d) / log p - 1)
  let F := fun d p : ℕ =>
    g d p / (((p : ℝ) - 2) * (1 - log (p : ℝ) / log (Q / d)))
  let b := fun d : ℕ =>
    wuSingularSeries (d * N) / ((Nat.totient d : ℝ) * log (Q / d))
  let w := fun d : ℕ => (convolutionCoeff W d : ℝ) *
    wuSingularSeries (d * N) / ((Nat.totient d : ℝ) * log (Q / d))
  have hQ : 0 < Q := rpow_pos_of_pos hNpos _
  have hq : 1 < q :=
    (one_lt_rpow hNr (pow_pos hδ (k + 1))).trans_le
      (reboxing_box_level_ge_lower hN2 hδ hδhi hb)
  have hq0 : 0 < q := by linarith
  have hs0 : 0 < s := by linarith
  have ht0 : 0 < t := by linarith
  have hY4 : 4 ≤ q ^ (1 / t) :=
    (hT4 N (hN04.trans hN)).trans
      (reboxing_endpoint_lower hN2 hδ hδhi hb ht0 ht le_rfl)
  have hmono := (hT2 N0 hN02).1
  have hcoeff : ∀ u ∈ Set.Icc (1 : ℝ) 10,
      0 ≤ wuEffectiveCoefficient true (k + 1) δ N0 u := by
    intro u hu
    exact (hT3 N0 hN03 u hu).1
  have hli : 0 ≤ 4 * logarithmicIntegral N := by
    have hli0 : 0 ≤ logarithmicIntegral N :=
      (by positivity : (0 : ℝ) ≤ N / (2 * log N)).trans (box_trueLi_lower hN4)
    positivity
  have hsupport := fun d hd => reboxing_support_level_bounds hQ.le hΔ0 hV
    (N := N) (d := d) hd
  have hpos := fun d hd =>
    (reboxing_support_product_bounds hΔ0 (fun j => (hV j).le) (N := N) (d := d) hd).1
  have hD : ∀ d ∈ boxConvolutionSupport W, 1 < Q / d :=
    fun d hd => hq.trans_le (hsupport d hd).1
  have hb0 : ∀ d ∈ boxConvolutionSupport W, 0 ≤ b d := by
    intro d hd
    exact div_nonneg (wuSingularSeries_pos _ (Nat.mul_pos (hpos d hd) (by omega))).le
      (mul_nonneg (Nat.cast_nonneg _) (log_pos (hD d hd)).le)
  have hw0 : ∀ d ∈ boxConvolutionSupport W, 0 ≤ w d := by
    intro d hd
    have he : w d = (convolutionCoeff W d : ℝ) * b d := by dsimp [w, b]; ring
    rw [he]
    exact mul_nonneg (Nat.cast_nonneg _) (hb0 d hd)
  obtain ⟨r', hrlo', hrhi', hp⟩ :=
    hparameters N (hN01.trans hN) i Δ V hb s t hs hst ht
  have herr : r' = r :=
    reboxingAlpha_terminal_unique hq0 hΔ ⟨hrlo', hrhi'⟩ ⟨hrlo, hrhi⟩
  subst r'
  have hblocks :
      reboxingGeometricMain true k N0 N δ Δ V t r
          (fun j => reboxingS1 q Δ t (j + 1)) ≤
        4 * logarithmicIntegral N *
          ∑ j ∈ range r, ∑ d ∈ boxConvolutionSupport W,
            (convolutionCoeff W d : ℝ) *
              ∑ p ∈ primeWindow N (a j) (a (j + 1)), b d * F d p := by
    unfold reboxingGeometricMain
    rw [mul_sum]
    apply sum_le_sum
    intro j hj
    have hjr : j + 1 ≤ r := by have := mem_range.mp hj; omega
    have hpj := hp (j + 1) (by omega) hjr
    simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right] at hpj
    obtain ⟨_, hjhi, _, hS1lo, hS1hi, _, _, hatoms⟩ := hpj
    rw [boxTheta_cons, mul_left_comm
      (wuEffectiveCoefficient true (k + 1) δ N0 (reboxingS1 q Δ t (j + 1)))]
    apply mul_le_mul_of_nonneg_left _ hli
    simp only [mul_sum]
    apply sum_le_sum
    intro d hd
    apply sum_le_sum
    intro p hpmem
    have hatom := hatoms d hd p hpmem
    obtain ⟨hpp, hpN, hpY, hpZ⟩ := mem_primeWindow.mp hpmem
    have hstart : q ^ (1 / t) ≤ a j := by
      simpa only [a, reboxingAlpha_zero] using
        (reboxingAlpha_strictMono (t := t) hq0 hΔ).monotone
          (show (0 : ℝ) ≤ j by positivity)
    have hp4 : (4 : ℝ) ≤ p := hY4.trans (hstart.trans hpY)
    have hp2 : 2 < p := by exact_mod_cast (show (2 : ℝ) < p by linarith)
    have hpupper : (p : ℝ) ≤ (Q / d) ^ (1 / 2 : ℝ) :=
      hpZ.le.trans (hjhi.trans
        ((reboxing_support_cutoff_bounds hQ.le hΔ0 hV hs0 hd).1.trans
          (rpow_le_rpow_of_exponent_le (hD d hd).le
            (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hs))))
    have hc := wu_inserted_theta_upper_coefficient (Q := Q)
      (show 0 < N by omega) (hpos d hd) hpp hp2 hpN (hD d hd) hpupper
      (hcoeff _ ⟨hS1lo, hS1hi⟩)
      (hmono ⟨hS1lo, hS1hi⟩ ⟨hatom.2.2.1, hatom.2.2.2.1⟩ hatom.1)
    rw [mul_left_comm
      (wuEffectiveCoefficient true (k + 1) δ N0 (reboxingS1 q Δ t (j + 1)))]
    exact mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg (convolutionCoeff W d))
  have hpart := reboxingAlpha_convolution_sum_partition (t := t) hq0 hΔ N r W
    (fun d p => b d * F d p)
  rw [← hpart] at hblocks
  have hrect :
      reboxingGeometricMain true k N0 N δ Δ V t r
          (fun j => reboxingS1 q Δ t (j + 1)) ≤
        4 * logarithmicIntegral N *
          ∑ d ∈ boxConvolutionSupport W,
            w d * ∑ p ∈ primeWindow N (a 0) (a r), F d p := by
    convert hblocks using 1
    congr 1
    apply sum_congr rfl
    intro d _
    rw [← mul_sum]
    dsimp [w, b]
    ring
  have hwindow : ∀ d ∈ boxConvolutionSupport W,
      (∑ p ∈ primeWindow N (a 0) (a r), F d p) ≤
        (∑ p ∈ primeWindow N (wuLocalCutoff N δ d t) (wuLocalCutoff N δ d s), F d p) +
        ∑ p ∈ primeWindow N (q ^ (1 / t)) ((Q / d) ^ (1 / t)), |F d p| := by
    intro d hd
    let A := primeWindow N (a 0) (a r)
    let B := primeWindow N (wuLocalCutoff N δ d t) (wuLocalCutoff N δ d s)
    let C := primeWindow N (q ^ (1 / t)) ((Q / d) ^ (1 / t))
    have hsub : A ⊆ B ∪ C := by
      intro p hpA
      obtain ⟨hpp, hpc, hpl, hpu⟩ := mem_primeWindow.mp hpA
      have hlow : q ^ (1 / t) ≤ (p : ℝ) := by
        simpa only [a, reboxingAlpha_zero] using hpl
      by_cases hc : (p : ℝ) < (Q / d) ^ (1 / t)
      · exact mem_union_right _ (mem_primeWindow.mpr ⟨hpp, hpc, hlow, hc⟩)
      · exact mem_union_left _ (mem_primeWindow.mpr ⟨hpp, hpc, le_of_not_gt hc,
          hpu.trans_le (hrlo.trans (reboxing_support_cutoff_bounds hQ.le hΔ0 hV hs0 hd).1)⟩)
    have hdis : Disjoint B C := by
      apply disjoint_left.mpr
      intro p hpB hpC
      have h1 := (mem_primeWindow.mp hpB).2.2.1
      have h2 := (mem_primeWindow.mp hpC).2.2.2
      exact (not_lt_of_ge h1) h2
    have hF0 : ∀ p ∈ B, 0 ≤ F d p := by
      intro p hpB
      have hp' := mem_primeWindow.mp hpB
      have hpr : (1 : ℝ) < p := by exact_mod_cast hp'.1.one_lt
      have hu := wu_buchstab_prime_parameter_mem hN2 hδ
        (by linarith : δ < 1 / 2) hb hs hst ht hd hpB
      have hlog : log ((Q / d) / p) / log p = log (Q / d) / log p - 1 := by
        rw [log_div (by linarith [hD d hd] : Q / d ≠ 0)
          (by linarith : (p : ℝ) ≠ 0), sub_div, div_self (log_pos hpr).ne']
      change 1 ≤ log ((Q / d) / p) / log p ∧
        log ((Q / d) / p) / log p ≤ 10 at hu
      rw [hlog] at hu
      have hg0 : 0 ≤ g d p := hcoeff _ hu
      have hp4 : (4 : ℝ) ≤ p := hY4.trans
        ((reboxing_support_cutoff_bounds hQ.le hΔ0 hV ht0 hd).1.trans hp'.2.2.1)
      have hpupper : (p : ℝ) ≤ (Q / d) ^ (1 / 2 : ℝ) :=
        hp'.2.2.2.le.trans (rpow_le_rpow_of_exponent_le (hD d hd).le
          (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hs))
      have hw := (reboxing_prime_weight_le_four_div (hD d hd) hp4 hpupper).1
      dsimp only [F]
      rw [div_eq_mul_inv]
      exact mul_nonneg hg0 (by simpa only [one_div] using hw)
    calc
      _ ≤ ∑ p ∈ A, |F d p| := sum_le_sum fun _ _ => le_abs_self _
      _ ≤ ∑ p ∈ B ∪ C, |F d p| :=
        sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => abs_nonneg _)
      _ = _ := by
        rw [sum_union hdis]
        congr 1
        exact sum_congr rfl fun p hpB => abs_of_nonneg (hF0 p hpB)
  apply hrect.trans
  unfold reboxingPrimeSum reboxingR3Absolute
  simp only [Bool.false_eq_true, if_false]
  rw [← mul_add, ← sum_add_distrib]
  apply mul_le_mul_of_nonneg_left _ hli
  apply sum_le_sum
  intro d hd
  rw [← mul_add]
  exact mul_le_mul_of_nonneg_left (hwindow d hd) (hw0 d hd)

/-- Actual source raw sum to the actual effective-coefficient prime sum.
R1, R2 and R3 are consumed in one uniform epsilon ledger; no raw-sum
comparison or error certificate is a caller hypothesis. -/
theorem reboxingRawPrimeSum_upper_prime (k : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N0 : ℕ, T ≤ N0 → ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → t ≤ 10 →
        reboxingRawPrimeSum true N δ s t (convolutionWuWindows N Δ V) ≤
          reboxingPrimeSum false N δ s t (convolutionWuWindows N Δ V)
            (fun d p => wuEffectiveCoefficient true (k + 1) δ N0
              (log ((N : ℝ) ^ (1 / 2 - δ) / d) / log p - 1)) +
          ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  obtain ⟨T1, hT14, hraw⟩ := reboxingRawPrimeSum_upper_geometric k hδ hδhi (half_pos hε)
  obtain ⟨T2, _, hnormalize⟩ := reboxingGeometricMain_upper_prime_add_R3 k hδ hδhi
  obtain ⟨T3, _, hR3⟩ := reboxingR3Absolute_relative k hδ hδhi (half_pos hε)
  refine ⟨max T1 (max T2 T3), hT14.trans (le_max_left _ _), ?_⟩
  intro N0 hN0 N hN he i Δ V hb s t hs hst ht
  have h1 : T1 ≤ N0 := by omega
  have h2 : T2 ≤ N0 := by omega
  have h3 : T3 ≤ N0 := by omega
  obtain ⟨r, hrlo, hrhi, hmain⟩ := hraw N0 h1 N hN he i Δ V hb s t hs hst ht
  have hprime := hnormalize N0 h2 N hN i Δ V hb s t hs hst ht r hrlo hrhi
  have hboundary := (hR3 N0 h3 N hN i Δ V hb t (by linarith) ht true).2
  linarith

end Wu2008DoubleSieve
