import MathlibNt.Wu2008DoubleSieve.ReboxingLowerNormalizationBoundary

/-!
# Signed lower normalization on all actual geometric blocks

The exact inserted factor is `1/p` when `p` divides the old convolution
atom, not `1/(p-2)`. Its replacement is paid against the entire positive
repeated-prime lane. No sign assumption on `a+h` is made.
-/

namespace Wu2008DoubleSieve

open Finset Filter Real
open scoped Classical Topology
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418

theorem wu_inserted_theta_lower_coefficient {N d p : ℕ} {Q a b B : ℝ}
    (hN : 0 < N) (hd : 0 < d) (hp : p.Prime) (hp2 : 2 < p) (hpN : p.Coprime N)
    (hQ : 1 < Q / d) (hupper : (p : ℝ) ≤ (Q / d) ^ (1 / 2 : ℝ))
    (hab : a ≤ b) (haB : a ≤ B) (hB : 0 ≤ B) :
    (wuSingularSeries (d * N) / ((Nat.totient d : ℝ) * log (Q / d))) *
        (a / (((p : ℝ) - 2) * (1 - log (p : ℝ) / log (Q / d)))) ≤
      b * (wuSingularSeries ((d * p) * N) /
        ((Nat.totient (d * p) : ℝ) * log (Q / (d * p)))) +
      B * (wuSingularSeries (d * N) / ((Nat.totient d : ℝ) * log (Q / d))) *
        (if p ∣ d then 1 / (((p : ℝ) - 2) * (1 - log (p : ℝ) / log (Q / d))) else 0) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp2r : (2 : ℝ) < p := by exact_mod_cast hp2
  have hratio := reboxing_log_ratio_half hQ hp0 hupper
  have hh : 0 < 1 - log (p : ℝ) / log (Q / d) := by linarith
  let w := wuSingularSeries (d * N) / ((Nat.totient d : ℝ) * log (Q / d))
  have hw : 0 ≤ w := div_nonneg (wuSingularSeries_pos _ (Nat.mul_pos hd hN)).le
    (mul_nonneg (Nat.cast_nonneg _) (log_pos hQ).le)
  rw [wu_inserted_theta_weight hN hd hp hp2 hpN hQ]
  by_cases hpd : p ∣ d
  · rw [if_pos hpd]
    let E := (1 / (p : ℝ)) / (1 - log (p : ℝ) / log (Q / d))
    let F := 1 / (((p : ℝ) - 2) * (1 - log (p : ℝ) / log (Q / d)))
    have hE : 0 ≤ E := by dsimp [E]; positivity
    have hEF : E ≤ F := by
      dsimp [E, F]
      rw [div_div]
      exact one_div_le_one_div_of_le (mul_pos (by linarith) hh)
        (mul_le_mul_of_nonneg_right (by linarith) hh.le)
    have h1 := mul_le_mul_of_nonneg_right hab hE
    have h2 := mul_le_mul_of_nonneg_right haB (sub_nonneg.mpr hEF)
    have h3 := mul_nonneg hB hE
    have hscalar : a * F ≤ b * E + B * F := by nlinarith
    have hm := mul_le_mul_of_nonneg_left hscalar hw
    convert hm using 2
    · rfl
    · dsimp [F]
      ring
    · simp only [w, E, F, if_pos hpd]
      ring
  · rw [if_neg hpd]
    have hscalar := mul_le_mul_of_nonneg_right hab
      (show 0 ≤ (1 / ((p : ℝ) - 2)) / (1 - log (p : ℝ) / log (Q / d)) by positivity)
    have hm := mul_le_mul_of_nonneg_left hscalar hw
    convert hm using 2
    · rfl
    · rw [div_div]
      ring
    · simp only [w, if_neg hpd]
      ring

noncomputable def reboxingLowerGeometricPrime {i : ℕ} (k N0 N : ℕ)
    (δ Δ : ℝ) (V : Fin i → ℝ) (t : ℝ) (r : ℕ) : ℝ :=
  4 * logarithmicIntegral N *
    ∑ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
      ((convolutionCoeff (convolutionWuWindows N Δ V) d : ℝ) *
        wuSingularSeries (d * N) /
        ((Nat.totient d : ℝ) * log ((N : ℝ) ^ (1 / 2 - δ) / d))) *
      ∑ p ∈ primeWindow N
          (reboxingAlpha ((N : ℝ) ^ (1 / 2 - δ) / (∏ l, V l)) Δ t 0)
          (reboxingAlpha ((N : ℝ) ^ (1 / 2 - δ) / (∏ l, V l)) Δ t r),
        wuEffectiveCoefficient false (k + 1) δ N0
          (log ((N : ℝ) ^ (1 / 2 - δ) / d) / log p - 1) /
          (((p : ℝ) - 2) * (1 - log (p : ℝ) / log ((N : ℝ) ^ (1 / 2 - δ) / d)))

/-- Exact normalization and the actual monotone lower coefficient
give a finite, fully summed comparison. The error is one global
repeated-prime lane, not one copy per geometric block. -/
theorem reboxingLowerGeometricPrime_le_main_add_repeated (k : ℕ) {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N0 : ℕ, T ≤ N0 → ∀ N : ℕ, N0 ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → t ≤ 10 → ∀ r : ℕ,
      let q := (N : ℝ) ^ (1 / 2 - δ) / (∏ l, V l)
      (reboxingAlpha q Δ t r ≤ q ^ (1 / s) ∧
        q ^ (1 / s) < reboxingAlpha q Δ t (r + 1)) →
      reboxingLowerGeometricPrime k N0 N δ Δ V t r ≤
        reboxingGeometricMain false k N0 N δ Δ V t r
          (fun j => reboxingS2 q Δ t i (j + 1)) +
        11 * reboxingRepeatedTheta N ((N : ℝ) ^ (1 / 2 - δ)) (δ ^ (k + 2))
          (convolutionWuWindows N Δ V) := by
  obtain ⟨T1, hT14, hparameters⟩ := reboxing_source_parameters k hδ hδhi
  obtain ⟨T2, hT2⟩ := eventually_atTop.mp
    (wu_effective_threshold_uniform_monotone false (k + 1) (by omega)
      hδ (by linarith : δ < 1 / 2))
  obtain ⟨T3, hT3⟩ := eventually_atTop.mp
    (wuEffectiveCoefficient_uniform_abs_le_eleven false (k + 1) (by omega)
      hδ (by linarith : δ < 1 / 2))
  obtain ⟨T4, hT4⟩ := eventually_atTop.mp
    (((tendsto_rpow_atTop (pow_pos hδ (k + 2))).comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (4 : ℝ)))
  refine ⟨max T1 (max T2 (max T3 T4)), hT14.trans (le_max_left _ _), ?_⟩
  intro N0 hN0 N hN i Δ V hb s t hs hst ht r
  dsimp only
  intro hr
  have h1 : T1 ≤ N := (le_max_left _ _).trans (hN0.trans hN)
  have h2 : T2 ≤ N0 := by omega
  have h3 : T3 ≤ N0 := by omega
  have h4 : T4 ≤ N := by omega
  have hN4 : 4 ≤ N := hT14.trans h1
  let Q := (N : ℝ) ^ (1 / 2 - δ)
  let q := Q / (∏ l, V l)
  let W := convolutionWuWindows N Δ V
  let f := wuEffectiveCoefficient false (k + 1) δ N0
  let u := fun d p : ℕ => log (Q / d) / log p - 1
  let w := fun d : ℕ => wuSingularSeries (d * N) / ((Nat.totient d : ℝ) * log (Q / d))
  let K := fun d p : ℕ => 1 / (((p : ℝ) - 2) * (1 - log (p : ℝ) / log (Q / d)))
  let P := primeWindow N (reboxingAlpha q Δ t 0) (reboxingAlpha q Δ t r)
  let Pj := fun j : ℕ => primeWindow N (reboxingAlpha q Δ t j) (reboxingAlpha q Δ t (j + 1))
  let I := fun d p : ℕ => wuSingularSeries ((d * p) * N) /
    ((Nat.totient (d * p) : ℝ) * log (Q / ((d : ℝ) * p)))
  let E := 4 * logarithmicIntegral N *
    ∑ d ∈ boxConvolutionSupport W, (convolutionCoeff W d : ℝ) * w d *
      ∑ p ∈ P, if p ∣ d then K d p else 0
  have hNreal : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hQpos : 0 < Q := rpow_pos_of_pos (by linarith) _
  have hV : ∀ l, 0 < V l := fun l =>
    (rpow_pos_of_pos (by linarith : (0 : ℝ) < N) _).trans_le (hb.2.2.2.2.1 l)
  have hΔ : 1 < Δ := by
    have hh := rpow_pos_of_pos (log_pos hNreal) (-4 : ℝ)
    linarith [hb.2.1]
  have hΔ0 : 0 < Δ := by linarith
  have hq : 1 < q := (one_lt_rpow hNreal (pow_pos hδ _)).trans_le
    (reboxing_box_level_ge_lower (by omega) hδ hδhi hb)
  have hq0 : 0 < q := by linarith
  have hD := fun d hd => reboxing_support_level_bounds hQpos.le hΔ0 hV (N := N) (d := d) hd
  have hsupport := fun d hd => wu_buchstab_prime_window_bounds (show 2 ≤ N by omega)
    hδ (by linarith : δ < 1 / 2) hb hs hst ht (d := d) hd
  have hw (d : ℕ) (hd : d ∈ boxConvolutionSupport W) : 0 ≤ w d :=
    div_nonneg (wuSingularSeries_pos _ (Nat.mul_pos (hsupport d hd).1 (by omega))).le
      (mul_nonneg (Nat.cast_nonneg _) (log_pos (hsupport d hd).2.2.1).le)
  have hli : 0 ≤ 4 * logarithmicIntegral N :=
    mul_nonneg (by norm_num) ((by positivity : (0 : ℝ) ≤ N / (2 * log N)).trans
      (box_trueLi_lower hN4))
  have hmono : MonotoneOn f (Set.Icc 1 10) := hT2 N0 h2
  obtain ⟨r0, hr0lo, hr0hi, hpdata⟩ := hparameters N h1 i Δ V hb s t hs hst ht
  have heqr : r = r0 := reboxingAlpha_terminal_unique hq0 hΔ hr ⟨hr0lo, hr0hi⟩
  subst r0
  have hgeom (d : ℕ) (hd : d ∈ boxConvolutionSupport W) (p : ℕ) (hp : p ∈ P) :
      (N : ℝ) ^ (δ ^ (k + 2)) ≤ p ∧
        (p : ℝ) < (Q / d) ^ (1 / 2 : ℝ) := by
    obtain ⟨_, _, hlo, hhi⟩ := mem_primeWindow.mp hp
    have hheight := reboxing_endpoint_lower (show 2 ≤ N by omega) hδ hδhi hb
      (show 0 < t by linarith) ht (le_refl (q ^ (1 / t)))
    have hupper := (reboxing_support_cutoff_bounds hQpos.le hΔ0 hV
      (show 0 < s by linarith) hd).1
    refine ⟨hheight.trans (by simpa only [reboxingAlpha_zero] using hlo), ?_⟩
    exact (hhi.trans_le (hr.1.trans hupper)).trans_le (hsupport d hd).2.2.2.2
  have hpoint (j : ℕ) (hj : j ∈ range r) (d : ℕ) (hd : d ∈ boxConvolutionSupport W)
      (p : ℕ) (hp : p ∈ Pj j) :
      w d * (f (u d p) * K d p) ≤
        f (reboxingS2 q Δ t i (j + 1)) * I d p +
          11 * w d * (if p ∣ d then K d p else 0) := by
    have hpj := hpdata (j + 1) (by omega) (by have := mem_range.mp hj; omega)
    simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right] at hpj
    have hu := hpj.2.2.2.2.2.2.2 d hd p hp
    have hmem : p ∈ P := by
      have hh := mem_primeWindow.mp hp
      have hm := (reboxingAlpha_strictMono (t := t) hq0 hΔ).monotone
      exact mem_primeWindow.mpr ⟨hh.1, hh.2.1,
        (hm (by positivity : (0 : ℝ) ≤ j)).trans hh.2.2.1,
        hh.2.2.2.trans_le (hm (by exact_mod_cast mem_range.mp hj))⟩
    have hp4 : (4 : ℝ) ≤ p := (hT4 N h4).trans (hgeom d hd p hmem).1
    have hp2 : 2 < p := by exact_mod_cast (show (2 : ℝ) < p by linarith)
    have hm := hmono ⟨hu.2.2.1, hu.2.2.2.1⟩
      ⟨hpj.2.2.2.2.2.1, hpj.2.2.2.2.2.2.1⟩ hu.2.1
    have hbnd := (le_abs_self (f (u d p))).trans (hT3 N0 h3 _ ⟨hu.2.2.1, hu.2.2.2.1⟩)
    have hh := wu_inserted_theta_lower_coefficient (show 0 < N by omega) (hsupport d hd).1
      (mem_primeWindow.mp hp).1 hp2 (mem_primeWindow.mp hp).2.1
      (hsupport d hd).2.2.1 (hgeom d hd p hmem).2.le hm hbnd (by norm_num : (0 : ℝ) ≤ 11)
    simpa only [w, u, f, K, I, q, Q, div_eq_mul_inv, one_mul] using hh
  have hfinite : reboxingLowerGeometricPrime k N0 N δ Δ V t r ≤
      reboxingGeometricMain false k N0 N δ Δ V t r
        (fun j => reboxingS2 q Δ t i (j + 1)) + 11 * E := by
    have hp := reboxingAlpha_convolution_sum_partition (t := t) hq0 hΔ N r W
      (fun d p => w d * (f (u d p) * K d p))
    have he := reboxingAlpha_convolution_sum_partition (t := t) hq0 hΔ N r W
      (fun d p => w d * (if p ∣ d then K d p else 0))
    have hsum : (∑ j ∈ range r, ∑ d ∈ boxConvolutionSupport W,
        (convolutionCoeff W d : ℝ) * ∑ p ∈ Pj j, w d * (f (u d p) * K d p)) ≤
      ∑ j ∈ range r, ∑ d ∈ boxConvolutionSupport W,
        (convolutionCoeff W d : ℝ) * ∑ p ∈ Pj j,
          (f (reboxingS2 q Δ t i (j + 1)) * I d p +
            11 * w d * (if p ∣ d then K d p else 0)) := by
      apply sum_le_sum
      intro j hj
      apply sum_le_sum
      intro d hd
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      exact sum_le_sum (fun p hp => hpoint j hj d hd p hp)
    have hh := mul_le_mul_of_nonneg_left hsum hli
    rw [← hp] at hh
    have he' : E = 4 * logarithmicIntegral N *
        ∑ j ∈ range r, ∑ d ∈ boxConvolutionSupport W,
          (convolutionCoeff W d : ℝ) * ∑ p ∈ Pj j,
            w d * (if p ∣ d then K d p else 0) := by
      rw [← he]
      dsimp [E, P]
      simp only [mul_sum, mul_assoc]
    rw [he']
    unfold reboxingGeometricMain
    simp only [boxTheta_cons]
    convert hh using 2
    · rfl
    · simp only [reboxingLowerGeometricPrime, w, f, u, K, W, q, Q,
        mul_sum, div_eq_mul_inv, mul_inv_rev, one_mul]
      apply sum_congr rfl
      intro d hd
      apply sum_congr rfl
      intro p hp
      ring
    · simp only [Pj, w, f, K, I, W, q, Q,
        mul_sum, sum_add_distrib, mul_add, div_eq_mul_inv, mul_inv_rev, one_mul]
      congr 1 <;>
        (apply sum_congr rfl
         intro j hj
         apply sum_congr rfl
         intro d hd
         apply sum_congr rfl
         intro p hp
         ring)
  have hE : E ≤ reboxingRepeatedTheta N Q (δ ^ (k + 2)) W := by
    unfold reboxingRepeatedTheta
    dsimp only [E]
    apply mul_le_mul_of_nonneg_left _ hli
    apply sum_le_sum
    intro d hd
    have hcoef : 0 ≤ (convolutionCoeff W d : ℝ) * w d :=
      mul_nonneg (Nat.cast_nonneg _) (hw d hd)
    have hsub : P.filter (fun p => p ∣ d) ⊆
        (primeWindow N ((N : ℝ) ^ (δ ^ (k + 2))) ((Q / d) ^ (1 / 2 : ℝ))).filter
          (fun p => p ∣ d) := by
      intro p hp
      obtain ⟨hp, hpd⟩ := mem_filter.mp hp
      have hp' := mem_primeWindow.mp hp
      exact mem_filter.mpr ⟨mem_primeWindow.mpr
        ⟨hp'.1, hp'.2.1, (hgeom d hd p hp).1, (hgeom d hd p hp).2⟩, hpd⟩
    have hsump : (∑ p ∈ P, if p ∣ d then K d p else 0) ≤
        ∑ p ∈ (primeWindow N ((N : ℝ) ^ (δ ^ (k + 2)))
          ((Q / d) ^ (1 / 2 : ℝ))).filter (fun p => p ∣ d), K d p := by
      rw [← sum_filter]
      apply sum_le_sum_of_subset_of_nonneg hsub
      intro p hp _
      have hp' := mem_primeWindow.mp (mem_filter.mp hp).1
      exact (reboxing_prime_weight_le_four_div (hsupport d hd).2.2.1
        ((hT4 N h4).trans hp'.2.2.1) hp'.2.2.2.le).1
    convert mul_le_mul_of_nonneg_left hsump hcoef using 1
    dsimp [w, K]
    ring
  exact hfinite.trans (add_le_add le_rfl
    (mul_le_mul_of_nonneg_left hE (show (0 : ℝ) ≤ 11 by norm_num)))

end Wu2008DoubleSieve
