import MathlibNt.Wu2008DoubleSieve.Omega2IntegralTransform
import MathlibNt.Wu2008DoubleSieve.ReboxingPrimeIntegral
import MathlibNt.Wu2008DoubleSieve.ReboxingEffectiveTransport

/-!
# The actual normalized Omega2 prime sum

Wu04 (5.2): the fixed-cutoff coordinate is transported through the
already proved signed prime integral. Divisors of N and of d are paid
separately, with one threshold before the source box and both parameters.
-/

namespace Wu2008DoubleSieve

open Finset Set Filter Real
open scoped Classical Topology Interval
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418

theorem omega2_window_parameter_mem {q p s t : ℝ}
    (hq : 1 < q) (hp : 1 < p) (hs : 2 ≤ s) (_hst : s ≤ t)
    (ht : 3 ≤ t) (ht5 : t ≤ 5)
    (hlo : q ^ (1 / t) ≤ p) (hhi : p < q ^ (1 / s)) :
    t * (1 - log p / log q) ∈ Icc (1 : ℝ) 10 := by
  have hshift := buchstab_shifted_parameter hq hp
    (show 0 < s by linarith) (show 0 < t by linarith) hlo hhi
  have heq : log (q / p) / log p = log q / log p - 1 := by
    rw [log_div (by linarith : q ≠ 0) (by linarith : p ≠ 0),
      sub_div, div_self (log_pos hp).ne']
  rw [heq] at hshift
  rw [← omega2_prime_coordinate hq hp]
  exact omega2_coordinate_mem ht ht5 ⟨by linarith [hshift.1], by linarith [hshift.2]⟩

theorem omega2_box_prime_integral_uniform (k : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ f : ℝ → ℝ, MonotoneOn f (Icc 1 10) →
      (∀ u ∈ Icc (1 : ℝ) 10, |f u| ≤ 11) →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → 3 ≤ t → t ≤ 5 →
      |reboxingPrimeSum false N δ s t (convolutionWuWindows N Δ V)
          (fun d p => f (t * (1 - log p / log ((N : ℝ) ^ (1 / 2 - δ) / d)))) -
        (∫ u in (1 - 1 / s)..(1 - 1 / t), f (t * u) / (u * (1 - u))) *
          boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V)| ≤
      ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  obtain ⟨Q0, _, hprime⟩ := omega2_source_prime_integral_uniform
    (show (0 : ℝ) ≤ 11 by norm_num) (half_pos hε)
  let η := wuLocalExponent k δ / 10
  have hη : 0 < η := div_pos (wuLocalExponent_pos k hδ hδhi) (by norm_num)
  obtain ⟨T1, hdelete⟩ := primeCoefficient_all_to_coprime_uniform hη
    (show (0 : ℝ) ≤ 11 by norm_num) (half_pos hε)
  have hgrow : Tendsto (fun N : ℕ => (N : ℝ) ^ (wuLocalExponent k δ)) atTop atTop :=
    (tendsto_rpow_atTop (wuLocalExponent_pos k hδ hδhi)).comp tendsto_natCast_atTop_atTop
  obtain ⟨T2, hT2⟩ := eventually_atTop.mp (hgrow.eventually (eventually_ge_atTop Q0))
  refine ⟨max 4 (max T1 T2), le_max_left _ _, ?_⟩
  intro N hN i Δ V hb f hf hfb s t hs hst ht ht5
  have hN4 : 4 ≤ N := (le_max_left _ _).trans hN
  have hT1N : T1 ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hT2N : T2 ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  let W := convolutionWuWindows N Δ V
  let Q := (N : ℝ) ^ (1 / 2 - δ)
  let I := ∫ u in (1 - 1 / s)..(1 - 1 / t), f (t * u) / (u * (1 - u))
  let g : ℕ → ℕ → ℝ := fun d p => f (t * (1 - log p / log (Q / d)))
  have hgeom := fun d hd => wu_buchstab_prime_window_bounds (show 2 ≤ N by omega)
    hδ hδhi hb hs hst (show t ≤ 10 by linarith) (d := d) hd
  have hpoint (d : ℕ) (hd : d ∈ boxConvolutionSupport W) :
      |(∑ p ∈ primeWindow N (wuLocalCutoff N δ d t) (wuLocalCutoff N δ d s),
          g d p / (((p : ℝ) - 2) * (1 - log p / log (Q / d)))) - I| ≤ ε := by
    have hsp := wuLocal_support_bounds (show 1 ≤ N by omega) hδ hδhi
      hb.2.2.2.2.1 ((boxSquaredPrefixes_iff _ _).mp hb.2.2.2.2.2) hd
    have hp := hprime (Q / d) ((hT2 N hT2N).trans hsp.2.2) f hf hfb s t hs hst ht ht5
    have hdif := hdelete N hT1N (Q / d) (wuLocalCutoff N δ d t)
      (wuLocalCutoff N δ d s) (g d) (hgeom d hd).2.2.1
      (hgeom d hd).2.2.2.1 (hgeom d hd).2.2.2.2 (by
        intro p hp
        have hp' := mem_primeWindow.mp hp
        exact hfb _ (omega2_window_parameter_mem (hgeom d hd).2.2.1
          (by exact_mod_cast hp'.1.one_lt) hs hst ht ht5 hp'.2.2.1 hp'.2.2.2))
    rw [abs_sub_comm] at hdif
    exact (abs_sub_le _ _ _).trans ((add_le_add hdif hp).trans_eq (by ring))
  have hli : 0 ≤ 4 * logarithmicIntegral N :=
    mul_nonneg (by norm_num) ((by positivity : (0 : ℝ) ≤ N / (2 * log N)).trans
      (box_trueLi_lower hN4))
  let w : ℕ → ℝ := fun d => (convolutionCoeff W d : ℝ) * wuSingularSeries (d * N) /
      ((Nat.totient d : ℝ) * log (Q / d))
  have hw (d : ℕ) (hd : d ∈ boxConvolutionSupport W) : 0 ≤ w d := by
    have h := hgeom d hd
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg _)
      (wuSingularSeries_pos _ (Nat.mul_pos h.1 (by omega))).le)
      (mul_nonneg (Nat.cast_nonneg _) (log_pos h.2.2.1).le)
  change |4 * logarithmicIntegral N *
      (∑ d ∈ boxConvolutionSupport W, w d *
        ∑ p ∈ primeWindow N (wuLocalCutoff N δ d t) (wuLocalCutoff N δ d s),
          g d p / (((p : ℝ) - 2) * (1 - log p / log (Q / d)))) -
      I * (4 * logarithmicIntegral N * ∑ d ∈ boxConvolutionSupport W, w d)| ≤
    ε * (4 * logarithmicIntegral N * ∑ d ∈ boxConvolutionSupport W, w d)
  rw [mul_left_comm I, ← mul_sub, abs_mul, abs_of_nonneg hli, mul_left_comm ε]
  apply mul_le_mul_of_nonneg_left _ hli
  rw [mul_comm I, Finset.sum_mul, ← Finset.sum_sub_distrib]
  simp only [← mul_sub]
  calc
    _ ≤ ∑ d ∈ boxConvolutionSupport W, |w d *
        ((∑ p ∈ primeWindow N (wuLocalCutoff N δ d t) (wuLocalCutoff N δ d s),
          g d p / (((p : ℝ) - 2) * (1 - log p / log (Q / d)))) - I)| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ boxConvolutionSupport W, w d * ε := by
      apply Finset.sum_le_sum
      intro d hd
      rw [abs_mul, abs_of_nonneg (hw d hd)]
      exact mul_le_mul_of_nonneg_left (hpoint d hd) (hw d hd)
    _ = _ := by rw [← Finset.sum_mul, mul_comm]

theorem omega2_effective_prime_transport_relative (upper : Bool) (k : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N0 : ℕ, T ≤ N0 → ∀ N : ℕ, N0 ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → 3 ≤ t → t ≤ 5 →
        let W := convolutionWuWindows N Δ V
        let g := fun d p : ℕ => wuEffectiveCoefficient upper (k + 1) δ N0
          (t * (1 - log p / log ((N : ℝ) ^ (1 / 2 - δ) / d)))
        |reboxingPrimeSum false N δ s t W g - reboxingPrimeSum true N δ s t W g| ≤
          ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) W := by
  let η := wuLocalExponent k δ / 10
  have hη : 0 < η := div_pos (wuLocalExponent_pos k hδ hδhi) (by norm_num)
  obtain ⟨T1, hT1⟩ := eventually_atTop.mp
    (wuEffectiveCoefficient_uniform_abs_le_eleven upper (k + 1) (by omega) hδ hδhi)
  obtain ⟨T2, hT2⟩ := eventually_atTop.mp
    (((tendsto_rpow_atTop hη).comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (max 4 (44 / (η * ε)))))
  refine ⟨max 4 (max T1 T2), le_max_left _ _, ?_⟩
  intro N0 hN0 N hN i Δ V hb s t hs hst ht ht5
  dsimp only
  have hN4 : 4 ≤ N := (le_max_left _ _).trans (hN0.trans hN)
  have hN01 : T1 ≤ N0 := (le_max_left _ _).trans ((le_max_right _ _).trans hN0)
  have hN2 : T2 ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans (hN0.trans hN))
  have hlarge := hT2 N hN2
  simp only [Function.comp_apply] at hlarge
  let g := fun d p : ℕ => wuEffectiveCoefficient upper (k + 1) δ N0
    (t * (1 - log p / log ((N : ℝ) ^ (1 / 2 - δ) / d)))
  have hg : ∀ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
      ∀ p ∈ primeWindow N (wuLocalCutoff N δ d t) (wuLocalCutoff N δ d s), |g d p| ≤ 11 := by
    intro d hd p hp
    have hgeom := wu_buchstab_prime_window_bounds (show 2 ≤ N by omega)
      hδ hδhi hb hs hst (show t ≤ 10 by linarith) hd
    have hp' := mem_primeWindow.mp hp
    exact hT1 N0 hN01 _ (omega2_window_parameter_mem hgeom.2.2.1
      (by exact_mod_cast hp'.1.one_lt) hs hst ht ht5 hp'.2.2.1 hp'.2.2.2)
  have hf := reboxingPrimeSum_transport_bound hN4 hδ hδhi hb hs hst (by linarith)
    (by norm_num : (0 : ℝ) ≤ 11) ((le_max_left _ _).trans hlarge) hg
  have hY : 0 < (N : ℝ) ^ η := rpow_pos_of_pos (by exact_mod_cast (show 0 < N by omega)) _
  have hcpos : 0 < 11 * (4 / (η * (N : ℝ) ^ η)) := by positivity
  have hTnon : 0 ≤ boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) :=
    nonneg_of_mul_nonneg_right ((abs_nonneg _).trans hf) hcpos
  have hc : 11 * (4 / (η * (N : ℝ) ^ η)) ≤ ε := by
    have hl := (div_le_iff₀ (mul_pos hη hε)).1 ((le_max_right _ _).trans hlarge)
    have h44 : 44 / (η * (N : ℝ) ^ η) ≤ ε :=
      (div_le_iff₀ (mul_pos hη hY)).2 (by nlinarith [hl])
    convert h44 using 1
    ring
  exact hf.trans (mul_le_mul_of_nonneg_right hc hTnon)

theorem omega2_effective_prime_integral_relative (upper : Bool) (k : ℕ)
    {δ ε : ℝ} (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N0 : ℕ, T ≤ N0 → ∀ N : ℕ, N0 ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → 3 ≤ t → t ≤ 5 →
      |reboxingPrimeSum true N δ s t (convolutionWuWindows N Δ V)
          (fun d p => wuEffectiveCoefficient upper (k + 1) δ N0
            (t * (1 - log p / log ((N : ℝ) ^ (1 / 2 - δ) / d)))) -
        (∫ u in (1 - 1 / s)..(1 - 1 / t),
          wuEffectiveCoefficient upper (k + 1) δ N0 (t * u) / (u * (1 - u))) *
          boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V)| ≤
      ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  obtain ⟨T1, hT14, hT1⟩ := omega2_box_prime_integral_uniform k hδ hδhi (half_pos hε)
  obtain ⟨T2, _, hT2⟩ := omega2_effective_prime_transport_relative upper k hδ hδhi (half_pos hε)
  obtain ⟨T3, hT3⟩ := eventually_atTop.mp
    ((wu_effective_threshold_uniform_monotone upper (k + 1) (by omega) hδ hδhi).and
      (wuEffectiveCoefficient_uniform_abs_le_eleven upper (k + 1) (by omega) hδ hδhi))
  refine ⟨max T1 (max T2 T3), hT14.trans (le_max_left _ _), ?_⟩
  intro N0 hN0 N hN i Δ V hb s t hs hst ht ht5
  have hm := hT3 N0 ((le_max_right _ _).trans ((le_max_right _ _).trans hN0))
  have hi := hT1 N ((le_max_left _ _).trans (hN0.trans hN)) i Δ V hb
    (wuEffectiveCoefficient upper (k + 1) δ N0) hm.1 hm.2 s t hs hst ht ht5
  have hp := hT2 N0 ((le_max_left _ _).trans ((le_max_right _ _).trans hN0))
    N hN i Δ V hb s t hs hst ht ht5
  dsimp only at hp
  rw [abs_sub_comm] at hp
  exact (abs_sub_le _ _ _).trans ((add_le_add hp hi).trans_eq (by ring))

end Wu2008DoubleSieve
