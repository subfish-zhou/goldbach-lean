import MathlibNt.Wu2008DoubleSieve.Omega2ReboxingNormalization

/-!
# Both absolute normalized boundaries for Omega2

Taking `(s,t,r)=(t,t,0)` gives the lower source boundary. The actual
terminal index gives the upper boundary. Absolute values are inside
the prime sums, so no positivity of the finite lower coefficient is used.
-/

namespace Wu2008DoubleSieve

open Finset Filter Real
open scoped Classical Topology
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418

noncomputable def omega2BoundaryAbsolute {i : ℕ} (k N0 N : ℕ)
    (δ Δ : ℝ) (V : Fin i → ℝ) (s t : ℝ) (r : ℕ) : ℝ :=
  4 * logarithmicIntegral N *
    ∑ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
      ((convolutionCoeff (convolutionWuWindows N Δ V) d : ℝ) *
        wuSingularSeries (d * N) /
        ((Nat.totient d : ℝ) * log ((N : ℝ) ^ (1 / 2 - δ) / d))) *
      ∑ p ∈ primeWindow N
          (reboxingAlpha ((N : ℝ) ^ (1 / 2 - δ) / (∏ j, V j)) Δ t r)
          (((N : ℝ) ^ (1 / 2 - δ) / d) ^ (1 / s)),
        |wuEffectiveCoefficient false (k + 1) δ N0
          (omega2ParameterTransform t (log ((N : ℝ) ^ (1 / 2 - δ) / d) / log p - 1)) /
          (((p : ℝ) - 2) *
            (1 - log (p : ℝ) / log ((N : ℝ) ^ (1 / 2 - δ) / d)))|

theorem omega2BoundaryAbsolute_relative (k : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N0 : ℕ, T ≤ N0 → ∀ N : ℕ, N0 ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → 3 ≤ t → t ≤ 5 → ∀ r : ℕ,
      (reboxingAlpha ((N : ℝ) ^ (1 / 2 - δ) / (∏ j, V j)) Δ t r ≤
          ((N : ℝ) ^ (1 / 2 - δ) / (∏ j, V j)) ^ (1 / s) ∧
        ((N : ℝ) ^ (1 / 2 - δ) / (∏ j, V j)) ^ (1 / s) <
          reboxingAlpha ((N : ℝ) ^ (1 / 2 - δ) / (∏ j, V j)) Δ t (r + 1)) →
      0 ≤ omega2BoundaryAbsolute k N0 N δ Δ V s t r ∧
        omega2BoundaryAbsolute k N0 N δ Δ V s t r ≤
          ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  let α := δ ^ (k + 2)
  let K := 2 * ((k : ℝ) + 1)
  let B := 2 * K / α + 2
  have hα : 0 < α := pow_pos hδ _
  have hK : 0 < K := by dsimp [K]; positivity
  obtain ⟨T1, hT1⟩ := reboxing_short_prime_mass hα hK
  obtain ⟨T2, _, hT2⟩ := reboxing_parameter_mesh_eventually k hδ hδhi
  obtain ⟨T3, hT3⟩ := eventually_atTop.mp
    (wuEffectiveCoefficient_uniform_abs_le_eleven false (k + 1) (by omega)
      hδ (by linarith : δ < 1 / 2))
  have hlogt : Tendsto (fun N : ℕ => log (N : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨T4, hT4⟩ := eventually_atTop.mp
    (((tendsto_rpow_atTop hα).comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (4 : ℝ)))
  obtain ⟨T5, hT5⟩ := eventually_atTop.mp
    (((tendsto_pow_atTop (by decide : 5 ≠ 0)).comp hlogt).eventually
      (eventually_ge_atTop (44 * B / ε)))
  refine ⟨max 4 (max T1 (max T2 (max T3 (max T4 T5)))), le_max_left _ _, ?_⟩
  intro N0 hN0 N hN i Δ V hb s t hs hst ht3 ht5 r hr
  have hN4 : 4 ≤ N := by omega
  have hN01 : T1 ≤ N0 := by omega
  have hN02 : T2 ≤ N0 := by omega
  have hN03 : T3 ≤ N0 := by omega
  have hN04 : T4 ≤ N0 := by omega
  have hN05 : T5 ≤ N0 := by omega
  have ht : t ≤ 10 := by linarith
  let Q := (N : ℝ) ^ (1 / 2 - δ)
  let W := convolutionWuWindows N Δ V
  let q := Q / (∏ j, V j)
  let Y := reboxingAlpha q Δ t r
  let Z := fun d : ℕ => (Q / d) ^ (1 / s)
  let g := fun d p : ℕ => wuEffectiveCoefficient false (k + 1) δ N0
    (omega2ParameterTransform t (log (Q / d) / log p - 1))
  have hNreal : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hL : 0 < log (N : ℝ) := log_pos hNreal
  have hNpos : (0 : ℝ) < N := by linarith
  have hQpos : 0 < Q := rpow_pos_of_pos hNpos _
  have hVpos : ∀ j, 0 < V j :=
    fun j => (rpow_pos_of_pos hNpos _).trans_le (hb.2.2.2.2.1 j)
  obtain ⟨hΔ, hq, hmesh⟩ := hT2 N (hN02.trans hN) i Δ V hb
  have hΔpos : 0 < Δ := by linarith
  have hqpos : 0 < q := by dsimp [q, Q]; linarith
  have hsupport := fun d hd => reboxing_support_level_bounds hQpos.le hΔpos hVpos
    (N := N) (d := d) hd
  have hheight := hT4 N (hN04.trans hN)
  have hend : ∀ d ∈ boxConvolutionSupport W, (N : ℝ) ^ α ≤ Y ∧ Y ≤ Z d ∧
      log (Z d / Y) ≤ K / log (N : ℝ) ^ (4 : ℕ) := by
    intro d hd
    exact reboxingR1_endpoint_bounds hN4 hδ hδhi hb hs hst ht hr hd
  have hYlo : q ^ (1 / t) ≤ Y := by
    simpa only [reboxingAlpha_zero] using
      (reboxingAlpha_strictMono (t := t) hqpos hΔ).monotone
        (show (0 : ℝ) ≤ r by positivity)
  have hprime : ∀ d ∈ boxConvolutionSupport W,
      (∑ p ∈ primeWindow N Y (Z d),
        |g d p / (((p : ℝ) - 2) * (1 - log (p : ℝ) / log (Q / d)))|) ≤
          44 * B / log (N : ℝ) ^ (5 : ℕ) := by
    intro d hd
    have hD : 1 < Q / d := hq.trans_le (hsupport d hd).1
    have hmass := hT1 N (hN01.trans hN) Y (Z d) (hend d hd).1
      (hend d hd).2.1 (hend d hd).2.2
    have hZupper : Z d ≤ (Q / d) ^ (1 / 2 : ℝ) :=
      rpow_le_rpow_of_exponent_le hD.le
        (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hs)
    calc
      _ ≤ 4 * 11 * ∑ p ∈ primeWindow N Y (Z d), (1 : ℝ) / p := by
        apply reboxing_prime_absolute_term_sum_le (g d) hD
          (hheight.trans (hend d hd).1) hZupper (by norm_num)
        intro p hp
        obtain ⟨_, _, hpY, hpZ⟩ := mem_primeWindow.mp hp
        have hu := reboxingLowerNormalization_parameter_mem hq hΔ hs hst ht
          (hsupport d hd).1 (hsupport d hd).2 hmesh (hYlo.trans hpY) hpZ
        exact hT3 N0 hN03 _ (omega2ParameterTransform_domain ht3 ht5 hu.1)
      _ ≤ 4 * 11 * (B / log (N : ℝ) ^ (5 : ℕ)) :=
        mul_le_mul_of_nonneg_left hmass (by norm_num)
      _ = _ := by ring
  have hli0 : 0 ≤ logarithmicIntegral N :=
    (by positivity : (0 : ℝ) ≤ N / (2 * log N)).trans (box_trueLi_lower hN4)
  have hw : ∀ d ∈ boxConvolutionSupport W,
      0 ≤ (convolutionCoeff W d : ℝ) * wuSingularSeries (d * N) /
        ((Nat.totient d : ℝ) * log (Q / d)) := by
    intro d hd
    have hd0 := (reboxing_support_product_bounds hΔpos (fun j => (hVpos j).le) hd).1
    have hD : 1 < Q / d := hq.trans_le (hsupport d hd).1
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg _)
      (wuSingularSeries_pos _ (Nat.mul_pos hd0 (by omega))).le)
      (mul_nonneg (Nat.cast_nonneg _) (log_pos hD).le)
  have hθ : 0 ≤ boxTheta N Q W := by
    unfold boxTheta
    exact mul_nonneg (mul_nonneg (by norm_num) hli0) (sum_nonneg hw)
  have hfinite : omega2BoundaryAbsolute k N0 N δ Δ V s t r ≤
      (44 * B / log (N : ℝ) ^ (5 : ℕ)) * boxTheta N Q W := by
    unfold omega2BoundaryAbsolute boxTheta
    rw [mul_left_comm (44 * B / log (N : ℝ) ^ (5 : ℕ))]
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by norm_num) hli0)
    calc
      _ ≤ ∑ d ∈ boxConvolutionSupport W,
          ((convolutionCoeff W d : ℝ) * wuSingularSeries (d * N) /
            ((Nat.totient d : ℝ) * log (Q / d))) * (44 * B / log (N : ℝ) ^ (5 : ℕ)) := by
        apply sum_le_sum
        intro d hd
        exact mul_le_mul_of_nonneg_left (hprime d hd) (hw d hd)
      _ = _ := by rw [← sum_mul, mul_comm]
  have hpay : 44 * B / log (N : ℝ) ^ (5 : ℕ) ≤ ε := by
    apply (div_le_iff₀ (by positivity)).2
    have hh := (div_le_iff₀ hε).1 (hT5 N (hN05.trans hN))
    dsimp only [Function.comp_apply] at hh
    nlinarith
  refine ⟨?_, hfinite.trans (mul_le_mul_of_nonneg_right hpay hθ)⟩
  unfold omega2BoundaryAbsolute
  apply mul_nonneg (mul_nonneg (by norm_num) hli0)
  exact sum_nonneg fun d hd => mul_nonneg (hw d hd) (sum_nonneg fun _ _ => abs_nonneg _)

end Wu2008DoubleSieve
