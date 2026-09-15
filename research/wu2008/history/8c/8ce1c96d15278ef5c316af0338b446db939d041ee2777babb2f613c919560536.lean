import MathlibNt.Wu2008DoubleSieve.ReboxingBoundaryR3Absolute
import MathlibNt.Wu2008DoubleSieve.ReboxingBoundaryR2ReverseRaw

/-!
# Signed lower normalization: the terminal prime boundary

Wu04 source lines 1082--1106 and 1113--1149, for the reverse comparison.
The lower coefficient may be negative. Extending a geometric prime
window therefore pays both endpoints in absolute term sum. The left
endpoint uses the accepted R3Absolute; this file pays the terminal end
using the same true-li short-window theorem and actual R1 geometry.
-/

namespace Wu2008DoubleSieve

open Finset Filter Real
open scoped Classical Topology
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418

/-- The full union of the geometric and actual source intervals has
its shifted parameter in `[1,10]`, including the terminal tail. -/
theorem reboxingLowerNormalization_parameter_mem {q D Δ s t p : ℝ} {i : ℕ}
    (hq : 1 < q) (hΔ : 1 < Δ) (hs : 2 ≤ s) (hst : s ≤ t) (ht10 : t ≤ 10)
    (hDlo : q ≤ D) (hDhi : D ≤ q * Δ ^ i)
    (hmesh : 10 * (i : ℝ) * log Δ ≤ log q)
    (hp : q ^ (1 / t) ≤ p) (hp' : p < D ^ (1 / s)) :
    1 ≤ log D / log p - 1 ∧ log D / log p - 1 ≤ 10 := by
  have hq0 : 0 < q := by linarith
  have hD0 : 0 < D := hq0.trans_le hDlo
  have hΔ0 : 0 < Δ := by linarith
  have hs0 : 0 < s := by linarith
  have ht0 : 0 < t := by linarith
  have hp1 : 1 < p := (one_lt_rpow hq (by positivity : 0 < 1 / t)).trans_le hp
  have hLp : 0 < log p := log_pos hp1
  have hlow : log q / t ≤ log p := by
    have hh := log_le_log (rpow_pos_of_pos hq0 _) hp
    rw [log_rpow hq0] at hh
    convert hh using 1
    ring
  have hhigh : log p ≤ log D / s := by
    have hh := log_le_log (by linarith : 0 < p) hp'.le
    rw [log_rpow hD0] at hh
    convert hh using 1
    ring
  have hLD : log D ≤ log q + (i : ℝ) * log Δ := by
    have hh := log_le_log hD0 hDhi
    simpa [log_mul hq0.ne' (pow_pos hΔ0 i).ne', log_pow] using hh
  constructor
  · have hh := (le_div_iff₀ hs0).1 hhigh
    have hratio : 2 ≤ log D / log p := (le_div_iff₀ hLp).2 (by nlinarith)
    linarith
  · have hLq : 0 < log q := log_pos hq
    have hten : log q / 10 ≤ log p :=
      (div_le_div_of_nonneg_left hLq.le ht0 ht10).trans hlow
    have hratio : log D / log p ≤ 11 := (div_le_iff₀ hLp).2 (by nlinarith)
    linarith

noncomputable def reboxingLowerTerminalAbsolute {i : ℕ} (k N0 N : ℕ)
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
          (log ((N : ℝ) ^ (1 / 2 - δ) / d) / log p - 1) /
          (((p : ℝ) - 2) *
            (1 - log (p : ℝ) / log ((N : ℝ) ^ (1 / 2 - δ) / d)))|

/-- Uniform absolute payment of the whole terminal tail. The threshold
precedes `N0`, the source family and the terminal index. -/
theorem reboxingLowerTerminalAbsolute_relative (k : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N0 : ℕ, T ≤ N0 → ∀ N : ℕ, N0 ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → t ≤ 10 → ∀ r : ℕ,
      (reboxingAlpha ((N : ℝ) ^ (1 / 2 - δ) / (∏ j, V j)) Δ t r ≤
          ((N : ℝ) ^ (1 / 2 - δ) / (∏ j, V j)) ^ (1 / s) ∧
        ((N : ℝ) ^ (1 / 2 - δ) / (∏ j, V j)) ^ (1 / s) <
          reboxingAlpha ((N : ℝ) ^ (1 / 2 - δ) / (∏ j, V j)) Δ t (r + 1)) →
      0 ≤ reboxingLowerTerminalAbsolute k N0 N δ Δ V s t r ∧
        reboxingLowerTerminalAbsolute k N0 N δ Δ V s t r ≤
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
  intro N0 hN0 N hN i Δ V hb s t hs hst ht r hr
  have hN4 : 4 ≤ N := (le_max_left _ _).trans (hN0.trans hN)
  have hN01 : T1 ≤ N0 := by omega
  have hN02 : T2 ≤ N0 := by omega
  have hN03 : T3 ≤ N0 := by omega
  have hN04 : T4 ≤ N0 := by omega
  have hN05 : T5 ≤ N0 := by omega
  let Q := (N : ℝ) ^ (1 / 2 - δ)
  let W := convolutionWuWindows N Δ V
  let q := Q / (∏ j, V j)
  let Y := reboxingAlpha q Δ t r
  let Z := fun d : ℕ => (Q / d) ^ (1 / s)
  let g := fun d p : ℕ => wuEffectiveCoefficient false (k + 1) δ N0
    (log (Q / d) / log p - 1)
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
        exact hT3 N0 hN03 _ hu
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
  have hfinite : reboxingLowerTerminalAbsolute k N0 N δ Δ V s t r ≤
      (44 * B / log (N : ℝ) ^ (5 : ℕ)) * boxTheta N Q W := by
    unfold reboxingLowerTerminalAbsolute boxTheta
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
  unfold reboxingLowerTerminalAbsolute
  apply mul_nonneg (mul_nonneg (by norm_num) hli0)
  exact sum_nonneg fun d hd => mul_nonneg (hw d hd) (sum_nonneg fun _ _ => abs_nonneg _)

end Wu2008DoubleSieve
