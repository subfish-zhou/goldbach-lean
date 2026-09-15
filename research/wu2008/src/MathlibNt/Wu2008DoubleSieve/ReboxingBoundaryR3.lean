import MathlibNt.Wu2008DoubleSieve.ReboxingBoundaryR1
import MathlibNt.Wu2008DoubleSieve.ReboxingRepeatedPrimes
import MathlibNt.Wu2008DoubleSieve.PrimeCoefficientIntegralBounds

/-!
# Actual coefficient-weighted lower-boundary payment R3

Wu04 (3.18), source lines 1096--1100 and 1125--1127.
The printed totient denominator and the actual effective coefficients
are retained. The proof also handles the signed lower coefficient.
-/

namespace Wu2008DoubleSieve

open Finset Filter Real
open scoped Classical Topology
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418

/-- On the added lower interval the coefficient parameter can exceed
`t-1`, so its upper bound uses the uniform source mesh condition. -/
theorem reboxingR3_parameter_mem {q D Δ t p : ℝ} {i : ℕ}
    (hq : 1 < q) (hΔ : 1 < Δ) (ht : 2 ≤ t) (ht10 : t ≤ 10)
    (hDlo : q ≤ D) (hDhi : D ≤ q * Δ ^ i)
    (hmesh : 10 * (i : ℝ) * log Δ ≤ log q)
    (hp : q ^ (1 / t) ≤ p) (hp' : p < D ^ (1 / t)) :
    1 ≤ log D / log p - 1 ∧ log D / log p - 1 ≤ 10 := by
  have hq0 : 0 < q := by linarith
  have hD0 : 0 < D := hq0.trans_le hDlo
  have hΔ0 : 0 < Δ := by linarith
  have ht0 : 0 < t := by linarith
  have hp1 : 1 < p := (one_lt_rpow hq (by positivity : 0 < 1 / t)).trans_le hp
  have hLp : 0 < log p := log_pos hp1
  have hlow : log q / t ≤ log p := by
    have hh := log_le_log (rpow_pos_of_pos hq0 _) hp
    rw [log_rpow hq0] at hh
    convert hh using 1
    ring
  have hhigh : log p ≤ log D / t := by
    have hh := log_le_log (by linarith : 0 < p) hp'.le
    rw [log_rpow hD0] at hh
    convert hh using 1
    ring
  have hLD : log D ≤ log q + (i : ℝ) * log Δ := by
    have hh := log_le_log hD0 hDhi
    simpa [log_mul hq0.ne' (pow_pos hΔ0 i).ne', log_pow] using hh
  constructor
  · have hh := (le_div_iff₀ ht0).1 hhigh
    have hratio : 2 ≤ log D / log p := (le_div_iff₀ hLp).2 (by nlinarith)
    linarith
  · have hLq : 0 < log q := log_pos hq
    have hten : log q / 10 ≤ log p :=
      (div_le_div_of_nonneg_left hLq.le ht0 ht10).trans hlow
    have hratio : log D / log p ≤ 11 := (div_le_iff₀ hLp).2 (by nlinarith)
    linarith

theorem reboxing_totient_weight_le_four_div {p : ℕ} {D : ℝ}
    (hp : p.Prime) (hD : 1 < D) (hp4 : (4 : ℝ) ≤ p)
    (hupper : (p : ℝ) ≤ D ^ (1 / 2 : ℝ)) :
    0 ≤ 1 / ((Nat.totient p : ℝ) * (1 - log (p : ℝ) / log D)) ∧
      1 / ((Nat.totient p : ℝ) * (1 - log (p : ℝ) / log D)) ≤ 4 / p := by
  have hgap := reboxing_log_ratio_half hD (by linarith : (0 : ℝ) < p) hupper
  have ht : (Nat.totient p : ℝ) = (p : ℝ) - 1 := by
    rw [Nat.totient_prime hp, Nat.cast_sub hp.one_lt.le, Nat.cast_one]
  rw [ht]
  have hp1 : 0 < (p : ℝ) - 1 := by linarith
  have hgap0 : 0 < 1 - log (p : ℝ) / log D := by linarith
  refine ⟨by positivity, ?_⟩
  have hden : 0 < ((p : ℝ) - 2) * (1 - log (p : ℝ) / log D) :=
    mul_pos (by linarith) (by linarith)
  calc
    _ ≤ 1 / (((p : ℝ) - 2) * (1 - log (p : ℝ) / log D)) :=
      one_div_le_one_div_of_le hden (by nlinarith)
    _ ≤ _ := (reboxing_prime_weight_le_four_div hD hp4 hupper).2

/-- The source R3 for upper=true; upper=false is the analogous signed
lower coefficient boundary, estimated in absolute value. -/
noncomputable def reboxingR3 {i : ℕ} (upper : Bool) (k N0 N : ℕ) (δ Δ : ℝ)
    (V : Fin i → ℝ) (t : ℝ) : ℝ :=
  4 * logarithmicIntegral N *
    ∑ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
      ((convolutionCoeff (convolutionWuWindows N Δ V) d : ℝ) * wuSingularSeries (d * N) /
        ((Nat.totient d : ℝ) * log ((N : ℝ) ^ (1 / 2 - δ) / d))) *
      ∑ p ∈ primeWindow N (((N : ℝ) ^ (1 / 2 - δ) / (∏ j, V j)) ^ (1 / t))
          (((N : ℝ) ^ (1 / 2 - δ) / d) ^ (1 / t)),
        wuEffectiveCoefficient upper (k + 1) δ N0
          (log ((N : ℝ) ^ (1 / 2 - δ) / d) / log p - 1) /
          ((Nat.totient p : ℝ) * (1 - log (p : ℝ) / log ((N : ℝ) ^ (1 / 2 - δ) / d)))

/-- Absolute R3 payment for the actual finite-threshold coefficients.
One base threshold precedes N0, then N≥N0, and the full source family. -/
theorem reboxingR3_relative (upper : Bool) (k : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N0 : ℕ, T ≤ N0 → ∀ N : ℕ, N0 ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ t : ℝ, 2 ≤ t → t ≤ 10 →
      |reboxingR3 upper k N0 N δ Δ V t| ≤
        ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  let α := δ ^ (k + 2)
  let K := 2 * ((k : ℝ) + 1)
  let B := 2 * K / α + 2
  have hα : 0 < α := pow_pos hδ _
  have hK : 0 < K := by dsimp [K]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  obtain ⟨T1, hT1⟩ := reboxing_short_prime_mass hα hK
  obtain ⟨T2, _, hT2⟩ := reboxing_parameter_mesh_eventually k hδ hδhi
  obtain ⟨T3, hT3⟩ := eventually_atTop.mp
    (wuEffectiveCoefficient_uniform_abs_le_eleven upper (k + 1) (by omega)
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
  intro N0 hN0 N hN i Δ V hb t ht ht10
  have hN4 : 4 ≤ N := (le_max_left _ _).trans (hN0.trans hN)
  have hN01 : T1 ≤ N0 := (le_max_left _ _).trans ((le_max_right _ _).trans hN0)
  have hN02 : T2 ≤ N0 :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hN0))
  have hN03 : T3 ≤ N0 := by omega
  have hN04 : T4 ≤ N0 := by omega
  have hN05 : T5 ≤ N0 := by omega
  let Q := (N : ℝ) ^ (1 / 2 - δ)
  let W := convolutionWuWindows N Δ V
  let q := Q / (∏ j, V j)
  let Y := q ^ (1 / t)
  let Z := fun d : ℕ => (Q / d) ^ (1 / t)
  let g := fun d p : ℕ => wuEffectiveCoefficient upper (k + 1) δ N0
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
  have hzero : reboxingAlpha q Δ t (0 : ℕ) ≤ q ^ (1 / t) ∧
      q ^ (1 / t) < reboxingAlpha q Δ t ((0 : ℕ) + 1) := by
    constructor
    · simp [reboxingAlpha]
    · simpa [reboxingAlpha] using
        mul_lt_mul_of_pos_left hΔ (rpow_pos_of_pos hqpos (1 / t))
  have hend : ∀ d ∈ boxConvolutionSupport W, (N : ℝ) ^ α ≤ Y ∧ Y ≤ Z d ∧
      log (Z d / Y) ≤ K / log (N : ℝ) ^ (4 : ℕ) := by
    intro d hd
    have hh := reboxingR1_endpoint_bounds hN4 hδ hδhi hb ht le_rfl ht10 hzero hd
    simpa only [reboxingAlpha_zero, Nat.cast_zero] using hh
  have hprime : ∀ d ∈ boxConvolutionSupport W,
      |∑ p ∈ primeWindow N Y (Z d),
        g d p / ((Nat.totient p : ℝ) * (1 - log (p : ℝ) / log (Q / d)))| ≤
          44 * B / log (N : ℝ) ^ (5 : ℕ) := by
    intro d hd
    have hD : 1 < Q / d := hq.trans_le (hsupport d hd).1
    have hmass := hT1 N (hN01.trans hN) Y (Z d) (hend d hd).1
      (hend d hd).2.1 (hend d hd).2.2
    calc
      _ ≤ ∑ p ∈ primeWindow N Y (Z d),
          |g d p / ((Nat.totient p : ℝ) * (1 - log (p : ℝ) / log (Q / d)))| :=
        abs_sum_le_sum_abs _ _
      _ ≤ ∑ p ∈ primeWindow N Y (Z d), 44 * (1 / (p : ℝ)) := by
        apply sum_le_sum
        intro p hp
        obtain ⟨hpp, _, hpY, hpZ⟩ := mem_primeWindow.mp hp
        have hp4 : (4 : ℝ) ≤ p := hheight.trans ((hend d hd).1.trans hpY)
        have hu := reboxingR3_parameter_mem hq hΔ ht ht10 (hsupport d hd).1
          (hsupport d hd).2 hmesh hpY hpZ
        have hg : |g d p| ≤ 11 := hT3 N0 hN03 _ hu
        have hpupper : (p : ℝ) ≤ (Q / d) ^ (1 / 2 : ℝ) := hpZ.le.trans
          (rpow_le_rpow_of_exponent_le hD.le
            (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) ht))
        have hw := reboxing_totient_weight_le_four_div hpp hD hp4 hpupper
        have hi : 0 ≤ ((Nat.totient p : ℝ) * (1 - log (p : ℝ) / log (Q / d)))⁻¹ := by
          simpa only [one_div] using hw.1
        rw [div_eq_mul_inv, abs_mul, abs_of_nonneg hi]
        calc
          _ ≤ 11 * (4 / (p : ℝ)) :=
            mul_le_mul hg (by simpa only [one_div] using hw.2)
              (by simpa only [one_div] using hw.1) (by norm_num)
          _ = _ := by ring
      _ = 44 * ∑ p ∈ primeWindow N Y (Z d), (1 : ℝ) / p := (mul_sum _ _ _).symm
      _ ≤ 44 * (B / log (N : ℝ) ^ (5 : ℕ)) :=
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
  have hfinite : |reboxingR3 upper k N0 N δ Δ V t| ≤
      (44 * B / log (N : ℝ) ^ (5 : ℕ)) * boxTheta N Q W := by
    unfold reboxingR3 boxTheta
    rw [abs_mul, abs_of_nonneg (mul_nonneg (by norm_num) hli0),
      mul_left_comm (44 * B / log (N : ℝ) ^ (5 : ℕ))]
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by norm_num) hli0)
    calc
      _ ≤ ∑ d ∈ boxConvolutionSupport W,
          |((convolutionCoeff W d : ℝ) * wuSingularSeries (d * N) /
            ((Nat.totient d : ℝ) * log (Q / d))) *
            ∑ p ∈ primeWindow N Y (Z d),
              g d p / ((Nat.totient p : ℝ) * (1 - log (p : ℝ) / log (Q / d)))| :=
        abs_sum_le_sum_abs _ _
      _ ≤ ∑ d ∈ boxConvolutionSupport W,
          ((convolutionCoeff W d : ℝ) * wuSingularSeries (d * N) /
            ((Nat.totient d : ℝ) * log (Q / d))) * (44 * B / log (N : ℝ) ^ (5 : ℕ)) := by
        apply sum_le_sum
        intro d hd
        rw [abs_mul, abs_of_nonneg (hw d hd)]
        exact mul_le_mul_of_nonneg_left (hprime d hd) (hw d hd)
      _ = _ := by rw [← sum_mul, mul_comm]
  have hpay : 44 * B / log (N : ℝ) ^ (5 : ℕ) ≤ ε := by
    apply (div_le_iff₀ (by positivity)).2
    have hh := (div_le_iff₀ hε).1 (hT5 N (hN05.trans hN))
    dsimp only [Function.comp_apply] at hh
    nlinarith
  exact hfinite.trans (mul_le_mul_of_nonneg_right hpay hθ)

end Wu2008DoubleSieve
