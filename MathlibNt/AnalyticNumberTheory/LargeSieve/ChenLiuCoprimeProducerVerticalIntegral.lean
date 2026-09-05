import MathlibNt.AnalyticNumberTheory.LargeSieve.ChenLiuCoprimeProducerLong
import MathlibNt.SieveTheory.Distribution.LiuPan.LiuPanPrimitivePerron
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

noncomputable section

open Classical Complex Finset MeasureTheory
open MathlibNt.SieveTheory.LiuWeight
open scoped BigOperators Interval

namespace AnalyticNumberTheory.LargeSieve.ChenLiuCoprimeProducer

private theorem continuous_vertical_line (σ : ℝ) :
    Continuous (liuPanPerronLine σ) := by
  unfold liuPanPerronLine
  fun_prop

private theorem vertical_line_ne_zero {σ : ℝ} (hσ : 1 / 2 ≤ σ) (t : ℝ) :
    liuPanPerronLine σ t ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp [liuPanPerronLine] at this
  linarith

private theorem continuous_vertical_reciprocal {σ : ℝ} (hσ : 1 / 2 ≤ σ) :
    Continuous (fun t => 1 / ‖liuPanPerronLine σ t‖) :=
  continuous_const.div (continuous_vertical_line σ).norm
    (fun t => norm_ne_zero_iff.mpr (vertical_line_ne_zero hσ t))

theorem vertical_reciprocal_le {σ : ℝ} (hσ : 1 / 2 ≤ σ) (t : ℝ) :
    1 / ‖liuPanPerronLine σ t‖ ≤ 3 / (1 + |t|) := by
  have hre : σ ≤ ‖liuPanPerronLine σ t‖ := by
    simpa [liuPanPerronLine] using Complex.re_le_norm (liuPanPerronLine σ t)
  have him : |t| ≤ ‖liuPanPerronLine σ t‖ := by
    simpa [liuPanPerronLine] using Complex.abs_im_le_norm (liuPanPerronLine σ t)
  apply (div_le_div_iff₀ (norm_pos_iff.mpr (vertical_line_ne_zero hσ t))
    (by positivity : 0 < 1 + |t|)).mpr
  nlinarith

theorem integral_vertical_log_weight {T : ℝ} (hT : 0 ≤ T) :
    (∫ t in -T..T, 1 / (1 + |t|)) = 2 * Real.log (1 + T) := by
  let f : ℝ → ℝ := fun t => 1 / (1 + |t|)
  have hc : Continuous f :=
    continuous_const.div (continuous_const.add continuous_abs) (by intro t; positivity)
  have hi (a b : ℝ) : IntervalIntegrable f volume a b := hc.intervalIntegrable a b
  have hpos : (∫ t in 0..T, f t) = Real.log (1 + T) := by
    calc
      _ = ∫ t in 0..T, 1 / (t + 1) := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [Set.uIcc_of_le hT] at ht
        simp [f, abs_of_nonneg ht.1, add_comm]
      _ = ∫ t in (0 + 1 : ℝ)..(T + 1), 1 / t :=
        intervalIntegral.integral_comp_add_right (fun t : ℝ => 1 / t) 1
      _ = _ := by
        rw [integral_one_div_of_pos (by norm_num) (by linarith)]
        simp [add_comm]
  have hneg : (∫ t in -T..0, f t) = ∫ t in 0..T, f t := by
    simpa [f] using
      (intervalIntegral.integral_comp_neg (f := f) (a := 0) (b := T)).symm
  change (∫ t in -T..T, f t) = _
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi (-T) 0) (hi 0 T),
    hneg, hpos]
  ring

/-- The reciprocal Perron denominator has only logarithmic mass on a vertical segment. -/
theorem vertical_reciprocal_integral_le {σ T : ℝ}
    (hσ : 1 / 2 ≤ σ) (hT : 0 ≤ T) :
    (∫ t in -T..T, 1 / ‖liuPanPerronLine σ t‖) ≤ 6 * Real.log (1 + T) := by
  have hc : Continuous (fun t : ℝ => 3 * (1 / (1 + |t|))) :=
    continuous_const.mul
      (continuous_const.div (continuous_const.add continuous_abs) (by intro t; positivity))
  calc
    _ ≤ ∫ t in -T..T, 3 * (1 / (1 + |t|)) := by
      apply intervalIntegral.integral_mono_on (by linarith)
        ((continuous_vertical_reciprocal hσ).intervalIntegrable _ _)
        (hc.intervalIntegrable _ _)
      intro t _
      simpa only [mul_one_div] using vertical_reciprocal_le hσ t
    _ = _ := by
      rw [intervalIntegral.integral_const_mul, integral_vertical_log_weight hT]
      ring

/-- A uniform primitive-character mean pays just one logarithm under the Perron integral.
The complex functions remain intact until taking the norm of their complete integrals. -/
theorem primitive_integral_mean_le (S : Finset ℕ)
    (G : (q : ℕ) → PrimitiveCharacter q → ℝ → ℂ)
    {σ Y T M : ℝ} (hσ : 1 / 2 ≤ σ) (hY : 0 < Y) (hT : 0 ≤ T)
    (hM : 0 ≤ M) (hG : ∀ q ∈ S, ∀ χ, Continuous (G q χ))
    (hmean : ∀ t ∈ Set.Icc (-T) T,
      (∑ q ∈ S, (q.totient : ℝ)⁻¹ * ∑ χ : PrimitiveCharacter q, ‖G q χ t‖) ≤ M) :
    (∑ q ∈ S, (q.totient : ℝ)⁻¹ * ∑ χ : PrimitiveCharacter q,
      ‖((2 * Real.pi : ℝ) : ℂ)⁻¹ *
        ∫ t in -T..T, G q χ t * (Y : ℂ) ^ (liuPanPerronLine σ t) /
          liuPanPerronLine σ t‖) ≤
      6 * Y ^ σ * M * Real.log (1 + T) := by
  let K : ℝ → ℝ := fun t => Y ^ σ / ‖liuPanPerronLine σ t‖
  let f : (q : ℕ) → PrimitiveCharacter q → ℝ → ℝ :=
    fun q χ t => K t * ‖G q χ t‖
  have hK : Continuous K :=
    continuous_const.div (continuous_vertical_line σ).norm
      (fun t => norm_ne_zero_iff.mpr (vertical_line_ne_zero hσ t))
  have hf (q : ℕ) (hq : q ∈ S) (χ : PrimitiveCharacter q) : Continuous (f q χ) :=
    hK.mul (hG q hq χ).norm
  have hfi (q : ℕ) (hq : q ∈ S) (χ : PrimitiveCharacter q) :
      IntervalIntegrable (f q χ) volume (-T) T := (hf q hq χ).intervalIntegrable _ _
  have hnorm : ‖((2 * Real.pi : ℝ) : ℂ)⁻¹‖ ≤ 1 := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    apply (inv_le_one₀ (by positivity)).mpr
    have := Real.pi_gt_three
    linarith
  have hpiece (q : ℕ) (χ : PrimitiveCharacter q) :
      ‖((2 * Real.pi : ℝ) : ℂ)⁻¹ *
        ∫ t in -T..T, G q χ t * (Y : ℂ) ^ (liuPanPerronLine σ t) /
          liuPanPerronLine σ t‖ ≤ ∫ t in -T..T, f q χ t := by
    rw [norm_mul]
    calc
      _ ≤ ‖∫ t in -T..T, G q χ t * (Y : ℂ) ^ (liuPanPerronLine σ t) /
          liuPanPerronLine σ t‖ :=
        mul_le_of_le_one_left (norm_nonneg _) hnorm
      _ ≤ ∫ t in -T..T, ‖G q χ t * (Y : ℂ) ^ (liuPanPerronLine σ t) /
          liuPanPerronLine σ t‖ :=
        intervalIntegral.norm_integral_le_integral_norm (by linarith)
      _ = _ := by
        apply intervalIntegral.integral_congr
        intro t _
        simp only [norm_div, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hY]
        simp only [liuPanPerronLine, Complex.add_re, Complex.ofReal_re,
          Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
          mul_zero, zero_mul, sub_self, add_zero]
        dsimp [f, K, liuPanPerronLine]
        ring
  have hsumc (q : ℕ) (hq : q ∈ S) :
      Continuous (fun t => ∑ χ : PrimitiveCharacter q, f q χ t) := by
    fun_prop
  have htotalc : Continuous
      (fun t => ∑ q ∈ S, (q.totient : ℝ)⁻¹ * ∑ χ : PrimitiveCharacter q, f q χ t) := by
    apply continuous_finsetSum
    intro q hq
    exact continuous_const.mul (hsumc q hq)
  calc
    _ ≤ ∑ q ∈ S, (q.totient : ℝ)⁻¹ * ∑ χ : PrimitiveCharacter q,
        ∫ t in -T..T, f q χ t := by
      apply sum_le_sum
      intro q hq
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact sum_le_sum fun χ _ => hpiece q χ
    _ = ∫ t in -T..T,
        ∑ q ∈ S, (q.totient : ℝ)⁻¹ * ∑ χ : PrimitiveCharacter q, f q χ t := by
      rw [intervalIntegral.integral_finsetSum
        (f := fun q t => (q.totient : ℝ)⁻¹ * ∑ χ : PrimitiveCharacter q, f q χ t)
        (fun q hq => (continuous_const.mul (hsumc q hq)).intervalIntegrable _ _)]
      apply sum_congr rfl
      intro q hq
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_finsetSum (fun χ _ => hfi q hq χ)]
    _ ≤ ∫ t in -T..T, K t * M := by
      apply intervalIntegral.integral_mono_on (by linarith)
        (htotalc.intervalIntegrable _ _) ((hK.mul continuous_const).intervalIntegrable _ _)
      intro t ht
      calc
        _ = K t * (∑ q ∈ S, (q.totient : ℝ)⁻¹ *
            ∑ χ : PrimitiveCharacter q, ‖G q χ t‖) := by
          simp only [f, mul_sum]
          apply sum_congr rfl
          intro q _
          apply sum_congr rfl
          intro χ _
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (hmean t ht) (by dsimp [K]; positivity)
    _ = (Y ^ σ * M) * (∫ t in -T..T, 1 / ‖liuPanPerronLine σ t‖) := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro t _
      dsimp [K]
      ring
    _ ≤ (Y ^ σ * M) * (6 * Real.log (1 + T)) :=
      mul_le_mul_of_nonneg_left (vertical_reciprocal_integral_le hσ hT) (by positivity)
    _ = _ := by ring

end AnalyticNumberTheory.LargeSieve.ChenLiuCoprimeProducer
