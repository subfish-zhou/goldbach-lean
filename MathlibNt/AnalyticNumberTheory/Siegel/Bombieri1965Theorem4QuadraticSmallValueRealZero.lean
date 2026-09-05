import MathlibNt.AnalyticNumberTheory.Siegel.Bombieri1965Theorem4QuadraticConvolutionWeightedSum
import MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLQuadraticConjugation

/-!
# Small actual quadratic L-values force near-one real zeros

The weighted positive convolution supplies the sign change. The zeta sign
near its pole follows from the actual regularized zeta function. This modern
argument does not assume a Siegel lower bound or the existence of an
exceptional zero.
-/

open Complex Finset Filter
open scoped Topology

namespace AnalyticNumberTheory.LargeSieve.Bombieri1965Theorem4

open DirichletCharacter

variable {q : ℕ} [NeZero q]

omit [NeZero q] in
/-- The coefficient at one gives a lower bound for every positive weighted prefix. -/
theorem one_le_quadraticConvolutionWeightedSum
    (χ : DirichletCharacter ℂ q) (hquad : χ ^ 2 = 1)
    (β : ℝ) {x : ℝ} (hx : 1 ≤ x) :
    1 ≤ quadraticConvolutionWeightedSum χ β x := by
  have hcoeff : quadraticSiegelConvolution χ 1 = 1 := by
    unfold quadraticSiegelConvolution
    rw [χ.isMultiplicative_zetaMul.map_one]
    rfl
  calc
    (1 : ℝ) = quadraticSiegelConvolution χ 1 * (1 : ℝ) ^ (-β) := by
      rw [hcoeff, Real.one_rpow, mul_one]
    _ ≤ quadraticConvolutionWeightedSum χ β x := by
      unfold quadraticConvolutionWeightedSum
      simpa only [Nat.cast_one] using Finset.single_le_sum
        (f := fun n : ℕ => quadraticSiegelConvolution χ n * (n : ℝ) ^ (-β))
        (fun n _ => mul_nonneg (quadraticSiegelConvolution_nonneg χ hquad n)
          (Real.rpow_nonneg (Nat.cast_nonneg n) _))
        (mem_Icc.mpr ⟨le_rfl, (Nat.one_le_floor_iff _).mpr hx⟩)

private theorem conductor_cutoff_one_le (q : ℕ) [NeZero q] :
    1 ≤ (648 * (q : ℝ)) ^ (4 : ℕ) := by
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  exact one_le_pow₀ (by linarith : (1 : ℝ) ≤ 648 * q)

/-- The explicit cutoff pays the weighted error by one half uniformly for
all exponents at least three quarters. -/
theorem quadraticConvolution_weighted_error_at_cutoff_le
    {β : ℝ} (hβ : 3 / 4 ≤ β) :
    81 * q * (1 + β / (β - 1 / 2)) *
        ((648 * (q : ℝ)) ^ (4 : ℕ)) ^ (1 / 2 - β) ≤ 1 / 2 := by
  have hq : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have ha : (0 : ℝ) < 648 * q := by positivity
  have hratio : β / (β - 1 / 2) ≤ 3 :=
    (div_le_iff₀ (by linarith)).mpr (by linarith)
  have hpow :
      ((648 * (q : ℝ)) ^ (4 : ℕ)) ^ (1 / 2 - β) ≤ (648 * (q : ℝ))⁻¹ := by
    calc
      _ ≤ ((648 * (q : ℝ)) ^ (4 : ℕ)) ^ (-1 / 4 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (conductor_cutoff_one_le q) (by linarith)
      _ = _ := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul ha.le]
        norm_num [Real.rpow_neg_one]
  calc
    _ ≤ (81 * (q : ℝ) * 4) * (648 * (q : ℝ))⁻¹ := by gcongr; linarith
    _ = 1 / 2 := by field_simp; ring

/-- A small L-value makes the actual continued zeta-L product positive at
the selected point to the left of one. -/
theorem IsPrimitive.re_zeta_mul_LFunction_pos_of_small_value
    (χ : DirichletCharacter ℂ q) (hprim : χ.IsPrimitive) (hχ : χ ≠ 1)
    (hquad : χ ^ 2 = 1) {ε : ℝ} (hε : 0 < ε) (hε4 : ε ≤ 1 / 4)
    (hsmall : (χ.LFunction 1).re ≤
      ε / (4 * (648 * (q : ℝ)) ^ (4 * ε))) :
    0 < (riemannZeta ((1 - ε : ℝ) : ℂ) * χ.LFunction ((1 - ε : ℝ) : ℂ)).re := by
  let x : ℝ := (648 * (q : ℝ)) ^ (4 : ℕ)
  have hx : 1 ≤ x := conductor_cutoff_one_le q
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hpower : x ^ ε = (648 * (q : ℝ)) ^ (4 * ε) := by
    rw [Real.rpow_mul (by positivity)]
    norm_num [x]
  have hmain :
      (χ.LFunction 1).re * x ^ ε / ε ≤ 1 / 4 := by
    rw [div_le_iff₀ hε]
    have h := mul_le_mul_of_nonneg_right hsmall (Real.rpow_nonneg hx0.le ε)
    rw [hpower] at h
    have hp : 0 < (648 * (q : ℝ)) ^ (4 * ε) := by
      rw [← hpower]
      exact Real.rpow_pos_of_pos hx0 _
    have heq : (ε / (4 * (648 * (q : ℝ)) ^ (4 * ε))) *
        (648 * (q : ℝ)) ^ (4 * ε) = ε / 4 := by
      rw [div_mul_eq_div_div, div_mul_cancel₀ _ hp.ne']
    rw [heq] at h
    simpa [hpower, div_eq_mul_inv, mul_comm] using h
  have hweight := one_le_quadraticConvolutionWeightedSum χ hquad (1 - ε) hx
  have herr := IsPrimitive.abs_quadraticConvolutionWeightedSum_sub_main_sub_product_le
    χ hprim hχ hquad (β := 1 - ε) (by linarith) (by linarith) hx
  have hpay := quadraticConvolution_weighted_error_at_cutoff_le (q := q)
    (β := 1 - ε) (by linarith)
  have hupper := (le_abs_self _).trans (herr.trans hpay)
  rw [show 1 - (1 - ε) = ε by ring] at hupper
  linarith

/-- The genuine regularized zeta value gives a fixed left neighborhood
where the Riemann zeta function has negative real part. -/
theorem exists_zeta_negative_left_neighborhood :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 4 ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
        (riemannZeta ((1 - ε : ℝ) : ℂ)).re < 0 := by
  have hc : Continuous (fun t : ℝ => (riemannZeta₁ (t : ℂ)).re) :=
    Complex.continuous_re.comp (differentiable_riemannZeta₁.continuous.comp
      Complex.continuous_ofReal)
  have he : ∀ᶠ t : ℝ in 𝓝 1, 0 < (riemannZeta₁ (t : ℂ)).re :=
    continuousAt_const.eventually_lt hc.continuousAt (by simp [riemannZeta₁_one])
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨min (r / 2) (1 / 4), lt_min (by positivity) (by norm_num),
    min_le_right _ _, ?_⟩
  intro ε hε hε₀
  have hεr : ε < r := by
    have := hε₀.trans (min_le_left _ _)
    linarith
  have hpos : 0 < (riemannZeta₁ ((1 - ε : ℝ) : ℂ)).re := by
    apply hball
    simpa [Real.dist_eq, abs_of_pos hε] using hεr
  have hs : ((1 - ε : ℝ) : ℂ) ≠ 1 := by
    exact_mod_cast (show 1 - ε ≠ 1 by linarith)
  have hform :
      (riemannZeta ((1 - ε : ℝ) : ℂ)).re =
        (1 - ε - 1)⁻¹ * (riemannZeta₁ ((1 - ε : ℝ) : ℂ)).re := by
    rw [riemannZeta_eq_inv_sub_mul hs]
    have hsub : ((1 - ε : ℝ) : ℂ) - 1 = ((1 - ε - 1 : ℝ) : ℂ) := by push_cast; rfl
    rw [hsub, ← ofReal_inv, re_ofReal_mul]
  rw [hform]
  rw [show 1 - ε - 1 = -ε by ring, inv_neg]
  exact mul_neg_of_neg_of_pos (neg_lt_zero.mpr (inv_pos.mpr hε)) hpos

/-- One outer zeta neighborhood works for all conductors and characters.
The small-value threshold is explicit and the produced zero belongs to the
actual L-function, strictly between `1-ε` and one. -/
theorem exists_uniform_small_value_real_zero_neighborhood :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 4 ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
        χ.IsPrimitive → χ ≠ 1 → χ ^ 2 = 1 →
        (χ.LFunction 1).re ≤ ε / (4 * (648 * (q : ℝ)) ^ (4 * ε)) →
        ∃ β : ℝ, β ∈ Set.Ioo (1 - ε) 1 ∧ χ.LFunction (β : ℂ) = 0 := by
  obtain ⟨ε₀, hε₀, hε₀4, hzeta⟩ := exists_zeta_negative_left_neighborhood
  refine ⟨ε₀, hε₀, hε₀4, ?_⟩
  intro ε hε hεbound q _ χ hprim hχ hquad hsmall
  have hε4 := hεbound.trans hε₀4
  have hLpos := LFunction_apply_one_re_pos_of_sq_eq_one hquad hχ
  have hprod := IsPrimitive.re_zeta_mul_LFunction_pos_of_small_value
    χ hprim hχ hquad hε hε4 hsmall
  have hreal := LFunction_ofReal_im_eq_zero_of_sq_eq_one χ hχ hquad (1 - ε)
    (by linarith)
  rw [mul_re, hreal, mul_zero, sub_zero] at hprod
  have hLneg : (χ.LFunction ((1 - ε : ℝ) : ℂ)).re < 0 :=
    neg_of_mul_pos_right hprod (hzeta ε hε hεbound).le
  have hc : Continuous (fun t : ℝ => (χ.LFunction (t : ℂ)).re) :=
    Complex.continuous_re.comp ((χ.differentiable_LFunction hχ).continuous.comp
      Complex.continuous_ofReal)
  obtain ⟨β, hβ, hzero⟩ := intermediate_value_Icc (show 1 - ε ≤ 1 by linarith)
    hc.continuousOn ⟨hLneg.le, by simpa using hLpos.le⟩
  have hβleft : 1 - ε < β := by
    rcases hβ.1.eq_or_lt with h | h
    · rw [← h] at hzero
      linarith
    · exact h
  have hβright : β < 1 := by
    rcases hβ.2.eq_or_lt with h | h
    · rw [h] at hzero
      simp only [ofReal_one] at hzero
      linarith
    · exact h
  refine ⟨β, ⟨hβleft, hβright⟩, ?_⟩
  apply Complex.ext
  · exact hzero
  · exact LFunction_ofReal_im_eq_zero_of_sq_eq_one χ hχ hquad β (by linarith)

end AnalyticNumberTheory.LargeSieve.Bombieri1965Theorem4
