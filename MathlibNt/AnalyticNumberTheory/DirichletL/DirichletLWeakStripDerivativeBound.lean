import MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLConditionalDerivativeAnalyticContinuation
import MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLFiniteDerivativeTruncationBound

/-!
# A genuine weak-strip bound for the continued Dirichlet-L derivative

This module joins the continued ordered derivative series to its finite
truncation at `⌊|t|⌋₊ + 1`.  The Abel tail is retained explicitly, so no
absolute-convergence argument is used in the weak strip.
-/

open Complex Finset Set

namespace DirichletLWeakStripDerivativeBound

open DirichletLAbelWeightVariation
open DirichletLConditionalDerivativeSeries
open DirichletLConditionalDerivativeAnalyticContinuation
open DirichletLFiniteDerivativeTruncationBound

variable {q : ℕ} [NeZero q]

/-- The canonical cutoff lies strictly above the height. -/
lemma abs_lt_natFloor_add_one {t : ℝ} :
    |t| < (⌊|t|⌋₊ + 1 : ℕ) := by
  exact_mod_cast Nat.lt_floor_add_one |t|

/-- The canonical cutoff is at most one above the height. -/
lemma natFloor_add_one_le_abs_add_one {t : ℝ} :
    ((⌊|t|⌋₊ + 1 : ℕ) : ℝ) ≤ |t| + 1 := by
  norm_num only [Nat.cast_add, Nat.cast_one]
  simpa [add_comm] using add_le_add_right (Nat.floor_le (abs_nonneg t)) 1

/-- In the requested weak strip the real part stays above one half. -/
lemma one_half_lt_sigma {A σ t : ℝ} (hA : A ∈ Set.Ioc 0 (1 / 2))
    (ht : 3 < |t|) (hσ : 1 - A / Real.log |t| ≤ σ) :
    1 / 2 < σ := by
  have hlog : 1 < Real.log |t| := logt_gt_one ht.le
  have hdiv : A / Real.log |t| < 1 / 2 := by
    calc
      A / Real.log |t| ≤ (1 / 2) / Real.log |t| :=
        (div_le_div_iff_of_pos_right (by linarith)).2 hA.2
      _ < 1 / 2 := by
        rw [div_lt_iff₀ (by linarith)]
        nlinarith
  linarith

/-- The continued argument has norm at most `|t| + 2` in the requested strip. -/
lemma norm_sigma_add_tI_le_abs_add_two {A σ t : ℝ}
    (hA : A ∈ Set.Ioc 0 (1 / 2)) (ht : 3 < |t|)
    (hσ : 1 - A / Real.log |t| ≤ σ) (hσ2 : σ ≤ 2) :
    ‖(σ + t * I : ℂ)‖ ≤ |t| + 2 := by
  have hσpos : 0 < σ := lt_trans (by norm_num) (one_half_lt_sigma hA ht hσ)
  calc
    ‖(σ + t * I : ℂ)‖ ≤ ‖(σ : ℂ)‖ + ‖(t : ℂ) * I‖ := norm_add_le _ _
    _ = ‖(σ : ℂ)‖ + ‖(t : ℂ)‖ := by rw [norm_mul, norm_I, mul_one]
    _ = |σ| + |t| := by
      rw [Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
    _ = σ + |t| := by rw [abs_of_pos hσpos]
    _ ≤ |t| + 2 := by linarith

/-- The logarithm of the canonical cutoff costs at most twice `log |t|`. -/
lemma log_natFloor_add_one_le_two_mul_log_abs {t : ℝ} (ht : 3 < |t|) :
    Real.log ((⌊|t|⌋₊ + 1 : ℕ) : ℝ) ≤ 2 * Real.log |t| := by
  have htpos : 0 < |t| := by linarith
  have hmpos : (0 : ℝ) < ((⌊|t|⌋₊ + 1 : ℕ) : ℝ) := by positivity
  have hmle : ((⌊|t|⌋₊ + 1 : ℕ) : ℝ) ≤ |t| ^ 2 :=
    (natFloor_add_one_le_abs_add_one (t := t)).trans (by nlinarith)
  calc
    Real.log ((⌊|t|⌋₊ + 1 : ℕ) : ℝ) ≤ Real.log (|t| ^ 2) :=
      Real.log_le_log hmpos hmle
    _ = 2 * Real.log |t| := by rw [Real.log_pow]; norm_num

/-- The potentially dangerous weak-strip power at the canonical cutoff is
uniformly paid by a fixed multiple of `exp A`. -/
lemma natFloor_add_one_rpow_one_sub_sigma_le {A σ t : ℝ}
    (hA : A ∈ Set.Ioc 0 (1 / 2)) (ht : 3 < |t|)
    (hσ : 1 - A / Real.log |t| ≤ σ) :
    (((⌊|t|⌋₊ + 1 : ℕ) : ℝ) ^ (1 - σ)) ≤ 3 * Real.exp A := by
  let m : ℝ := ((⌊|t|⌋₊ + 1 : ℕ) : ℝ)
  have hmone : 1 ≤ m := by simp [m]
  have hmpos : 0 < m := lt_of_lt_of_le zero_lt_one hmone
  have hlog : 1 < Real.log |t| := logt_gt_one ht.le
  have hlogm : Real.log m ≤ 2 * Real.log |t| := by
    simpa only [m] using log_natFloor_add_one_le_two_mul_log_abs ht
  have hexpA3 : Real.exp A ≤ 3 :=
    (Real.exp_le_exp.mpr (hA.2.trans (by norm_num))).trans Real.exp_one_lt_three.le
  have hexpAone : 1 ≤ Real.exp A := by
    simpa only [Real.exp_zero] using Real.exp_le_exp.mpr hA.1.le
  by_cases he : 1 - σ ≤ 0
  · calc
      m ^ (1 - σ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hmone he
      _ ≤ 3 * Real.exp A := by nlinarith
  · have hepos : 0 < 1 - σ := lt_of_not_ge he
    have heupper : 1 - σ ≤ A / Real.log |t| := by linarith
    have hmul : Real.log m * (1 - σ) ≤ 2 * A := by
      calc
        Real.log m * (1 - σ) ≤ (2 * Real.log |t|) * (1 - σ) :=
          mul_le_mul_of_nonneg_right hlogm hepos.le
        _ ≤ (2 * Real.log |t|) * (A / Real.log |t|) :=
          mul_le_mul_of_nonneg_left heupper (by positivity)
        _ = 2 * A := by field_simp
    rw [Real.rpow_def_of_pos hmpos]
    calc
      Real.exp (Real.log m * (1 - σ)) ≤ Real.exp (2 * A) := Real.exp_le_exp.mpr hmul
      _ = Real.exp A * Real.exp A := by rw [show 2 * A = A + A by ring, Real.exp_add]
      _ ≤ Real.exp A * 3 := mul_le_mul_of_nonneg_left hexpA3 (Real.exp_pos A).le
      _ = 3 * Real.exp A := by ring

/-- Exact calibration of the multiplication order in the finite derivative
sum.  The zero term is handled separately; positive terms use the existing
`logCpowWeight_nat_eq` bridge. -/
lemma sum_logCpowWeight_eq_derivative_truncation
    (χ : DirichletCharacter ℂ q) (σ t : ℝ) (m : ℕ) :
    (∑ n ∈ range m, logCpowWeight (σ + t * I) n * χ n) =
      ∑ n ∈ range m,
        (-(Complex.log n) * (n : ℂ) ^ (-(σ + t * I))) * χ n := by
  apply sum_congr rfl
  intro n hn
  rcases n with _ | n
  · simp [logCpowWeight, cpowWeight]
  · rw [logCpowWeight_nat_eq (σ + t * I) (Nat.succ_pos n)]

/-- Assembly theorem for the continued derivative in the weak strip.  This is
the honest tail-budget interface: the first summand is the proved finite
truncation estimate and the second is exactly the paid Abel tail at
`m = ⌊|t|⌋₊ + 1`. -/
theorem norm_deriv_LFunction_le_truncation_add_tail
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {A C σ t : ℝ} (hA : A ∈ Set.Ioc 0 (1 / 2))
    (hσ : 1 - A / Real.log |t| ≤ σ) (ht : 3 < |t|) (hC : 2 ≤ C) :
    let m := ⌊|t|⌋₊ + 1
    ‖deriv χ.LFunction (σ + t * I)‖ ≤
      Real.exp A * C * (Real.log |t|) ^ 2 +
        q * (‖logCpowWeight (σ + t * I) m‖ +
          logVariationBudget (σ + t * I) m) := by
  let m := ⌊|t|⌋₊ + 1
  have hσpos : 0 < σ := lt_trans (by norm_num) (one_half_lt_sigma hA ht hσ)
  have hsre : 0 < (σ + t * I : ℂ).re := by simpa using hσpos
  have hm : 1 ≤ m := by simp [m]
  have htail := norm_orderedLogDerivativeSeries_sub_sum_range_le
    χ hχ (σ + t * I) hsre hm
  have hseries := orderedLogDerivativeSeries_eq_deriv_LFunction_of_re_pos
    χ hχ (σ + t * I) hsre
  have hfinite := norm_derivative_truncation_le χ hA hσ ht hC
  have hsum := sum_logCpowWeight_eq_derivative_truncation χ σ t m
  have hfinite' :
      ‖∑ n ∈ range m, logCpowWeight (σ + t * I) n * χ n‖ ≤
        Real.exp A * C * (Real.log |t|) ^ 2 := by
    rw [hsum]
    exact hfinite
  change ‖deriv χ.LFunction (σ + t * I)‖ ≤ _
  rw [← hseries]
  calc
    ‖orderedLogDerivativeSeries χ hχ (σ + t * I) hsre‖ =
        ‖(∑ n ∈ range m, logCpowWeight (σ + t * I) n * χ n) +
          (orderedLogDerivativeSeries χ hχ (σ + t * I) hsre -
            ∑ n ∈ range m, logCpowWeight (σ + t * I) n * χ n)‖ := by
              congr 1
              abel
    _ ≤ ‖∑ n ∈ range m, logCpowWeight (σ + t * I) n * χ n‖ +
          ‖orderedLogDerivativeSeries χ hχ (σ + t * I) hsre -
            ∑ n ∈ range m, logCpowWeight (σ + t * I) n * χ n‖ := norm_add_le _ _
    _ ≤ Real.exp A * C * (Real.log |t|) ^ 2 +
          q * (‖logCpowWeight (σ + t * I) m‖ +
            logVariationBudget (σ + t * I) m) := by
      exact add_le_add hfinite' htail

/-- At the canonical cutoff the entire explicit Abel tail is absorbed by a
fixed numerical multiple of the weak-strip logarithmic budget. -/
theorem canonical_tail_le_fixed_log_sq
    {A σ t : ℝ} (hA : A ∈ Set.Ioc 0 (1 / 2))
    (hσ : 1 - A / Real.log |t| ≤ σ) (hσ2 : σ ≤ 2) (ht : 3 < |t|) :
    let m := ⌊|t|⌋₊ + 1
    q * (‖logCpowWeight (σ + t * I) m‖ +
      logVariationBudget (σ + t * I) m) ≤
        Real.exp A * (100 * q) * (Real.log |t|) ^ 2 := by
  let m : ℕ := ⌊|t|⌋₊ + 1
  let s : ℂ := σ + t * I
  let L : ℝ := Real.log |t|
  let P : ℝ := (m : ℝ) ^ (1 - σ)
  have hσhalf : 1 / 2 < σ := one_half_lt_sigma hA ht hσ
  have hσpos : 0 < σ := by linarith
  have hmone : (1 : ℝ) ≤ m := by simp [m]
  have hmpos : (0 : ℝ) < m := lt_of_lt_of_le zero_lt_one hmone
  have hL : 1 < L := by simpa only [L] using logt_gt_one ht.le
  have hlogm : Real.log (m : ℝ) ≤ 2 * L := by
    simpa only [m, L] using log_natFloor_add_one_le_two_mul_log_abs ht
  have hlogm0 : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg hmone
  have hP0 : 0 ≤ P := by positivity
  have hP : P ≤ 3 * Real.exp A := by
    simpa only [m, P] using natFloor_add_one_rpow_one_sub_sigma_le hA ht hσ
  have hinv : 1 / σ ≤ 2 := by
    rw [div_le_iff₀ hσpos]
    nlinarith
  have hinv0 : 0 ≤ 1 / σ := by positivity
  have hinv2 : 1 / σ ^ 2 ≤ 4 := by
    rw [div_le_iff₀ (sq_pos_of_pos hσpos)]
    nlinarith
  have hinv20 : 0 ≤ 1 / σ ^ 2 := by positivity
  have hnorm : ‖s‖ ≤ |t| + 2 := by
    simpa only [s] using norm_sigma_add_tI_le_abs_add_two hA ht hσ hσ2
  have habsm : |t| < (m : ℝ) := by
    exact_mod_cast (abs_lt_natFloor_add_one (t := t))
  have hnormm : ‖s‖ ≤ 3 * (m : ℝ) := by linarith
  have hmneg0 : 0 ≤ (m : ℝ) ^ (-σ) := by positivity
  have hmnegP : (m : ℝ) ^ (-σ) ≤ P := by
    exact Real.rpow_le_rpow_of_exponent_le hmone (by linarith)
  have hm_mul_neg : (m : ℝ) * (m : ℝ) ^ (-σ) = P := by
    dsimp only [P]
    rw [show 1 - σ = 1 + (-σ) by ring, Real.rpow_add hmpos, Real.rpow_one]
  have hnorm_neg : ‖s‖ * (m : ℝ) ^ (-σ) ≤ 3 * P := by
    calc
      ‖s‖ * (m : ℝ) ^ (-σ) ≤ (3 * (m : ℝ)) * (m : ℝ) ^ (-σ) :=
        mul_le_mul_of_nonneg_right hnormm hmneg0
      _ = 3 * P := by rw [← hm_mul_neg]; ring
  have hweight : ‖logCpowWeight s m‖ ≤ 2 * L * P := by
    rw [logCpowWeight, norm_mul, norm_neg, norm_real, Real.norm_eq_abs,
      abs_of_nonneg hlogm0, cpowWeight,
      Complex.norm_cpow_eq_rpow_re_of_pos hmpos]
    simp only [s, add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im, mul_zero,
      mul_one, sub_self, add_zero, neg_re]
    exact mul_le_mul hlogm hmnegP hmneg0 (by positivity)
  have hbudget : logVariationBudget s m ≤ (14 + 12 * L) * P := by
    rw [logVariationBudget]
    have hlogdiv : Real.log (m : ℝ) / σ ≤ 4 * L := by
      rw [div_eq_mul_inv]
      calc
        Real.log (m : ℝ) * σ⁻¹ ≤ (2 * L) * 2 :=
          mul_le_mul hlogm (by simpa only [one_div] using hinv)
            (by simpa only [one_div] using hinv0) (by positivity)
        _ = 4 * L := by ring
    calc
      (m : ℝ) ^ (-s.re) *
          (1 / s.re + ‖s‖ * (Real.log (m : ℝ) / s.re + 1 / s.re ^ 2)) =
        (m : ℝ) ^ (-σ) * (1 / σ) +
          (‖s‖ * (m : ℝ) ^ (-σ)) * (Real.log (m : ℝ) / σ) +
          (‖s‖ * (m : ℝ) ^ (-σ)) * (1 / σ ^ 2) := by
            simp only [s, add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im,
              mul_zero, mul_one, sub_self, add_zero]
            ring
      _ ≤ P * 2 + (3 * P) * (4 * L) + (3 * P) * 4 := by
        gcongr
      _ ≤ (14 + 12 * L) * P := by
        ring_nf
        exact le_rfl
  have htail : ‖logCpowWeight s m‖ + logVariationBudget s m ≤ 100 * Real.exp A * L ^ 2 := by
    calc
      _ ≤ (2 * L + (14 + 12 * L)) * P := by linarith
      _ ≤ (2 * L + (14 + 12 * L)) * (3 * Real.exp A) := by
        gcongr
      _ ≤ 100 * Real.exp A * L ^ 2 := by
        have hexp : 0 < Real.exp A := Real.exp_pos A
        nlinarith [sq_nonneg (L - 1)]
  dsimp only
  change (q : ℝ) * (‖logCpowWeight s m‖ + logVariationBudget s m) ≤ _
  calc
    _ ≤ (q : ℝ) * (100 * Real.exp A * L ^ 2) :=
      mul_le_mul_of_nonneg_left htail (Nat.cast_nonneg q)
    _ = Real.exp A * (100 * q) * L ^ 2 := by ring

/-- Fully explicit weak-strip derivative bound, with the Abel tail absorbed. -/
theorem norm_deriv_LFunction_le_fixed_log_sq
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {A C σ t : ℝ} (hA : A ∈ Set.Ioc 0 (1 / 2))
    (hσ : 1 - A / Real.log |t| ≤ σ) (hσ2 : σ ≤ 2)
    (ht : 3 < |t|) (hC : 2 ≤ C) :
    ‖deriv χ.LFunction (σ + t * I)‖ ≤
      Real.exp A * (C + 100 * q) * (Real.log |t|) ^ 2 := by
  have hmain := norm_deriv_LFunction_le_truncation_add_tail χ hχ hA hσ ht hC
  have htail := canonical_tail_le_fixed_log_sq (q := q) hA hσ hσ2 ht
  dsimp only at hmain htail
  have hsum := hmain.trans (add_le_add_right htail _)
  calc
    ‖deriv χ.LFunction (σ + t * I)‖ ≤
        Real.exp A * C * (Real.log |t|) ^ 2 +
          Real.exp A * (100 * q) * (Real.log |t|) ^ 2 := by
            simpa only [Nat.cast_add, Nat.cast_one] using hsum
    _ = Real.exp A * (C + 100 * q) * (Real.log |t|) ^ 2 := by ring

end DirichletLWeakStripDerivativeBound
