import MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLGlobalConductorLogValueBound
import MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLConditionalDerivativeAnalyticContinuation
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# A squared-logarithmic conductor-height bound for Dirichlet L-derivatives

The naturally ordered derivative series is cut at the shared cutoff
`q * (⌊|t|⌋₊ + 1)`.  Its finite prefix is estimated by a harmonic sum, and in
the Abel tail the factor `q / m` pays for the full height of the argument.
-/

open Complex Finset

namespace DirichletLGlobalConductorLogDerivativeBound

open DirichletLAbelWeightVariation
open DirichletLConditionalDerivativeSeries
open DirichletLConditionalDerivativeAnalyticContinuation
open DirichletLGlobalConductorLogValueBound

variable {q : ℕ} [NeZero q]

private lemma character_nat_zero_of_ne_one
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) : χ (0 : ℕ) = 0 := by
  exact DirichletLConditionalValueSeries.character_nat_zero_of_ne_one χ hχ

private lemma rpow_one_sub_le_exp_one
    {m k : ℕ} {σ : ℝ} (hm : 2 ≤ m) (hk1 : 1 ≤ k) (hkm : k ≤ m)
    (hnear : 1 - 1 / Real.log m ≤ σ) :
    (k : ℝ) ^ (1 - σ) ≤ Real.exp 1 := by
  exact DirichletLGlobalConductorLogValueBound.rpow_one_sub_le_exp_one hm hk1 hkm hnear

private lemma norm_derivative_prefix_le
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {σ t : ℝ} {m : ℕ}
    (hm : 2 ≤ m) (hnear : 1 - 1 / Real.log m ≤ σ) :
    ‖∑ k ∈ range m, logCpowWeight (σ + I * t) k * χ k‖ ≤
      2 * Real.exp 1 * Real.log m * (1 + Real.log m) := by
  have hlogm0 : 0 ≤ Real.log (m : ℝ) := (Real.log_pos (by exact_mod_cast hm)).le
  calc
    _ ≤ ∑ k ∈ range m, ‖logCpowWeight (σ + I * t) k * χ k‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ range m,
        2 * Real.exp 1 * Real.log m * ((k + 1 : ℕ) : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro k hk
      by_cases hk0 : k = 0
      · subst k
        rw [character_nat_zero_of_ne_one χ hχ]
        simp
        positivity
      · have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
        have hkm : k < m := Finset.mem_range.mp hk
        have hkpos : (0 : ℝ) < k := by exact_mod_cast (Nat.zero_lt_of_ne_zero hk0)
        have hpow := rpow_one_sub_le_exp_one hm hk1 hkm.le hnear
        have hlogk0 : 0 ≤ Real.log (k : ℝ) := Real.log_nonneg (by exact_mod_cast hk1)
        have hlogkm : Real.log (k : ℝ) ≤ Real.log (m : ℝ) :=
          Real.strictMonoOn_log.monotoneOn hkpos
            (show (0 : ℝ) < (m : ℝ) by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hm))
            (by exact_mod_cast hkm.le)
        have hinv : (k : ℝ)⁻¹ ≤ 2 * ((k + 1 : ℕ) : ℝ)⁻¹ := by
          rw [inv_eq_one_div, show 2 * ((k + 1 : ℕ) : ℝ)⁻¹ =
            2 / ((k + 1 : ℕ) : ℝ) by rw [div_eq_mul_inv]]
          rw [div_le_div_iff₀ hkpos (by positivity)]
          push_cast
          have hk1R : (1 : ℝ) ≤ k := by exact_mod_cast hk1
          nlinarith
        calc
          ‖logCpowWeight (σ + I * t) k * χ k‖
              ≤ ‖logCpowWeight (σ + I * t) k‖ := by
                rw [norm_mul]
                exact mul_le_of_le_one_right (norm_nonneg _) (χ.norm_le_one k)
          _ = Real.log (k : ℝ) * (k : ℝ) ^ (-σ) := by
                rw [logCpowWeight, norm_mul, norm_neg, norm_real, Real.norm_eq_abs,
                  abs_of_nonneg hlogk0, cpowWeight,
                  Complex.norm_cpow_eq_rpow_re_of_pos hkpos]
                simp
          _ = Real.log (k : ℝ) * ((k : ℝ) ^ (1 - σ) * (k : ℝ)⁻¹) := by
                rw [← Real.rpow_neg_one, ← Real.rpow_add hkpos]
                congr 2
                ring
          _ ≤ Real.log m * (Real.exp 1 * (k : ℝ)⁻¹) := by
                exact mul_le_mul hlogkm
                  (mul_le_mul_of_nonneg_right hpow (by positivity))
                  (by positivity) hlogm0
          _ ≤ Real.log m * (Real.exp 1 *
                (2 * ((k + 1 : ℕ) : ℝ)⁻¹)) :=
                mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_left hinv (Real.exp_pos 1).le) hlogm0
          _ = 2 * Real.exp 1 * Real.log m * ((k + 1 : ℕ) : ℝ)⁻¹ := by ring
    _ = 2 * Real.exp 1 * Real.log m * (harmonic m : ℝ) := by
      simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
      rw [Finset.mul_sum]
    _ ≤ 2 * Real.exp 1 * Real.log m * (1 + Real.log m) := by
      exact mul_le_mul_of_nonneg_left
        (by exact_mod_cast harmonic_le_one_add_log m)
        (mul_nonneg (mul_nonneg (by norm_num) (Real.exp_pos 1).le) hlogm0)

private lemma norm_derivative_tail_le
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {σ t : ℝ}
    (hσlower : 1 / 2 ≤ σ) (hσupper : σ ≤ 2)
    (hnear : 1 - 1 / Real.log (dirichletLConductorHeightCutoff q t) ≤ σ) :
    ‖orderedLogDerivativeSeries χ hχ (σ + I * t)
        (by have hσpos : 0 < σ := lt_of_lt_of_le (by norm_num) hσlower
            simpa using hσpos) -
        ∑ k ∈ range (dirichletLConductorHeightCutoff q t),
          logCpowWeight (σ + I * t) k * χ k‖ ≤
      3 * (14 + 7 * Real.log (dirichletLConductorHeightCutoff q t)) := by
  let H := dirichletLHeightBlock t
  let m := dirichletLConductorHeightCutoff q t
  let s : ℂ := σ + I * t
  let L : ℝ := Real.log m
  let P : ℝ := (m : ℝ) ^ (1 - σ)
  have hm : 2 ≤ m := two_le_conductorHeightCutoff χ hχ t
  have hH1 : (1 : ℝ) ≤ H := by exact_mod_cast one_le_heightBlock t
  have hHpos : (0 : ℝ) < H := lt_of_lt_of_le zero_lt_one hH1
  have htH : |t| < (H : ℝ) := by simpa [H] using abs_lt_heightBlock t
  have hσpos : 0 < σ := lt_of_lt_of_le (by norm_num) hσlower
  have hL0 : 0 ≤ L := (log_conductorHeightCutoff_pos χ hχ t).le
  have hP0 : 0 ≤ P := by positivity
  have hP : P ≤ Real.exp 1 :=
    rpow_one_sub_le_exp_one hm (by omega) (le_refl m) (by simpa [m] using hnear)
  have he : Real.exp 1 < 3 := Real.exp_one_lt_three
  have hnorm : ‖s‖ ≤ σ + |t| := by
    dsimp [s]
    calc
      _ ≤ ‖(σ : ℂ)‖ + ‖I * (t : ℂ)‖ := norm_add_le _ _
      _ = |σ| + |t| := by simp
      _ = σ + |t| := by rw [abs_of_pos hσpos]
  have hnormH : ‖s‖ / (H : ℝ) ≤ 3 := by
    rw [div_le_iff₀ hHpos]
    nlinarith
  have hinv : 1 / σ ≤ 2 := by
    rw [div_le_iff₀ hσpos]
    nlinarith
  have hinv2 : 1 / σ ^ 2 ≤ 4 := by
    rw [div_le_iff₀ (sq_pos_of_pos hσpos)]
    nlinarith
  have hsre : s.re = σ := by simp [s]
  have hfactor : (q : ℝ) * (m : ℝ) ^ (-σ) = P / H := by
    dsimp [P]
    have hqpos : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
    have hmcast : (m : ℝ) = (q : ℝ) * (H : ℝ) := by
      simp [m, H, dirichletLConductorHeightCutoff]
    rw [show -σ = (1 - σ) + (-1) by ring, Real.rpow_add (by positivity),
      Real.rpow_neg_one, hmcast, div_eq_mul_inv]
    field_simp [ne_of_gt hqpos]
  have hweight : (q : ℝ) * ‖logCpowWeight s m‖ ≤ P * L := by
    have hmpos : (0 : ℝ) < m := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hm)
    have hw : ‖logCpowWeight s m‖ = L * (m : ℝ) ^ (-σ) := by
      rw [logCpowWeight, norm_mul, norm_neg, norm_real, Real.norm_eq_abs,
        abs_of_nonneg hL0, cpowWeight, Complex.norm_cpow_eq_rpow_re_of_pos hmpos]
      simp only [neg_re, hsre]
    calc
      (q : ℝ) * ‖logCpowWeight s m‖ = L * ((q : ℝ) * (m : ℝ) ^ (-σ)) := by
        rw [hw]
        ring
      _ = L * (P / H) := by rw [hfactor]
      _ ≤ L * P := mul_le_mul_of_nonneg_left (div_le_self hP0 hH1) hL0
      _ = P * L := by ring
  have hbudget : (q : ℝ) * logVariationBudget s m ≤ P * (14 + 6 * L) := by
    rw [logVariationBudget, hsre]
    have hinv0 : 0 ≤ 1 / σ := by positivity
    have hinner :
        (1 / σ) / (H : ℝ) + (‖s‖ / (H : ℝ)) * (L / σ + 1 / σ ^ 2) ≤
          14 + 6 * L := by
      have hfirst : (1 / σ) / (H : ℝ) ≤ 2 :=
        (div_le_self hinv0 hH1).trans hinv
      have hinv' : σ⁻¹ ≤ 2 := by simpa only [one_div] using hinv
      have hlog : L / σ ≤ 2 * L := by
        rw [div_eq_mul_inv]
        simpa only [mul_comm] using mul_le_mul_of_nonneg_left hinv' hL0
      have hparen : L / σ + 1 / σ ^ 2 ≤ 2 * L + 4 := add_le_add hlog hinv2
      have hsecond : (‖s‖ / (H : ℝ)) * (L / σ + 1 / σ ^ 2) ≤
          3 * (2 * L + 4) := by
        exact mul_le_mul hnormH hparen (by positivity) (by norm_num)
      nlinarith
    calc
      (q : ℝ) * ((m : ℝ) ^ (-σ) *
          (1 / σ + ‖s‖ * (L / σ + 1 / σ ^ 2))) =
          P * ((1 / σ) / (H : ℝ) +
            (‖s‖ / (H : ℝ)) * (L / σ + 1 / σ ^ 2)) := by
              rw [← mul_assoc, hfactor]
              ring
      _ ≤ P * (14 + 6 * L) := mul_le_mul_of_nonneg_left hinner hP0
  have htail := norm_orderedLogDerivativeSeries_sub_sum_range_le
    χ hχ s (by simpa [hsre] using hσpos) (m := m) (by omega)
  calc
    _ ≤ (q : ℝ) * (‖logCpowWeight s m‖ + logVariationBudget s m) := by
      simpa [m, s] using htail
    _ = (q : ℝ) * ‖logCpowWeight s m‖ +
        (q : ℝ) * logVariationBudget s m := by ring
    _ ≤ P * L + P * (14 + 6 * L) := add_le_add hweight hbudget
    _ = P * (14 + 7 * L) := by ring
    _ ≤ 3 * (14 + 7 * L) :=
      mul_le_mul (hP.trans he.le) le_rfl (by positivity) (by norm_num)

/-- Near the line `re s = 1`, the derivative has squared-logarithmic growth in
the conductor-height cutoff, with no positive power of either modulus or height. -/
theorem norm_deriv_LFunction_le_sixtyfour_mul_one_add_log_sq_conductorHeightCutoff
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {σ t : ℝ}
    (hσlower : 1 / 2 ≤ σ) (hσupper : σ ≤ 2)
    (hnear : 1 - 1 / Real.log (dirichletLConductorHeightCutoff q t) ≤ σ) :
    ‖deriv χ.LFunction (σ + I * t)‖ ≤
      64 * (1 + Real.log (dirichletLConductorHeightCutoff q t)) ^ 2 := by
  let m := dirichletLConductorHeightCutoff q t
  let L : ℝ := Real.log m
  have hm : 2 ≤ m := two_le_conductorHeightCutoff χ hχ t
  have hL0 : 0 ≤ L := (log_conductorHeightCutoff_pos χ hχ t).le
  have hσpos : 0 < σ := lt_of_lt_of_le (by norm_num) hσlower
  have hseries := orderedLogDerivativeSeries_eq_deriv_LFunction_of_re_pos
    χ hχ (σ + I * t) (by simpa using hσpos)
  have hprefix := norm_derivative_prefix_le χ hχ (σ := σ) (t := t) (m := m)
    hm (by simpa [m] using hnear)
  have htail := norm_derivative_tail_le χ hχ hσlower hσupper hnear
  change ‖deriv χ.LFunction (σ + I * t)‖ ≤ 64 * (1 + L) ^ 2
  rw [← hseries]
  calc
    _ ≤ ‖orderedLogDerivativeSeries χ hχ (σ + I * t) (by simpa using hσpos) -
          ∑ k ∈ range m, logCpowWeight (σ + I * t) k * χ k‖ +
        ‖∑ k ∈ range m, logCpowWeight (σ + I * t) k * χ k‖ :=
          norm_le_norm_sub_add _ _
    _ ≤ 3 * (14 + 7 * L) + 2 * Real.exp 1 * L * (1 + L) := by
      simpa [m, L] using add_le_add htail hprefix
    _ ≤ 3 * (14 + 7 * L) + 6 * L * (1 + L) := by
      have hcoef : 2 * Real.exp 1 ≤ 6 := by
        linarith only [Real.exp_one_lt_three]
      gcongr
    _ ≤ 64 * (1 + L) ^ 2 := by
      nlinarith

end DirichletLGlobalConductorLogDerivativeBound