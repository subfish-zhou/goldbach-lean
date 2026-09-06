import Mathlib.NumberTheory.Harmonic.Bounds
import MathlibNt.SieveTheory.Selberg.Liu.LiuSelbergCorrectionEuler

/-!
# Harmonic remainder in Liu's Selberg denominator

This file isolates the elementary harmonic error in the exact denominator
convolution.  All estimates are pointwise in the fixed even integer `N`.
-/

open scoped BigOperators

namespace MathlibNt.SieveTheory.LiuWeight

open Finset
open MathlibNt.SieveTheory.SingularSeries

theorem liuHarmonic_eq_harmonic (m : ℕ) :
    liuHarmonic m = (harmonic m : ℝ) := by
  rw [liuHarmonic, harmonic_eq_sum_Icc, Rat.cast_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Rat.cast_inv, Rat.cast_natCast]

theorem log_add_one_le_liuHarmonic (m : ℕ) :
    Real.log (m + 1) ≤ liuHarmonic m := by
  rw [liuHarmonic_eq_harmonic]
  simpa only [Nat.cast_add, Nat.cast_one] using log_add_one_le_harmonic m

theorem liuHarmonic_le_one_add_log (m : ℕ) :
    liuHarmonic m ≤ 1 + Real.log m := by
  rw [liuHarmonic_eq_harmonic]
  exact harmonic_le_one_add_log m

/-- The error left after replacing `H_{⌊x/d⌋}` by `log x - log d`. -/
noncomputable def liuHarmonicResidual (x d : ℕ) : ℝ :=
  liuHarmonic (x / d) - (Real.log x - Real.log d)

theorem liuHarmonicResidual_nonneg_le_one
    {x d : ℕ} (hd : d ∈ Finset.Icc 1 x) :
    0 ≤ liuHarmonicResidual x d ∧ liuHarmonicResidual x d ≤ 1 := by
  have hdpos : 0 < d := (Finset.mem_Icc.mp hd).1
  have hdx : d ≤ x := (Finset.mem_Icc.mp hd).2
  have hxpos : 0 < x := lt_of_lt_of_le hdpos hdx
  have hqpos : 0 < x / d := Nat.div_pos hdx hdpos
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hdpos
  have hxR : (0 : ℝ) < (x : ℝ) := by exact_mod_cast hxpos
  have hqR : (0 : ℝ) < ((x / d : ℕ) : ℝ) := by exact_mod_cast hqpos
  have hyR : (0 : ℝ) < (x : ℝ) / (d : ℝ) := div_pos hxR hdR
  have hfloor_lt :
      (x : ℝ) / (d : ℝ) < ((x / d + 1 : ℕ) : ℝ) := by
    rw [div_lt_iff₀ hdR]
    exact_mod_cast (by
      simpa [mul_comm] using Nat.lt_mul_div_succ x hdpos)
  have hfloor_le :
      ((x / d : ℕ) : ℝ) ≤ (x : ℝ) / (d : ℝ) := by
    rw [le_div_iff₀ hdR]
    exact_mod_cast Nat.div_mul_le_self x d
  have hlog_div :
      Real.log ((x : ℝ) / (d : ℝ)) = Real.log x - Real.log d :=
    Real.log_div (ne_of_gt hxR) (ne_of_gt hdR)
  have hlower :
      Real.log x - Real.log d ≤ liuHarmonic (x / d) := by
    rw [← hlog_div]
    refine le_trans
      (Real.strictMonoOn_log.monotoneOn hyR ?_ (le_of_lt hfloor_lt)) ?_
    · change (0 : ℝ) < ((x / d + 1 : ℕ) : ℝ)
      positivity
    · simpa only [Nat.cast_add, Nat.cast_one] using
        log_add_one_le_liuHarmonic (x / d)
  have hupper :
      liuHarmonic (x / d) ≤ 1 + (Real.log x - Real.log d) := by
    rw [← hlog_div]
    refine le_trans (liuHarmonic_le_one_add_log (x / d)) ?_
    simpa only [add_comm] using add_le_add_left
      (Real.strictMonoOn_log.monotoneOn hqR hyR hfloor_le) 1
  constructor <;> dsimp [liuHarmonicResidual] <;> linarith

/-- The signed correction tail beyond `x`, written as an actual indicator family. -/
noncomputable def liuSelbergCorrectionTail (N x : ℕ) : ℕ → ℝ :=
  {d : ℕ | x < d}.indicator (fun d => liuSelbergCorrection N d)

/-- The absolute correction tail beyond `x`, written as an actual indicator family. -/
noncomputable def liuSelbergCorrectionAbsTail (N x : ℕ) : ℕ → ℝ :=
  {d : ℕ | x < d}.indicator (fun d => |liuSelbergCorrection N d|)

theorem summable_abs_liuSelbergCorrection_mul_log_nat
    {N : ℕ} (hNeven : Even N) (hN : 0 < N) :
    Summable (fun d : ℕ => |liuSelbergCorrection N d| * Real.log d) := by
  have hs := (summable_abs_liuSelbergCorrection_mul_log hNeven hN).sub
    ((summable_abs_liuSelbergCorrection hNeven hN).mul_left (Real.log 2))
  apply hs.congr
  intro d
  by_cases hd : d = 0
  · subst d
    simp
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by exact_mod_cast hd)]
  ring

theorem summable_liuSelbergCorrectionTail
    {N x : ℕ} (hNeven : Even N) (hN : 0 < N) :
    Summable (liuSelbergCorrectionTail N x) := by
  have hs : Summable (liuSelbergCorrection N) := by
    apply Summable.of_norm
    simpa only [Real.norm_eq_abs] using
      summable_abs_liuSelbergCorrection hNeven hN
  exact hs.indicator _

theorem summable_liuSelbergCorrectionAbsTail
    {N x : ℕ} (hNeven : Even N) (hN : 0 < N) :
    Summable (liuSelbergCorrectionAbsTail N x) := by
  exact (summable_abs_liuSelbergCorrection hNeven hN).indicator _

theorem liuSelbergCorrection_sum_Icc_add_tail
    {N x : ℕ} (hNeven : Even N) (hN : 0 < N) :
    (∑ d ∈ Finset.Icc 1 x, liuSelbergCorrection N d) +
        ∑' d : ℕ, liuSelbergCorrectionTail N x d =
      ∑' d : ℕ, liuSelbergCorrection N d := by
  have hs : Summable (liuSelbergCorrection N) := by
    apply Summable.of_norm
    simpa only [Real.norm_eq_abs] using
      summable_abs_liuSelbergCorrection hNeven hN
  rw [← hs.sum_add_tsum_subtype_compl (Finset.Icc 1 x)]
  congr 1
  refine Eq.trans ?_
    (_root_.tsum_subtype {d : ℕ | d ∉ Finset.Icc 1 x} (liuSelbergCorrection N)).symm
  apply tsum_congr
  intro d
  by_cases hd0 : d = 0
  · subst d
    simp [liuSelbergCorrectionTail, Set.indicator]
  have hdpos : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr hd0
  simp [liuSelbergCorrectionTail, Set.indicator, Finset.mem_Icc, hdpos, not_le]

/-- Exact separation of the logarithmic main term, the signed correction tail,
the logarithmic moment, and the elementary harmonic residual. -/
theorem liuSelbergArithmetic_sum_Icc_eq_log_main_add_remainders
    {N x : ℕ} (hNeven : Even N) (hN : 0 < N) :
    (∑ n ∈ Finset.Icc 1 x, liuSelbergArithmetic N n) =
      Real.log x * (∑' d : ℕ, liuSelbergCorrection N d) -
        Real.log x * (∑' d : ℕ, liuSelbergCorrectionTail N x d) -
        (∑ d ∈ Finset.Icc 1 x,
          liuSelbergCorrection N d * Real.log d) +
        ∑ d ∈ Finset.Icc 1 x,
          liuSelbergCorrection N d * liuHarmonicResidual x d := by
  rw [liuSelbergArithmetic_sum_Icc]
  have hsplit := liuSelbergCorrection_sum_Icc_add_tail
    (x := x) hNeven hN
  calc
    (∑ d ∈ Finset.Icc 1 x,
        liuSelbergCorrection N d * liuHarmonic (x / d)) =
        ∑ d ∈ Finset.Icc 1 x,
          (liuSelbergCorrection N d * (Real.log x - Real.log d) +
            liuSelbergCorrection N d * liuHarmonicResidual x d) := by
              apply Finset.sum_congr rfl
              intro d hd
              simp only [liuHarmonicResidual]
              ring
    _ = Real.log x *
          (∑ d ∈ Finset.Icc 1 x, liuSelbergCorrection N d) -
        (∑ d ∈ Finset.Icc 1 x,
          liuSelbergCorrection N d * Real.log d) +
        ∑ d ∈ Finset.Icc 1 x,
          liuSelbergCorrection N d * liuHarmonicResidual x d := by
            simp_rw [mul_sub]
            rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
              ← Finset.sum_mul]
            ring
    _ = Real.log x * (∑' d : ℕ, liuSelbergCorrection N d) -
        Real.log x * (∑' d : ℕ, liuSelbergCorrectionTail N x d) -
        (∑ d ∈ Finset.Icc 1 x,
          liuSelbergCorrection N d * Real.log d) +
        ∑ d ∈ Finset.Icc 1 x,
          liuSelbergCorrection N d * liuHarmonicResidual x d := by
            rw [← hsplit]
            ring

/-- A transparent fixed-`N` reduction of the finite Selberg denominator to
three explicit absolutely summable errors.  No uniformity in `N` is asserted. -/
theorem abs_liuSelbergArithmetic_sum_Icc_sub_log_main_le
    {N x : ℕ} (hNeven : Even N) (hN : 0 < N) (_hx : 1 ≤ x) :
    |(∑ n ∈ Finset.Icc 1 x, liuSelbergArithmetic N n) -
        Real.log x / (2 * liuSingularSeries N)| ≤
      Real.log x * (∑' d : ℕ, liuSelbergCorrectionAbsTail N x d) +
        (∑' d : ℕ, |liuSelbergCorrection N d| * Real.log d) +
        ∑' d : ℕ, |liuSelbergCorrection N d| := by
  have hxlog : 0 ≤ Real.log (x : ℝ) := Real.log_natCast_nonneg x
  have habstail := summable_liuSelbergCorrectionAbsTail
    (x := x) hNeven hN
  have habs := summable_abs_liuSelbergCorrection hNeven hN
  have hlog := summable_abs_liuSelbergCorrection_mul_log_nat hNeven hN
  have htail_norm :
      |∑' d : ℕ, liuSelbergCorrectionTail N x d| ≤
        ∑' d : ℕ, liuSelbergCorrectionAbsTail N x d := by
    have hnorm (d : ℕ) :
        ‖liuSelbergCorrectionTail N x d‖ = liuSelbergCorrectionAbsTail N x d := by
      by_cases hd : x < d <;>
        simp [liuSelbergCorrectionTail, liuSelbergCorrectionAbsTail,
          Set.indicator, hd, Real.norm_eq_abs]
    simpa only [hnorm, Real.norm_eq_abs] using
      norm_tsum_le_tsum_norm (habstail.congr fun d => (hnorm d).symm)
  have hmoment :
      |∑ d ∈ Finset.Icc 1 x,
          liuSelbergCorrection N d * Real.log d| ≤
        ∑' d : ℕ, |liuSelbergCorrection N d| * Real.log d := by
    calc
      |∑ d ∈ Finset.Icc 1 x,
          liuSelbergCorrection N d * Real.log d| ≤
          ∑ d ∈ Finset.Icc 1 x,
            |liuSelbergCorrection N d * Real.log d| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ d ∈ Finset.Icc 1 x,
          |liuSelbergCorrection N d| * Real.log d := by
            apply Finset.sum_congr rfl
            intro d hd
            rw [abs_mul, abs_of_nonneg (Real.log_natCast_nonneg d)]
      _ ≤ ∑' d : ℕ, |liuSelbergCorrection N d| * Real.log d :=
        hlog.sum_le_tsum _ (fun d _ =>
          mul_nonneg (abs_nonneg _) (Real.log_natCast_nonneg d))
  have hresidual :
      |∑ d ∈ Finset.Icc 1 x,
          liuSelbergCorrection N d * liuHarmonicResidual x d| ≤
        ∑' d : ℕ, |liuSelbergCorrection N d| := by
    calc
      |∑ d ∈ Finset.Icc 1 x,
          liuSelbergCorrection N d * liuHarmonicResidual x d| ≤
          ∑ d ∈ Finset.Icc 1 x,
            |liuSelbergCorrection N d * liuHarmonicResidual x d| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ d ∈ Finset.Icc 1 x, |liuSelbergCorrection N d| := by
        apply Finset.sum_le_sum
        intro d hd
        rw [abs_mul, abs_of_nonneg
          (liuHarmonicResidual_nonneg_le_one hd).1]
        exact mul_le_of_le_one_right (abs_nonneg _)
          (liuHarmonicResidual_nonneg_le_one hd).2
      _ ≤ ∑' d : ℕ, |liuSelbergCorrection N d| :=
        habs.sum_le_tsum _ (fun d _ => abs_nonneg _)
  rw [liuSelbergArithmetic_sum_Icc_eq_log_main_add_remainders hNeven hN,
    tsum_liuSelbergCorrection hNeven hN]
  let A := -Real.log x * (∑' d : ℕ, liuSelbergCorrectionTail N x d)
  let B := -(∑ d ∈ Finset.Icc 1 x,
    liuSelbergCorrection N d * Real.log d)
  let C := ∑ d ∈ Finset.Icc 1 x,
    liuSelbergCorrection N d * liuHarmonicResidual x d
  have heq :
      Real.log x * (1 / (2 * liuSingularSeries N)) -
          Real.log x * (∑' d : ℕ, liuSelbergCorrectionTail N x d) -
          (∑ d ∈ Finset.Icc 1 x,
            liuSelbergCorrection N d * Real.log d) +
          (∑ d ∈ Finset.Icc 1 x,
            liuSelbergCorrection N d * liuHarmonicResidual x d) -
          Real.log x / (2 * liuSingularSeries N) =
        A + B + C := by
    dsimp [A, B, C]
    ring
  rw [heq]
  calc
    |A + B + C| ≤ |A| + |B| + |C| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le A B) le_rfl)
    _ ≤ Real.log x * (∑' d : ℕ, liuSelbergCorrectionAbsTail N x d) +
          (∑' d : ℕ, |liuSelbergCorrection N d| * Real.log d) +
          ∑' d : ℕ, |liuSelbergCorrection N d| := by
      dsimp [A, B, C]
      rw [abs_mul, abs_neg, abs_of_nonneg hxlog, abs_neg]
      gcongr

end MathlibNt.SieveTheory.LiuWeight
