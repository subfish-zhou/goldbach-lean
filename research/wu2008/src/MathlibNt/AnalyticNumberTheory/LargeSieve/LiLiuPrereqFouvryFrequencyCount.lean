import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryExtractedAnalyticReduction
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Uniform logarithmic cost of the actual frequency shells

The count bound depends only on the ambient scale and the fixed cutoff
exponent, not the residue, nu, coefficient family, or surviving masks.
-/

noncomputable section
open Filter
open scoped Topology

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

theorem log_two_ceil_rpow_bound {x C : ℝ} (hx : 1 ≤ x) (hC : 0 ≤ C) :
    (Nat.log 2 ⌈x ^ C⌉₊ + 1 : ℕ) ≤
      2 + C * Real.log x / Real.log 2 := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hp := Real.rpow_pos_of_pos hx0 C
  have hp1 : 1 ≤ x ^ C := Real.one_le_rpow hx hC
  have hc : (⌈x ^ C⌉₊ : ℝ) ≤ 2 * x ^ C := by
    have hh := Nat.ceil_lt_add_one hp.le
    linarith
  have hcp : (0 : ℝ) < ⌈x ^ C⌉₊ := by
    exact_mod_cast Nat.ceil_pos.mpr hp
  have hlog : Real.log (⌈x ^ C⌉₊ : ℝ) ≤ Real.log 2 + C * Real.log x := by
    calc
      _ ≤ Real.log (2 * x ^ C) := Real.log_le_log hcp hc
      _ = _ := by rw [Real.log_mul (by norm_num) hp.ne', Real.log_rpow hx0]
  have hn := Real.natLog_le_logb ⌈x ^ C⌉₊ 2
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  simp only [Real.logb, Nat.cast_ofNat] at hn
  have hb := hn.trans (div_le_div_of_nonneg_right hlog htwo.le)
  push_cast
  calc
    (Nat.log 2 ⌈x ^ C⌉₊ : ℝ) + 1 ≤
        (Real.log 2 + C * Real.log x) / Real.log 2 + 1 := by linarith
    _ = _ := by field_simp; ring

/-- The full-level cutoff is at most a fixed power of x. This merely
bounds the number of shells; individual cutoff tests stay unchanged. -/
theorem fullLevel_frequency_count_bound {x L M η : ℝ}
    (hx : 1 ≤ x) (hL0 : 0 ≤ L) (hL : L ≤ x) (hM : 1 ≤ M) (hη : 0 ≤ η) :
    (Nat.log 2 ⌈L ^ 2 / M * x ^ η⌉₊ + 1 : ℕ) ≤
      2 + (η + 2) * Real.log x / Real.log 2 := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hM0 : 0 < M := lt_of_lt_of_le zero_lt_one hM
  have hb : L ^ 2 / M * x ^ η ≤ x ^ (η + 2) := by
    calc
      _ ≤ L ^ 2 * x ^ η := mul_le_mul_of_nonneg_right
        ((div_le_iff₀ hM0).mpr (by nlinarith [sq_nonneg L]))
        (Real.rpow_nonneg hx0.le η)
      _ ≤ x ^ 2 * x ^ η := mul_le_mul_of_nonneg_right
        (by nlinarith) (Real.rpow_nonneg hx0.le η)
      _ = x ^ (η + 2) := by
        rw [Real.rpow_add hx0, Real.rpow_two]
        ring
  have hn := Nat.add_le_add_right (Nat.log_mono_right (b := 2) (Nat.ceil_mono hb)) 1
  exact (Nat.cast_le.mpr hn).trans (log_two_ceil_rpow_bound hx (by linarith))


/-- A fixed power margin absorbs the shell count uniformly over both
varying scales. The threshold is chosen before L and M. -/
theorem eventually_fullLevel_frequency_count_le_rpow {η δ : ℝ}
    (hη : 0 ≤ η) (hδ : 0 < δ) :
    ∀ᶠ x : ℝ in atTop, ∀ L M : ℝ, 0 ≤ L → L ≤ x → 1 ≤ M →
      ((Nat.log 2 ⌈L ^ 2 / M * x ^ η⌉₊ + 1 : ℕ) : ℝ) ≤ x ^ δ := by
  have hc : (fun _ : ℝ => (2 : ℝ)) =o[atTop] (fun x : ℝ => x ^ δ) :=
    (Asymptotics.isLittleO_const_id_atTop (2 : ℝ)).comp_tendsto
      (tendsto_rpow_atTop hδ)
  have hs := hc.add ((isLittleO_log_rpow_atTop hδ).const_mul_left
    ((η + 2) / Real.log 2))
  filter_upwards [hs.bound (by norm_num : (0 : ℝ) < 1),
    eventually_ge_atTop (1 : ℝ)] with x hx hx1
  intro L M hL0 hL hM
  have hb : 2 + (η + 2) * Real.log x / Real.log 2 ≤ x ^ δ := by
    have hp := Real.rpow_nonneg (by linarith : 0 ≤ x) δ
    have ha := (le_abs_self _).trans (show
        |2 + (η + 2) / Real.log 2 * Real.log x| ≤ x ^ δ from by
      simpa only [Real.norm_eq_abs, one_mul, abs_of_nonneg hp] using hx)
    simpa only [div_mul_eq_mul_div] using ha
  exact (fullLevel_frequency_count_bound hx1 hL0 hL hM hη).trans hb


end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
