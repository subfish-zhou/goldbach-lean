import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open Filter
open scoped Topology

namespace MathlibNt.Analysis

/-- A fixed positive logarithmic saving absorbs every fixed coefficient,
uniformly in the normalization exponent and every weight with a positive
uniform lower bound. The cutoff precedes both varying parameters `p` and `s`. -/
theorem eventually_log_rpow_remainder_lt_of_lower_bound
    (C u ρ κ : ℝ) (hu : 0 < u) (hρ : 0 < ρ) (hκ : 0 < κ) :
    ∀ᶠ N : ℕ in atTop, ∀ p s : ℝ, u ≤ s →
      C * (N : ℝ) / Real.log (N : ℝ) ^ (p + κ) <
        ρ * s * (N : ℝ) / Real.log (N : ℝ) ^ p := by
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hpow : Tendsto
      (fun N : ℕ => Real.log (N : ℝ) ^ κ) atTop atTop :=
    (tendsto_rpow_atTop hκ).comp hlog
  have hratio : Tendsto
      (fun N : ℕ => C / Real.log (N : ℝ) ^ κ) atTop (𝓝 0) :=
    hpow.const_div_atTop C
  have hsmall : ∀ᶠ N : ℕ in atTop,
      C / Real.log (N : ℝ) ^ κ < ρ * u :=
    hratio.eventually (gt_mem_nhds (mul_pos hρ hu))
  filter_upwards [hsmall, eventually_ge_atTop (2 : ℕ)] with N hsmallN hN
  intro p s hs
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlogpos : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hp : 0 < Real.log (N : ℝ) ^ p := Real.rpow_pos_of_pos hlogpos p
  have hk : 0 < Real.log (N : ℝ) ^ κ := Real.rpow_pos_of_pos hlogpos κ
  have hcoef : C / Real.log (N : ℝ) ^ κ < ρ * s :=
    lt_of_lt_of_le hsmallN (mul_le_mul_of_nonneg_left hs hρ.le)
  calc
    C * (N : ℝ) / Real.log (N : ℝ) ^ (p + κ) =
        (C / Real.log (N : ℝ) ^ κ) *
          ((N : ℝ) / Real.log (N : ℝ) ^ p) := by
      rw [Real.rpow_add hlogpos]
      field_simp [hp.ne', hk.ne']
    _ < (ρ * s) * ((N : ℝ) / Real.log (N : ℝ) ^ p) :=
      mul_lt_mul_of_pos_right hcoef (div_pos hNpos hp)
    _ = ρ * s * (N : ℝ) / Real.log (N : ℝ) ^ p := by ring

end MathlibNt.Analysis
