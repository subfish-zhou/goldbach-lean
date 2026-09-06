import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

namespace AnalyticNumberTheory.LargeSieve.PanQuotientBounds
open Filter
open scoped Topology
noncomputable section

theorem eventually_nat_div_quarter :
    ∀ᶠ N : ℕ in atTop, ∀ a : ℕ, 1 ≤ a →
      (a : ℝ) ≤ (N : ℝ) ^ (2 / 3 : ℝ) →
      (N : ℝ) ^ (1 / 4 : ℝ) ≤ (N / a : ℕ) := by
  have hg := ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 12)).comp
    tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop (2 : ℝ))
  filter_upwards [hg, eventually_ge_atTop (1 : ℕ)] with N hG hN
  dsimp only [Function.comp_apply] at hG
  intro a ha haN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by positivity
  have ha0 : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by omega)
  have hquarter : 1 ≤ (N : ℝ) ^ (1 / 4 : ℝ) :=
    Real.one_le_rpow hN1 (by norm_num)
  have hsplit : (N : ℝ) ^ (1 / 4 : ℝ) * (N : ℝ) ^ (1 / 12 : ℝ) =
      (N : ℝ) ^ (1 / 3 : ℝ) := by
    rw [← Real.rpow_add hN0]; norm_num
  have hgap : (N : ℝ) ^ (1 / 4 : ℝ) + 1 ≤ (N : ℝ) ^ (1 / 3 : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hG (Real.rpow_nonneg hN0.le (1 / 4 : ℝ))
    rw [hsplit] at h
    linarith only [hquarter, h]
  have hprod : (N : ℝ) ^ (1 / 3 : ℝ) * (a : ℝ) ≤ N := by
    calc
      _ ≤ (N : ℝ) ^ (1 / 3 : ℝ) * (N : ℝ) ^ (2 / 3 : ℝ) :=
        mul_le_mul_of_nonneg_left haN (by positivity)
      _ = N := by rw [← Real.rpow_add hN0]; norm_num
  have hfloor : (N : ℝ) < (N / a : ℕ) * (a : ℝ) + a := by
    exact_mod_cast (Nat.lt_div_mul_add (show 0 < a by omega) : N < N / a * a + a)
  have hlt : (N : ℝ) ^ (1 / 3 : ℝ) < (N / a : ℕ) + 1 := by
    apply (mul_lt_mul_iff_left₀ ha0).mp
    calc
      (N : ℝ) ^ (1 / 3 : ℝ) * (a : ℝ) ≤ N := hprod
      _ < ((N / a : ℕ) + 1) * (a : ℝ) := by
        simpa only [add_mul, one_mul] using hfloor
  linarith only [hgap, hlt]

theorem eventually_quotient_parameters (b : ℝ) (M : ℕ) :
    ∀ᶠ N : ℕ in atTop, ∀ a : ℕ, 1 ≤ a →
      (a : ℝ) ≤ (N : ℝ) ^ (2 / 3 : ℝ) →
      M ≤ N / a ∧ 0 < Real.log (N : ℝ) ∧
      0 < Real.log (N / a : ℕ) ∧
      Real.log (N : ℝ) ≤ 4 * Real.log (N / a : ℕ) ∧
      (4 : ℝ) ^ b ≤ Real.log (N / a : ℕ) := by
  have hp := ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp
    tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop (M : ℝ))
  have hl := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
    (eventually_ge_atTop (4 * (4 : ℝ) ^ b))
  filter_upwards [eventually_nat_div_quarter, hp, hl, eventually_ge_atTop (2 : ℕ)]
    with N hQ hP hL hN
  dsimp only [Function.comp_apply] at hP hL
  intro a ha haN
  have hQ' := hQ a ha haN
  have hN1 : (1 : ℝ) < N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by positivity
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos hN1
  have hcomp := Real.log_le_log (Real.rpow_pos_of_pos hN0 (1 / 4 : ℝ)) hQ'
  rw [Real.log_rpow hN0] at hcomp
  have hlogt : 0 < Real.log (N / a : ℕ) := by linarith
  refine ⟨?_, hlogN, hlogt, ?_, ?_⟩
  · exact_mod_cast hP.trans hQ'
  · linarith
  · linarith

end
end AnalyticNumberTheory.LargeSieve.PanQuotientBounds