module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Tactic

@[expose] public section

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
    linarith
  have hprod : (N : ℝ) ^ (1 / 3 : ℝ) * (a : ℝ) ≤ N := by
    calc
      _ ≤ (N : ℝ) ^ (1 / 3 : ℝ) * (N : ℝ) ^ (2 / 3 : ℝ) :=
        mul_le_mul_of_nonneg_left haN (by positivity)
      _ = N := by rw [← Real.rpow_add hN0]; norm_num
  have hfloor : (N : ℝ) < (N / a : ℕ) * (a : ℝ) + a := by
    exact_mod_cast (Nat.lt_div_mul_add (show 0 < a by omega) : N < N / a * a + a)
  have hlt : (N : ℝ) ^ (1 / 3 : ℝ) < (N / a : ℕ) + 1 := by nlinarith
  linarith

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

/-- Enlarge the logarithmic conductor exponent after passing to a quotient. -/
theorem log_rpow_le_quotient_log_rpow_succ {L l K b : ℝ}
    (hL : 0 ≤ L) (hl : 0 < l) (hK : 0 ≤ K) (hb : 0 ≤ b)
    (hlogs : L ≤ K * l) (hpay : K ^ b ≤ l) :
    L ^ b ≤ l ^ (b + 1) := by
  calc
    _ ≤ (K * l) ^ b := Real.rpow_le_rpow hL hlogs hb
    _ = K ^ b * l ^ b := Real.mul_rpow hK hl.le
    _ ≤ l * l ^ b := mul_le_mul_of_nonneg_right hpay (by positivity)
    _ = _ := by rw [Real.rpow_add hl, Real.rpow_one, mul_comm]

/-- Transfer a logarithmic saving from a quotient using bounds for its size and logarithm. -/
theorem div_log_rpow_le_of_quotient {N y a : ℕ} {J K s Z : ℝ}
    (ha : 0 < a) (hJ : 0 ≤ J) (hK : 0 < K) (hs : 0 ≤ s)
    (hN : 0 < Real.log (N : ℝ)) (hy : 0 < Real.log (y : ℝ))
    (hlogs : Real.log (N : ℝ) ≤ K * Real.log (y : ℝ))
    (hsize : (y : ℝ) * a ≤ Z) :
    J * (y : ℝ) / Real.log (y : ℝ) ^ s ≤
      (J * K ^ s * Z / Real.log (N : ℝ) ^ s) / (a : ℝ) := by
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have hZ : 0 ≤ Z := (by positivity : 0 ≤ (y : ℝ) * a).trans hsize
  have hpower : Real.log (N : ℝ) ^ s / K ^ s ≤ Real.log (y : ℝ) ^ s := by
    apply (div_le_iff₀ (Real.rpow_pos_of_pos hK s)).2
    rw [mul_comm, ← Real.mul_rpow hK.le hy.le]
    exact Real.rpow_le_rpow hN.le hlogs hs
  apply (le_div_iff₀ ha').2
  rw [div_mul_eq_mul_div, mul_assoc J]
  calc
    _ ≤ (J * Z) / (Real.log (N : ℝ) ^ s / K ^ s) :=
      div_le_div₀ (mul_nonneg hJ hZ) (mul_le_mul_of_nonneg_left hsize hJ)
        (by positivity) hpower
    _ = _ := by rw [div_div_eq_mul_div, mul_right_comm]

end
end AnalyticNumberTheory.LargeSieve.PanQuotientBounds
