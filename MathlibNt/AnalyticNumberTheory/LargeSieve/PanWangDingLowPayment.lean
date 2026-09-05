import MathlibNt.AnalyticNumberTheory.LargeSieve.PanWangDingLowMass
import Mathlib.Analysis.SpecialFunctions.Log.Base

namespace AnalyticNumberTheory.LargeSieve.PanLow
open Classical Finset Filter
open scoped BigOperators Topology
noncomputable section

/-- Positive modulus only.  The coarse log N bound is enough; no arithmetic
or analytic estimate stronger than the existing omega bound is used. -/
theorem primeFactors_card_le_log_of_le {m : ℕ} {X : ℝ}
    (hm : 0 < m) (hmX : (m : ℝ) ≤ X) :
    (m.primeFactors.card : ℝ) ≤ (Real.log 2)⁻¹ * Real.log X := by
  calc
    _ ≤ (Nat.log2 m : ℝ) := by exact_mod_cast card_primeFactors_le_log2 hm
    _ ≤ Real.log (m : ℝ) / Real.log 2 := Real.log2_le_logb m
    _ ≤ Real.log X / Real.log 2 := by
      exact div_le_div_of_nonneg_right (Real.log_le_log (by exact_mod_cast hm) hmX)
        (Real.log_nonneg (by norm_num))
    _ = _ := by ring

/-- Pure scalar payment with an explicit elementary log-versus-power premise.
The eventual theorem below discharges that premise before quantifying cells. -/
theorem low_budget_scalar {X L A W R U b K c : ℝ}
    (hX : 0 < X) (hL : 1 ≤ L) (hA0 : 0 ≤ A) (hW0 : 0 ≤ W)
    (_hR0 : 0 ≤ R) (hK : 0 ≤ K) (hc : 0 ≤ c)
    (hA : A ≤ X ^ (2 / 3 : ℝ)) (hW : W ≤ c * L) (hR : R ≤ L ^ b)
    (hlog : L ^ (U + b + 1) ≤ X ^ (1 / 3 : ℝ)) :
    R * ((K * X / L ^ (U + b + 2)) * (1 + L) + A * W) ≤
      (2 * K + c) * X / L ^ U := by
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hmain : L ^ b * ((K * X / L ^ (U + b + 2)) * (1 + L)) ≤
      2 * K * X / L ^ U := by
    calc
      _ ≤ L ^ b * ((K * X / L ^ (U + b + 2)) * (2 * L ^ (2 : ℕ))) := by
        apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hLp.le _)
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        nlinarith
      _ = _ := by
        rw [show U + b + 2 = (U + b) + (2 : ℝ) by ring,
          Real.rpow_add hLp, Real.rpow_add hLp, Real.rpow_two]
        field_simp
  have hbad : L ^ b * (A * W) ≤ c * X / L ^ U := by
    apply (le_div_iff₀ (Real.rpow_pos_of_pos hLp U)).2
    calc
      _ ≤ (L ^ b * (X ^ (2 / 3 : ℝ) * (c * L))) * L ^ U := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul hA hW hW0 (by positivity)
      _ = c * X ^ (2 / 3 : ℝ) * L ^ (U + b + 1) := by
        rw [Real.rpow_add hLp, Real.rpow_add hLp, Real.rpow_one]
        ring
      _ ≤ c * X ^ (2 / 3 : ℝ) * X ^ (1 / 3 : ℝ) :=
        mul_le_mul_of_nonneg_left hlog (by positivity)
      _ = c * X := by
        rw [mul_assoc, ← Real.rpow_add hX]
        norm_num
  calc
    _ ≤ L ^ b * ((K * X / L ^ (U + b + 2)) * (1 + L) + A * W) :=
      mul_le_mul_of_nonneg_right hR (by positivity)
    _ = L ^ b * ((K * X / L ^ (U + b + 2)) * (1 + L)) + L ^ b * (A * W) :=
      mul_add _ _ _
    _ ≤ 2 * K * X / L ^ U + c * X / L ^ U := add_le_add hmain hbad
    _ = _ := by ring

/-- All constants and the threshold precede N, m, A₂ and Q.  s=U+b+2.
The only limiting input is Mathlib's log-versus-positive-power little-o. -/
theorem exists_low_budget_payment (U b K : ℝ) (_hU : 0 < U) (_hb : 0 ≤ b)
    (hK : 0 < K) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ m A₂ Q : ℕ,
      1 ≤ m → (m : ℝ) ≤ Real.sqrt N → (A₂ : ℝ) ≤ (N : ℝ) ^ (2 / 3 : ℝ) →
      (Q : ℝ) ≤ Real.log (N : ℝ) ^ b →
      (Q : ℝ) * ((K * N / Real.log (N : ℝ) ^ (U + b + 2)) *
        (1 + Real.log N) + (A₂ : ℝ) * (m.primeFactors.card : ℝ)) ≤
        C * N / Real.log (N : ℝ) ^ U := by
  let c : ℝ := (Real.log 2)⁻¹
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨2 * K + c, by positivity, ?_⟩
  have hlim := (isLittleO_log_rpow_rpow_atTop (U + b + 1)
    (show (0 : ℝ) < 1 / 3 by norm_num)).bound (show (0 : ℝ) < 1 by norm_num)
  have hn := tendsto_natCast_atTop_atTop.eventually hlim
  have hl : ∀ᶠ N : ℕ in atTop, 1 ≤ Real.log (N : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop 1)
  apply eventually_atTop.mp
  filter_upwards [hn, hl, eventually_ge_atTop (3 : ℕ)] with N hlogs hL hN
  intro m A₂ Q hm hmN hA hQ
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog : Real.log (N : ℝ) ^ (U + b + 1) ≤ (N : ℝ) ^ (1 / 3 : ℝ) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by linarith :
      0 ≤ Real.log (N : ℝ)) _), abs_of_nonneg (Real.rpow_nonneg hNp.le _), one_mul]
      using hlogs
  have hmX : (m : ℝ) ≤ N := hmN.trans (by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_self_of_one_le (by exact_mod_cast (show 1 ≤ N by omega))
      (by norm_num))
  exact low_budget_scalar hNp hL (by positivity) (by positivity) (by positivity)
    hK.le hc.le hA (primeFactors_card_le_log_of_le (by omega) hmX) hQ hlog

end
end AnalyticNumberTheory.LargeSieve.PanLow