import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

noncomputable section
open Filter

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

/-- A fixed coefficient is absorbed by a strictly positive exponent gap. -/
theorem g9Scale_eventually_const_mul_rpow_le (C p q : ℝ) (hpq : p < q) :
    ∀ᶠ N : ℝ in atTop, C * N ^ p ≤ N ^ q := by
  filter_upwards [(tendsto_rpow_atTop (sub_pos.mpr hpq)).eventually
    (eventually_ge_atTop C), eventually_gt_atTop (0 : ℝ)] with N hC hN
  calc
    C * N ^ p ≤ N ^ (q - p) * N ^ p :=
      mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hN.le p)
    _ = N ^ q := by rw [← Real.rpow_add hN]; congr 1; ring

/-- The lower and upper power endpoints are admitted at one global threshold. -/
theorem g9Scale_eventually_power_endpoints (K ε α : ℝ) (hK : 1 ≤ K)
    (hε : 0 < ε) (hεα : ε < α) :
    ∀ᶠ N : ℝ in atTop,
      (4 * N) ^ ε ≤ N ^ α / 2 ∧
      N ^ (1 / 10 : ℝ) ≤ (N / K) ^ (1 / 10 + ε / 10 : ℝ) := by
  have hK0 : 0 < K := lt_of_lt_of_le zero_lt_one hK
  filter_upwards [g9Scale_eventually_const_mul_rpow_le (2 * (4 : ℝ) ^ ε) ε α hεα,
    g9Scale_eventually_const_mul_rpow_le (K ^ (1 / 10 + ε / 10 : ℝ))
      (1 / 10) (1 / 10 + ε / 10) (by linarith),
    eventually_gt_atTop (0 : ℝ)] with N hlo hhi hN
  constructor
  · rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) hN.le]
    linarith
  · rw [Real.div_rpow hN.le hK0.le]
    apply (le_div_iff₀ (Real.rpow_pos_of_pos hK0 _)).mpr
    simpa [mul_comm] using hhi

/-- Uniform local/global scale bridge. The cutoff precedes both moving parameters.
No conclusion about well-factorability or a curved summation region is asserted. -/
theorem g9Scale_eventually_local_global (K ε α : ℝ) (hK : 1 ≤ K)
    (hε : 0 < ε) (hεα : ε < α) (_hα : α ≤ (1 / 10 : ℝ)) :
    ∀ᶠ N : ℝ in atTop, ∀ x T : ℝ,
      N / K ≤ x → x ≤ 4 * N → N ^ α / 2 ≤ T → T ≤ N ^ (1 / 10 : ℝ) →
      let ν := Real.log T / Real.log x
      1 < x ∧ 1 ≤ T ∧ T = x ^ ν ∧ ε ≤ ν ∧
        ν ≤ 1 / 10 + ε / 10 ∧ N ≤ K * x := by
  have hK0 : 0 < K := lt_of_lt_of_le zero_lt_one hK
  filter_upwards [g9Scale_eventually_power_endpoints K ε α hK hε hεα,
    eventually_gt_atTop K] with N hpow hNK
  intro x T hNx hxN hNT hTN
  have hN : 0 < N := hK0.trans hNK
  have hx : 1 < x := by
    have : 1 < N / K := (lt_div_iff₀ hK0).mpr (by simpa using hNK)
    exact this.trans_le hNx
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hlo : x ^ ε ≤ T :=
    (Real.rpow_le_rpow hx0.le hxN hε.le).trans (hpow.1.trans hNT)
  have hT : 1 ≤ T := (Real.one_le_rpow hx.le hε.le).trans hlo
  have hT0 : 0 < T := zero_lt_one.trans_le hT
  have hid : T = x ^ (Real.log T / Real.log x) := by
    rw [Real.rpow_def_of_pos hx0]
    have hlog : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx)
    rw [mul_div_cancel₀ _ hlog, Real.exp_log hT0]
  have hhi : T ≤ x ^ (1 / 10 + ε / 10 : ℝ) :=
    hTN.trans (hpow.2.trans (Real.rpow_le_rpow (div_pos hN hK0).le hNx
      (by linarith)))
  refine ⟨hx, hT, hid, ?_, ?_, ?_⟩
  · exact (Real.rpow_le_rpow_left_iff hx).mp (by simpa only [← hid] using hlo)
  · exact (Real.rpow_le_rpow_left_iff hx).mp (by simpa only [← hid] using hhi)
  · have := (div_le_iff₀ hK0).mp hNx
    simpa [mul_comm] using this

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
