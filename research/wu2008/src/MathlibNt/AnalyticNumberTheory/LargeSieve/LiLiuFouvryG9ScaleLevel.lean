import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuFouvryG9Scale

noncomputable section
open Filter

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

/-- Numerical level conversion, not a transport theorem for well-factorability. -/
theorem g9Scale_level_identity (x T ν ε : ℝ) (hx : 0 < x) (hT : T = x ^ ν) :
    x ^ ((5 - 5 * ν) / 9 - ε) = x ^ (5 / 9 - ε) / T ^ (5 / 9 : ℝ) := by
  rw [show (5 - 5 * ν) / 9 - ε = (5 / 9 - ε) - ν * (5 / 9) by ring,
    Real.rpow_sub hx, Real.rpow_mul hx.le, ← hT]

/-- The positive gap `δ - ε` absorbs the fixed scale distortion `K^(5/9-ε)`.
The threshold is independent of the local scale `x`. -/
theorem g9Scale_eventually_level_numerator (K ε δ : ℝ) (hK : 1 ≤ K)
    (hε : ε ≤ (5 / 9 : ℝ)) (hδε : ε < δ) :
    ∀ᶠ N : ℝ in atTop, ∀ x : ℝ, N / K ≤ x →
      N ^ (5 / 9 - δ) ≤ x ^ (5 / 9 - ε) := by
  have hK0 : 0 < K := lt_of_lt_of_le zero_lt_one hK
  filter_upwards [g9Scale_eventually_const_mul_rpow_le (K ^ (5 / 9 - ε))
    (5 / 9 - δ) (5 / 9 - ε) (by linarith),
    eventually_gt_atTop (0 : ℝ)] with N hpay hN
  intro x hNx
  have hx0 : 0 < x := (div_pos hN hK0).trans_le hNx
  have hNKx : N ≤ K * x := by
    simpa [mul_comm] using (div_le_iff₀ hK0).mp hNx
  have hcomp := Real.rpow_le_rpow hN.le hNKx (sub_nonneg.mpr hε)
  rw [Real.mul_rpow hK0.le hx0.le] at hcomp
  exact le_of_mul_le_mul_left (hpay.trans hcomp) (Real.rpow_pos_of_pos hK0 _)

/-- Full uniform scale bridge with the optional genuine numerical level comparison.
Only fixed parameter restrictions and the original rectangle bounds are inputs. -/
theorem g9Scale_eventually_local_global_and_level (K ε α δ : ℝ) (hK : 1 ≤ K)
    (hε : 0 < ε) (hεα : ε < α) (hα : α ≤ (1 / 10 : ℝ)) (hδε : ε < δ) :
    ∀ᶠ N : ℝ in atTop, ∀ x T : ℝ,
      N / K ≤ x → x ≤ 4 * N → N ^ α / 2 ≤ T → T ≤ N ^ (1 / 10 : ℝ) →
      let ν := Real.log T / Real.log x
      1 < x ∧ 1 ≤ T ∧ T = x ^ ν ∧ ε ≤ ν ∧
        ν ≤ 1 / 10 + ε / 10 ∧ N ≤ K * x ∧
        N ^ (5 / 9 - δ) / T ^ (5 / 9 : ℝ) ≤ x ^ ((5 - 5 * ν) / 9 - ε) := by
  filter_upwards [g9Scale_eventually_local_global K ε α hK hε hεα hα,
    g9Scale_eventually_level_numerator K ε δ hK (by linarith) hδε] with N hscale hlevel
  intro x T hNx hxN hNT hTN
  obtain ⟨hx, hT, hid, hlo, hhi, hNKx⟩ := hscale x T hNx hxN hNT hTN
  refine ⟨hx, hT, hid, hlo, hhi, hNKx, ?_⟩
  rw [g9Scale_level_identity x T _ ε (zero_lt_one.trans hx) hid]
  exact div_le_div_of_nonneg_right (hlevel x hNx)
    (Real.rpow_nonneg (zero_le_one.trans hT) _)

/-- Explicit quantifier-order interface: one cutoff works for every local block. -/
theorem g9Scale_exists_threshold_local_global_and_level (K ε α δ : ℝ) (hK : 1 ≤ K)
    (hε : 0 < ε) (hεα : ε < α) (hα : α ≤ (1 / 10 : ℝ)) (hδε : ε < δ) :
    ∃ N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N → ∀ x T : ℝ,
      N / K ≤ x → x ≤ 4 * N → N ^ α / 2 ≤ T → T ≤ N ^ (1 / 10 : ℝ) →
      let ν := Real.log T / Real.log x
      1 < x ∧ 1 ≤ T ∧ T = x ^ ν ∧ ε ≤ ν ∧
        ν ≤ 1 / 10 + ε / 10 ∧ N ≤ K * x ∧
        N ^ (5 / 9 - δ) / T ^ (5 / 9 : ℝ) ≤ x ^ ((5 - 5 * ν) / 9 - ε) :=
  eventually_atTop.mp (g9Scale_eventually_local_global_and_level K ε α δ hK hε hεα hα hδε)

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
