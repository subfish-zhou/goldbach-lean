import MathlibNt.SieveTheory.LiLiuGoldbachWeightTwelve

open Filter
open scoped Topology
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- Uniformly absorb a fixed polynomial loss into the analytic counting scale.
The threshold precedes the exponent alpha. -/
theorem goldbach_power_error_le_log_scale_eventually
    (C κ δ : ℝ) (hC : 0 ≤ C) (hκ : 0 < κ) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → ∀ α : ℝ, κ ≤ α →
      C * (N : ℝ) ^ (1 - α) ≤ δ * (N : ℝ) / (Real.log N) ^ 2 := by
  have ht : Tendsto (fun x : ℝ => C * (Real.log x) ^ 2 / x ^ κ) atTop (𝓝 0) := by
    have h := (_root_.isLittleO_log_rpow_rpow_atTop (2 : ℝ) hκ).tendsto_div_nhds_zero
    simpa only [Real.rpow_two, mul_zero, mul_div_assoc] using
      (tendsto_const_nhds (x := C)).mul h
  have hn := (ht.comp tendsto_natCast_atTop_atTop).eventually (gt_mem_nhds hδ)
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 hn
  refine ⟨max N₀ 2, le_max_right _ _, ?_⟩
  intro N hN α hα
  have hN2 : 2 ≤ N := (le_max_right _ _).trans hN
  have hbase : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hpos : (0 : ℝ) < N := by linarith
  have hlog : 0 < (Real.log N) ^ 2 := sq_pos_of_pos (Real.log_pos hbase)
  have hden : 0 < (N : ℝ) ^ κ := Real.rpow_pos_of_pos hpos _
  have hpα : 0 < (N : ℝ) ^ α := Real.rpow_pos_of_pos hpos _
  have hpow := Real.rpow_le_rpow_of_exponent_le hbase.le hα
  have hsmall : C * (Real.log N) ^ 2 / (N : ℝ) ^ κ < δ :=
    hN₀ N ((le_max_left _ _).trans hN)
  apply (le_div_iff₀ hlog).2
  calc
    C * (N : ℝ) ^ (1 - α) * (Real.log N) ^ 2 =
        (C * (Real.log N) ^ 2 / (N : ℝ) ^ α) * N := by
      rw [Real.rpow_sub hpos, Real.rpow_one]
      ring
    _ ≤ (C * (Real.log N) ^ 2 / (N : ℝ) ^ κ) * N := by
      apply mul_le_mul_of_nonneg_right _ hpos.le
      exact div_le_div_of_nonneg_left (mul_nonneg hC (sq_nonneg _)) hden hpow
    _ ≤ δ * N := mul_le_mul_of_nonneg_right hsmall.le hpos.le

/-- The actual switched twelve-term lower bound with arbitrary analytic-scale
loss. This does not assert positivity of the labelled main expression. -/
theorem goldbachWeight_twelve_switched_log_scale_eventually
    (ε δ : ℝ) (hε : 0 < ε) (hεu : ε < (2 : ℝ) / 15) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even N → ∀ α β γ : ℝ,
      (1 : ℝ) / 18 < α → α < β → β < (1 - 3 * β) / 3 →
      (1 - 3 * β) / 3 < γ → γ < (1 : ℝ) / 3 →
      (goldbachWeightTwelveSwitchedRHS (goldbachDifferenceCarrier N ε) N ε
        ((N : ℝ) ^ α) ((N : ℝ) ^ β) ((N : ℝ) ^ γ)
        ((N : ℝ) ^ ((9 : ℝ) / 19 - ε)) : ℝ) -
        δ * (N : ℝ) / (Real.log N) ^ 2 ≤ 4 * (D19 N : ℝ) := by
  obtain ⟨Ns, hs⟩ := goldbachWeight_twelve_switched_lower_bound_eventually ε hε hεu
  obtain ⟨Ne, _, he⟩ := goldbach_power_error_le_log_scale_eventually
    2214 ((1 : ℝ) / 18) δ (by norm_num) (by norm_num) hδ
  refine ⟨max Ns Ne, ?_⟩
  intro N hN hEven α β γ hα hαβ hβγ hγ hγu
  have hmain := hs N ((le_max_left _ _).trans hN) hEven α β γ hα hαβ hβγ hγ hγu
  have herror := he N ((le_max_right _ _).trans hN) α hα.le
  linarith

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig