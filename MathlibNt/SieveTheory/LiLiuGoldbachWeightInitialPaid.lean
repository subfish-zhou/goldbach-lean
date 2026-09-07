import MathlibNt.SieveTheory.LiLiuGoldbachWeightInitialBudget
import MathlibNt.SieveTheory.LiLiuGoldbachTwoBasic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

open Filter
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- The paid first weight refinement on the actual prime-difference carrier.
One epsilon-dependent threshold precedes all three exponent parameters.
This is not the full twelve-term inequality or positivity of D19. -/
theorem goldbachWeight_initial_paid_eventually (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ α β γ : ℝ,
      (1 : ℝ) / 21 < α → α ≤ β → β ≤ γ →
      (goldbachS1 (goldbachDifferenceCarrier N ε) N ((N : ℝ) ^ β) : ℝ) -
        goldbachS3Closed (goldbachDifferenceCarrier N ε) N ((N : ℝ) ^ β) ((N : ℝ) ^ γ) ≥
      (goldbachS1 (goldbachDifferenceCarrier N ε) N ((N : ℝ) ^ α) : ℝ) -
        goldbachS3Closed (goldbachDifferenceCarrier N ε) N ((N : ℝ) ^ α) ((N : ℝ) ^ γ) +
        goldbachWeightG6 (goldbachDifferenceCarrier N ε) N ((N : ℝ) ^ α) ((N : ℝ) ^ β) +
        goldbachWeightG7 (goldbachDifferenceCarrier N ε) N ((N : ℝ) ^ α) ((N : ℝ) ^ β) ((N : ℝ) ^ γ) -
        goldbachWeightG14 (goldbachDifferenceCarrier N ε) N ((N : ℝ) ^ α) ((N : ℝ) ^ β) -
        goldbachWeightG15 (goldbachDifferenceCarrier N ε) N ((N : ℝ) ^ α) ((N : ℝ) ^ β) ((N : ℝ) ^ γ) -
        42 * (N : ℝ) ^ (1 - α) := by
  obtain ⟨Ng, hg⟩ := exists_goldbachBasic_growth_cutoff ε hε
  have hpowers : ∀ᶠ N : ℕ in atTop, 2 ≤ (N : ℝ) ^ ((1 : ℝ) / 21) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 21)).comp
      tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 2)
  apply Filter.Eventually.exists_forall_of_atTop
  filter_upwards [eventually_ge_atTop Ng, eventually_ge_atTop (1 : ℕ), hpowers]
    with N hNg hN hpow
  intro α β γ hα hαβ hβγ
  have hbase : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hz : 2 ≤ (N : ℝ) ^ α :=
    hpow.trans (Real.rpow_le_rpow_of_exponent_le hbase hα.le)
  have hzb : (N : ℝ) ^ α ≤ (N : ℝ) ^ β :=
    Real.rpow_le_rpow_of_exponent_le hbase hαβ
  have hbc : (N : ℝ) ^ β ≤ (N : ℝ) ^ γ :=
    Real.rpow_le_rpow_of_exponent_le hbase hβγ
  have hA : ∀ n ∈ goldbachDifferenceCarrier N ε, 1 ≤ n ∧ n < N := by
    intro n hn
    have hb := goldbachDifferenceCarrier_bounds (hg N hNg).1 hn
    exact ⟨by omega, hb.2⟩
  have hpaid := goldbachWeight_initial_paid_real (goldbachDifferenceCarrier N ε) N
    hN hA hα rfl hz hzb hbc
  have hpayment : 42 * (N : ℝ) / (N : ℝ) ^ α = 42 * (N : ℝ) ^ (1 - α) := by
    rw [Real.rpow_sub hN0, Real.rpow_one]
    ring
  simpa only [hpayment] using hpaid

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig