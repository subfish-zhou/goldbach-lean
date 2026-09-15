import MathlibNt.SieveTheory.LiLiuGoldbachG10SwitchFinite
import MathlibNt.SieveTheory.LiLiuGoldbachBadBound

open Filter
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- Payment for the actual additional bad and square masses of the candidate switch. -/
theorem goldbachG10SwitchErrors_le_880 (N : ℕ) (ε β : ℝ)
    (hε : 0 < ε) (hN : 1 ≤ N) (hβ : β ≤ (1 : ℝ) / 2)
    (hz : 2 ≤ (N : ℝ) ^ β) :
    ((400 * goldbachBadCount (goldbachDifferenceCarrier N ε) N +
      40 * goldbachQA (goldbachDifferenceCarrier N ε) N ((N : ℝ) ^ β) : ℤ) : ℝ) ≤
      880 * (N : ℝ) ^ (1 - β) := by
  have hbase : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hz0 : 0 < (N : ℝ) ^ β := Real.rpow_pos_of_pos hN0 _
  have hzN : ((N : ℝ) ^ β) ^ 2 ≤ (N : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ N)]
    calc
      (N : ℝ) ^ (β * (2 : ℕ)) ≤ (N : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hbase (by norm_num; linarith)
      _ = N := Real.rpow_one _
  have hX := goldbachBadCount_twice_le_four_div N ε ((N : ℝ) ^ β) hN hz0 hzN
  have hA : ∀ n ∈ goldbachDifferenceCarrier N ε, 1 ≤ n ∧ n < N := by
    intro n hn
    have hb := goldbachG10DifferenceCarrier_bounds hε hn
    exact ⟨hb.1, hb.2.1⟩
  have hQ := goldbachQA_real_le_two_mul_div (goldbachDifferenceCarrier N ε) N
    ((N : ℝ) ^ β) hA hz
  calc
    ((400 * goldbachBadCount (goldbachDifferenceCarrier N ε) N +
      40 * goldbachQA (goldbachDifferenceCarrier N ε) N ((N : ℝ) ^ β) : ℤ) : ℝ)
        ≤ 200 * (4 * (N : ℝ) / ((N : ℝ) ^ β)) +
          40 * (2 * (N : ℝ) / ((N : ℝ) ^ β)) := by
            push_cast at hX ⊢
            linarith
    _ = 880 * (N : ℝ) ^ (1 - β) := by
      rw [Real.rpow_sub hN0, Real.rpow_one]
      ring

/-- A parameter-uniform paid upper bound for the separately named candidate G10.
This does not assert an analytic upper bound for the labelled prime source. -/
theorem goldbachG10Corrected_eventually_le_pi10_add_880 (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ β γ : ℝ,
      (1 : ℝ) / 18 < β → β < (1 - 3 * β) / 3 →
      (1 - 3 * β) / 3 < γ → γ < (1 : ℝ) / 3 →
      (goldbachG10Corrected (goldbachDifferenceCarrier N ε) N
        ((N : ℝ) ^ β) ((N : ℝ) ^ γ) : ℝ) ≤
        (goldbachPi10 N ε ((N : ℝ) ^ β) ((N : ℝ) ^ γ) : ℝ) +
          880 * (N : ℝ) ^ (1 - β) := by
  obtain ⟨Ng, hg⟩ := goldbachG10Corrected_actual_eventually_le_pi10_with_errors ε hε
  have hpowers : ∀ᶠ N : ℕ in atTop, 2 ≤ (N : ℝ) ^ ((1 : ℝ) / 21) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 21)).comp
      tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 2)
  apply Filter.Eventually.exists_forall_of_atTop
  filter_upwards [eventually_ge_atTop Ng, eventually_ge_atTop (1 : ℕ), hpowers]
    with N hNg hN hpow
  intro β γ hβ hβγ hγ hγtop
  have hbase : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hz : 2 ≤ (N : ℝ) ^ β :=
    hpow.trans (Real.rpow_le_rpow_of_exponent_le hbase (by linarith : (1 : ℝ) / 21 ≤ β))
  have herr := goldbachG10SwitchErrors_le_880 N ε β hε hN (by linarith) hz
  have hmain := (Int.cast_le (R := ℝ)).mpr (hg N hNg β γ hβ hβγ hγ hγtop)
  push_cast at herr hmain ⊢
  linarith

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig