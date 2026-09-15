import WRefinedLossRecovered
import MathlibNt.Wu2008DoubleSieve.Counting
import MathlibNt.Wu2008DoubleSieve.TruncatedSixthMassRectangle
import MathlibNt.Wu2008DoubleSieve.SharpLogRecurrence

noncomputable section

namespace Wu18938Campaign.M3.Confirmed

open Real Wu2008DoubleSieve Wu2004MeanValue
open MathlibNt.Wu2008DoubleSieve
open MathlibNt.SieveTheory.SwitchingPrinciple

theorem refinement_loss_rational :
    (112 / 125 : ℝ) < 8 * log (500 / 447) ∧
      8 * log (500 / 447) < (2241 / 2500 : ℝ) := by
  have hl := SharpLogRecurrence.log_lower (by norm_num : (1 : ℝ) ≤ 500 / 447)
  have hu := SharpLogRecurrence.log_upper (by norm_num : (1 : ℝ) ≤ 500 / 447)
  norm_num [SharpLogRecurrence.lowerLog, SharpLogRecurrence.upperLog] at hl hu
  constructor <;> linarith

theorem actual_refinement_loss_1894 {ε : ℝ} (heps : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ((wuPrimeComplements N).card : ℝ) -
        (8 * log (500 / 447) + ε) * truncatedSixthMassScale N ≤
          ((refinedGood N (947 / 500)).card : ℝ) := by
  classical
  obtain ⟨T, hT⟩ := refinedGood_card_lower_add_unit
    (947 / 500) ε (by norm_num) (by norm_num) heps
  refine ⟨max 4 T, le_max_left _ _, fun N hN he => ?_⟩
  have h := hT N ((le_max_right _ _).trans hN) he
  have hunit : ((wuPrimeComplements N).card : ℝ) =
      (chenGoodRepresentations N).card + (if (N - 1).Prime then (1 : ℝ) else 0) := by
    rw [wuPrimeComplements_card_eq_release]
    split_ifs <;> push_cast <;> ring
  rw [hunit, truncatedSixthMassScale,
    wuSingularSeries_eq_liu N (by omega)]
  norm_num only [show (1 : ℝ) / (947 / 500 - 1) = 500 / 447 by norm_num] at h
  convert h using 1
  ring

theorem refined_1894_from_ordinary_count
    (hcount : ∀ ε : ℝ, 0 < ε →
      ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
        ((899 / 1000 : ℝ) - ε) * truncatedSixthMassScale N ≤
          ((wuPrimeComplements N).card : ℝ)) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      truncatedSixthMassScale N / 400 <
        ((refinedGood N (947 / 500)).card : ℝ) ∧
      ∃ p r q : ℕ, p.Prime ∧ (r = 1 ∨ r.Prime) ∧ q.Prime ∧
        N = p + r * q ∧ (r : ℝ) ≤ (q : ℝ) ^ (447 / 500 : ℝ) := by
  obtain ⟨Tc, hTc, hc⟩ := hcount (1 / 40000) (by norm_num)
  obtain ⟨Tl, _, hl⟩ := actual_refinement_loss_1894
    (ε := 1 / 40000) (by norm_num)
  refine ⟨max Tc Tl, hTc.trans (le_max_left _ _), fun N hN he => ?_⟩
  have hN4 := hTc.trans ((le_max_left _ _).trans hN)
  have hN0 : 0 < N := by omega
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hscale : 0 < truncatedSixthMassScale N := by
    unfold truncatedSixthMassScale
    exact div_pos (mul_pos (wuSingularSeries_pos N hN0)
      (by exact_mod_cast hN0)) (sq_pos_of_pos (log_pos hNr))
  have hcN := hc N ((le_max_left _ _).trans hN) he
  have hlN := hl N ((le_max_right _ _).trans hN) he
  have hpaid := mul_lt_mul_of_pos_right refinement_loss_rational.2 hscale
  have hgood : truncatedSixthMassScale N / 400 <
      ((refinedGood N (947 / 500)).card : ℝ) := by
    nlinarith only [hcN, hlN, hpaid, hscale]
  refine ⟨hgood, ?_⟩
  have hpos : 0 < ((refinedGood N (947 / 500)).card : ℝ) :=
    (div_pos hscale (by norm_num)).trans hgood
  have hn : 0 < (refinedGood N (947 / 500)).card := by exact_mod_cast hpos
  obtain ⟨p, hp⟩ := Finset.card_pos.mp hn
  obtain ⟨hpp, r, q, hq, hr, hN', hsize⟩ := mem_refinedGood.mp hp
  refine ⟨p, r, q, hpp, hr, hq, hN', ?_⟩
  convert hsize using 1
  norm_num

end Wu18938Campaign.M3.Confirmed
