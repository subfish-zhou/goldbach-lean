import MathlibNt.SieveTheory.LinearSieve.JurkatRichert.JurkatRichert1965ChenRichertConsumer
import MathlibNt.SieveTheory.Selberg.Liu.LiuSelbergCorrectedChenBridge

/-!
# Chen's 1+2 endpoint after the verified sieve and distribution inputs

The Jurkat--Richert weighted lower bound already pays the valuation-weighted
prime-power penalty. Only the genuine triple upper bound remains conditional.
The Liu--Pan specialization below uses the existing Selberg-square-to-triple
producer, including its endpoint and paper-modulus corrections.

These are conditional Chen theorems, not unconditional analytic producers.
The quantitative statement counts the existing `chenGoodRepresentations`;
neither the historical counting bridge nor a weakened counting object is used.
-/

open Filter
open scoped Topology

namespace MathlibNt.SieveTheory.ChenVerifiedPrerequisites

open SwitchingPrinciple LiuWeight

/-- The original public representation count has coefficient `0.67`, conditional
only on the actual triple penalty estimate. All sieve and BV inputs are internal. -/
theorem chen_good_representations_lower_bound_of_triple_penalty
    (hTriple : ChenJurkatRichertTriplePenaltyUpperBound) :
    ∀ᶠ N : ℕ in atTop, Even N →
      (0.67 : ℝ) * SingularSeries.liuSingularSeries N * (N : ℝ) /
          Real.log N ^ (2 : ℕ) ≤
        ((chenGoodRepresentations N).card : ℝ) := by
  obtain ⟨C, _, hTripleEvent⟩ := hTriple
  have hJR := JurkatRichert1965ChenRichertConsumer.chenWeightedLowerBound
    (1 / 10000 : ℝ) (by norm_num)
  have hrem := eventually_inverse_log_remainder_le_liuSingularSeries
    C (1 / 10000 : ℝ) (by norm_num)
  filter_upwards [hJR, hTripleEvent, hrem, eventually_ge_atTop 9] with
    N hJRN hTN hremN hN
  intro hEven
  have hscale :
      0 ≤ SingularSeries.liuSingularSeries N * (N : ℝ) /
        Real.log N ^ (2 : ℕ) :=
    div_nonneg
      (mul_nonneg (SingularSeries.liuSingularSeries_pos N).le (Nat.cast_nonneg N))
      (sq_nonneg _)
  have hbridge := corrected_counting_bridge_public_of_nine_le hN
  rw [correctedChenKeyCount_eq_jurkatRichertWeightedCount_sub_triple] at hbridge
  have hj := hJRN hEven
  have ht := hTN hEven
  simp only [mul_div_assoc, mul_assoc] at hj ht hremN hscale ⊢
  nlinarith only [hj, ht, hremN, hbridge, hscale]

/-- The canonical switched-source theorem supplies the sole remaining triple
estimate, preserving the full public `0.67` count. -/
theorem chen_good_representations_lower_bound_of_liu_coprime
    (hLiu : LiuPanCanonicalCoprimeTheorem) :
    ∀ᶠ N : ℕ in atTop, Even N →
      (0.67 : ℝ) * SingularSeries.liuSingularSeries N * (N : ℝ) /
          Real.log N ^ (2 : ℕ) ≤
        ((chenGoodRepresentations N).card : ℝ) :=
  chen_good_representations_lower_bound_of_triple_penalty
    (liu_pan_wang_ding_strictTriple_upper hLiu)

/-- A positive actual representation count supplies the unconditional-shape
existence statement without repeating the sieve error-budget endgame. -/
theorem chens_theorem_of_liu_coprime
    (hLiu : LiuPanCanonicalCoprimeTheorem) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even N →
      ∃ p q : ℕ, p.Prime ∧ ChensTheorem.Semiprime q ∧ N = p + q := by
  obtain ⟨N₀, hcount⟩ := eventually_atTop.mp (chen_good_representations_lower_bound_of_liu_coprime hLiu)
  refine ⟨max N₀ 9, ?_⟩
  intro N hN hEven
  have hN₀ : N₀ ≤ N := le_trans (le_max_left _ _) hN
  have hN9 : 9 ≤ N := le_trans (le_max_right _ _) hN
  have hlog : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hmain : 0 < (0.67 : ℝ) *
      MathlibNt.SieveTheory.SingularSeries.liuSingularSeries N * (N : ℝ) /
        Real.log N ^ (2 : ℕ) := by
    exact div_pos
      (mul_pos (mul_pos (by norm_num)
        (MathlibNt.SieveTheory.SingularSeries.liuSingularSeries_pos N))
        (by exact_mod_cast (show 0 < N by omega)))
      (pow_pos hlog 2)
  have hcard : 0 < (chenGoodRepresentations N).card := by
    exact_mod_cast hmain.trans_le (hcount N hN₀ hEven)
  obtain ⟨p, hp⟩ := Finset.card_pos.mp hcard
  simp only [chenGoodRepresentations, Finset.mem_filter, Finset.mem_range] at hp
  exact ⟨p, N - p, hp.2.1,
    ⟨hp.2.2.1, hp.2.2.2⟩, by omega⟩


end MathlibNt.SieveTheory.ChenVerifiedPrerequisites
