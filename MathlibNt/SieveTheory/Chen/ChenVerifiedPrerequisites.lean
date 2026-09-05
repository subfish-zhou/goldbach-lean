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

/-- The existing prime-plus-at-most-two-primes endpoint with only the triple
upper bound explicit; the verified Richert certificate supplies the lower bound. -/
theorem chens_theorem_of_triple_penalty
    (hTriple : ChenJurkatRichertTriplePenaltyUpperBound) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even N →
      ∃ p q : ℕ, p.Prime ∧ ChensTheorem.Semiprime q ∧ N = p + q := by
  obtain ⟨N₀, hchen⟩ :=
    chensTheorem_of_jurkatRichertWeightedLowerBound_and_triplePenalty
      JurkatRichert1965ChenRichertConsumer.chenFacingSourceChainCertificate.weightedLowerBound
      hTriple
  refine ⟨N₀, ?_⟩
  intro N hN hEven
  obtain ⟨p, q, hp, hq, hP₂, hsum⟩ := hchen N hN hEven
  exact ⟨p, q, hp, ⟨hq, hP₂⟩, hsum⟩

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

/-- The actual existing public Chen assembly with every sieve and BV premise
discharged. The canonical Liu switched-source bound is still an explicit input. -/
theorem chens_theorem_of_liu_coprime
    (hLiu : LiuPanCanonicalCoprimeTheorem) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even N →
      ∃ p q : ℕ, p.Prime ∧ ChensTheorem.Semiprime q ∧ N = p + q :=
  ChensTheorem.chens_theorem_of_jurkat_richert_weighted_lower_bound
    JurkatRichert1965ChenRichertConsumer.chenFacingSourceChainCertificate.weightedLowerBound
    hLiu

/-- The existing source-interval and logarithmic-integral normalization
transport connects Corollary (2.30) without any new analytic assumption. -/
theorem chens_theorem_of_corollary230
    (hPan : LiuPanWangDingCorollary230) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even N →
      ∃ p q : ℕ, p.Prime ∧ ChensTheorem.Semiprime q ∧ N = p + q :=
  chens_theorem_of_liu_coprime hPan.to_canonicalCoprimeTheorem

end MathlibNt.SieveTheory.ChenVerifiedPrerequisites
