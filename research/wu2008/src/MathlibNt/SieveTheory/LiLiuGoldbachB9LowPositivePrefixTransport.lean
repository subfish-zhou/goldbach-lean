import MathlibNt.SieveTheory.LiLiuGoldbachB9LowPositivePrefixFinite
import MathlibNt.SieveTheory.LiLiuGoldbachS5CountTransport

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- All finite losses are internal; the threshold is chosen before the sieve cutoff. -/
theorem goldbachS5ClosedBelow_le_positivePrefix_sifted_normalized_of_pos (eps delta : ℝ)
    (heps : 0 < eps) (hdelta : 0 < delta) :
    ∃ N0 : ℕ, 4 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → ∀ Z : ℝ,
      1 ≤ Z → Z ≤ Real.sqrt (N : ℝ) →
      (goldbachS5ClosedBelow (goldbachDifferenceCarrier N eps) N
        ((N : ℝ) ^ (4 / 53 : ℝ)) ((N : ℝ) ^ (1 / 3 : ℝ))
        ((N : ℝ) ^ (1 / 10 : ℝ)) : ℝ) ≤
        (goldbachB9LowPositivePrefixSiftedCount N eps Z : ℝ) +
        delta * (SingularSeries.liuSingularSeries N * (N : ℝ) / Real.log (N : ℝ) ^ 2) := by
  obtain ⟨Ns, hNs, hs⟩ := exists_goldbachS4_switch_threshold eps heps
  obtain ⟨Nb, hNb, hb⟩ := goldbachS4_finiteLoss_normalized (delta / 2) (by positivity)
  obtain ⟨Nq, _hNq, hq⟩ := goldbachS5SquareCount_normalized (delta / 2) (by positivity)
  refine ⟨max Ns (max Nb Nq), (hNb.trans (le_max_left _ _)).trans (le_max_right _ _), ?_⟩
  intro N hN Z hZ hZu
  have hsN : Ns ≤ N := (le_max_left _ _).trans hN
  have hbN : Nb ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hqN : Nq ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  have hfinite := goldbachS5ClosedBelow_le_positivePrefix_sifted
    (hNs.trans hsN) heps (hs N hsN) hZ
  have hreal :
      (goldbachS5ClosedBelow (goldbachDifferenceCarrier N eps) N
        ((N : ℝ) ^ (4 / 53 : ℝ)) ((N : ℝ) ^ (1 / 3 : ℝ))
        ((N : ℝ) ^ (1 / 10 : ℝ)) : ℝ) ≤
        (goldbachB9LowPositivePrefixSiftedCount N eps Z : ℝ) +
        400 * (goldbachBadCount (goldbachDifferenceCarrier N eps) N : ℝ) +
        400 * (goldbachS5SquareCount N : ℝ) + 400 * (Nat.floor Z : ℝ) := by
    exact_mod_cast hfinite
  have hbad := hb N hbN eps Z (by linarith) hZu
  have hsquare := hq N hqN
  linarith

theorem goldbachS5ClosedBelow_le_positivePrefix_sifted_normalized
    (delta : ℝ) (hdelta : 0 < delta) (eps : ℝ)
    (heps : 0 < eps ∧ eps < (2 : ℝ) / 15) :
    ∃ N0 : ℕ, 4 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → ∀ Z : ℝ,
      1 ≤ Z → Z ≤ Real.sqrt (N : ℝ) →
      (goldbachS5ClosedBelow (goldbachDifferenceCarrier N eps) N
        ((N : ℝ) ^ (4 / 53 : ℝ)) ((N : ℝ) ^ (1 / 3 : ℝ))
        ((N : ℝ) ^ (1 / 10 : ℝ)) : ℝ) ≤
        (goldbachB9LowPositivePrefixSiftedCount N eps Z : ℝ) +
        delta * (SingularSeries.liuSingularSeries N * (N : ℝ) / Real.log (N : ℝ) ^ 2) :=
  goldbachS5ClosedBelow_le_positivePrefix_sifted_normalized_of_pos eps delta heps.1 hdelta

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig