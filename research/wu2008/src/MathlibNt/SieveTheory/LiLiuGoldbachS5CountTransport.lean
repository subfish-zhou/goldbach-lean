import MathlibNt.SieveTheory.LiLiuGoldbachB9C10Bridge
import MathlibNt.SieveTheory.LiLiuGoldbachS5SquareMass

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- A union of square-divisibility fibres is at most their actual QA mass.
The ambient carrier is all positive integers below N, not the prime difference set. -/
theorem goldbachS5SquareCount_le_QA (N : ℕ) :
    goldbachS5SquareCount N ≤
      goldbachQA ((Finset.range N).filter fun n => 0 < n) N ((N : ℝ)^(4 / 53 : ℝ)) := by
  classical
  let A := (Finset.range N).filter fun n => 0 < n
  let S := goldbachSquarePrimes N ((N : ℝ)^(4 / 53 : ℝ))
  have hsub : goldbachS5SquareSet N ⊆ S.biUnion (fun r => A.filter fun n => r^2 ∣ n) := by
    intro n hn
    obtain ⟨hn0, hnN, r, hr, hrlow, hrd⟩ := mem_goldbachS5SquareSet_iff.mp hn
    apply Finset.mem_biUnion.mpr
    refine ⟨r, mem_goldbachSquarePrimes_iff.mpr
      ⟨hr, hrlow, (Nat.le_of_dvd hn0 hrd).trans hnN.le⟩, ?_⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hnN, hn0⟩, hrd⟩
  have hc : (goldbachS5SquareSet N).card ≤ ∑ r ∈ S, (A.filter fun n => r^2 ∣ n).card :=
    (Finset.card_le_card hsub).trans (Finset.card_biUnion_le)
  have hcast := (Int.ofNat_le.mpr hc)
  simpa [goldbachS5SquareCount, goldbachQA, A, S] using hcast

theorem goldbachS5SquareCount_normalized (δ : ℝ) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      400 * (goldbachS5SquareCount N : ℝ) ≤
        δ * (SingularSeries.liuSingularSeries N * (N : ℝ) / Real.log (N : ℝ)^2) := by
  obtain ⟨N₀, hN₀, hmass⟩ := goldbachS5_squareMass_normalized δ hδ
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN
  have hqa := hmass N hN ((Finset.range N).filter fun n => 0 < n) (by
    intro n hn
    obtain ⟨hr, hp⟩ := Finset.mem_filter.mp hn
    exact ⟨hp, Finset.mem_range.mp hr⟩)
  have hc : (goldbachS5SquareCount N : ℝ) ≤
      (goldbachQA ((Finset.range N).filter fun n => 0 < n) N ((N : ℝ)^(4 / 53 : ℝ)) : ℝ) := by
    exact_mod_cast goldbachS5SquareCount_le_QA N
  exact (mul_le_mul_of_nonneg_left hc (by norm_num : (0 : ℝ) ≤ 400)).trans hqa


end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig