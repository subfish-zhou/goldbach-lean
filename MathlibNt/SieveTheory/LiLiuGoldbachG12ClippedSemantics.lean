import MathlibNt.SieveTheory.LiLiuGoldbachG12ClippedConsumers

noncomputable section
open Classical Finset
open scoped BigOperators
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
open Wu2004MeanValue AnalyticNumberTheory.Sieve AnalyticNumberTheory.LargeSieve
namespace G12ClippedWindow


/-- Empty normalization changes no prime atoms: the clamp is the literal intersection. -/
theorem clamp_window_eq_filter (N m : ℕ) (ε : ℝ) (T V : ℕ → ℝ) :
    window N (clampLower N ε T V) (clampUpper N ε V) m =
      (goldbachG11LinkedPrimeWindow N ε m).filter
        (fun r : ℕ => T m < (r : ℝ) ∧ (r : ℝ) ≤ V m) := by
  ext r
  simp only [window, goldbachG11LinkedPrimeWindow, mem_filter]
  constructor
  · rintro ⟨hr,hp,hl,hu⟩
    have hlold : goldbachG11PiLiLo N ε m < r :=
      (le_min (le_max_left _ _) (le_max_left _ _)).trans_lt hl
    have hmin : (r : ℝ) ≤ min (goldbachG11PiLiHi N m) (V m) := by
      rcases le_max_iff.mp hu with hb | hg
      · exact False.elim ((not_le_of_gt hlold) hb)
      · exact hg
    have hmax : max (goldbachG11PiLiLo N ε m) (T m) < r := by
      rcases min_lt_iff.mp hl with hb | hg
      · exact False.elim ((not_lt_of_ge hu) hb)
      · exact hg
    exact ⟨⟨hr,hp,hlold,(le_min_iff.mp hmin).1⟩,
      (max_lt_iff.mp hmax).2,(le_min_iff.mp hmin).2⟩
  · rintro ⟨⟨hr,hp,hl,hh⟩,ht,hv⟩
    exact ⟨hr,hp,(min_le_right _ _).trans_lt (max_lt hl ht),
      (le_min hh hv).trans (le_max_right _ _)⟩


end G12ClippedWindow
