import MathlibNt.SieveTheory.LiLiuGoldbachG12ClippedConsumers

noncomputable section
open Classical Finset
open scoped BigOperators
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
open Wu2004MeanValue AnalyticNumberTheory.Sieve AnalyticNumberTheory.LargeSieve
namespace G12ClippedWindow

/-- The distributed residual is exactly the actual AP window discrepancy. -/
theorem residual_eq_ap_counts {N : ℕ} {ε : ℝ} {g L U : ℕ → ℝ}
    (hN : 2 ≤ N) (h : Admissible N ε g L U) (d b : ℕ) :
    residual N g L U d b =
      ∑ m ∈ (goldbachG12ActiveProductSupport N).filter (fun m => m.Coprime d),
        g m * ((((window N L U m).filter (fun r => Nat.ModEq d (m*r) b)).card : ℝ) -
          ((window N L U m).card : ℝ) / (d.totient : ℝ)) := by
  unfold residual
  apply sum_congr rfl
  intro m hm
  obtain ⟨hm,hmd⟩ := mem_filter.mp hm
  rw [apWindow_card_eq_inverse h d b hN hm hmd, window_card hN h hm]

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

/-- The full clipped mass really is the coefficient-weighted cardinality of the cell. -/
theorem longMask_mass_eq (N : ℕ) (ε : ℝ) (cellLong longOK : ℕ → Prop)
    (T V : ℕ → ℝ) :
    mass N (longMask N cellLong longOK) (clampLower N ε T V) (clampUpper N ε V) =
      ∑ m ∈ (goldbachG12ActiveProductSupport N).filter (fun m => cellLong m ∧ ¬longOK m),
        goldbachG12NormalizedCoefficient N m *
          (((goldbachG11LinkedPrimeWindow N ε m).filter
            (fun r : ℕ => T m < (r : ℝ) ∧ (r : ℝ) ≤ V m)).card : ℝ) := by
  simp only [mass, clamp_window_eq_filter, sum_filter, longMask]
  apply sum_congr rfl
  intro m _
  split_ifs <;> simp

end G12ClippedWindow
