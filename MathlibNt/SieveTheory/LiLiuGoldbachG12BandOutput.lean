import MathlibNt.SieveTheory.LiLiuGoldbachG12ClippedOutputSemantics
import MathlibNt.SieveTheory.LiLiuGoldbachG12RoughBudget
import MathlibNt.SieveTheory.LiLiuGoldbachG12BoundarySource

noncomputable section
open Classical Finset
open scoped BigOperators
open MathlibNt.SieveTheory MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

namespace G12BandOutput

/-- The output-prime indicator is nonnegative, including repeated representations. -/
theorem prime_indicator_nonneg (N m r : ℕ) :
    (0 : ℝ) ≤ if (N-r*m).Prime then 1 else 0 := by
  split <;> norm_num

/-- Ungated source loss from the first-prime coprimality gate. -/
def badMass (N : ℕ) (g L U : ℕ → ℝ) : ℝ :=
  ∑ m ∈ goldbachG12ActiveProductSupport N,
    g m * (((G12ClippedWindow.window N L U m).filter (fun r => ¬r.Coprime N)).card : ℝ)

/-- Physical mass retains short-prime coprimality, unlike the sieve source. -/
def goodMass (N : ℕ) (g L U : ℕ → ℝ) : ℝ :=
  ∑ m ∈ goldbachG12ActiveProductSupport N,
    g m * (((G12ClippedWindow.window N L U m).filter (fun r => r.Coprime N)).card : ℝ)

theorem mass_split (N : ℕ) (g L U : ℕ → ℝ) :
    G12ClippedWindow.mass N g L U = goodMass N g L U + badMass N g L U := by
  unfold G12ClippedWindow.mass goodMass badMass
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro m _
  simp only [← sum_boole, ← mul_add, ← sum_add_distrib]
  congr 1
  calc
    _ = ∑ _r ∈ G12ClippedWindow.window N L U m, (1 : ℝ) := by simp
    _ = _ := sum_congr rfl (by intro r _; by_cases h : r.Coprime N <;> simp [h])

/-- Uniform transport for arbitrary admissible windows, not a cellwise estimate. -/
theorem badMass_le {N : ℕ} (hN : 4 ≤ N) {ε : ℝ} {g L U : ℕ → ℝ}
    (had : G12ClippedWindow.Admissible N ε g L U) :
    badMass N g L U ≤ 21*N/(N : ℝ)^(4/53 : ℝ) := by
  apply le_trans _ (goldbachG12MainMassBad_le hN ε)
  unfold badMass goldbachG12MainMassBad
  apply sum_le_sum
  intro m hm
  have hsub : (G12ClippedWindow.window N L U m).filter (fun r => ¬r.Coprime N) ⊆
      (goldbachG11LinkedPrimeWindow N ε m).filter (fun r => r ∣ N) := by
    intro r hr
    obtain ⟨hr,hn⟩ := mem_filter.mp hr
    have hw := G12ClippedWindow.window_subset had hm hr
    have hp := (mem_filter.mp hw).2.1
    exact mem_filter.mpr ⟨hw,by_contra fun hd => hn (hp.coprime_iff_not_dvd.mpr hd)⟩
  exact mul_le_mul (had m hm).1.2 (Nat.cast_le.mpr (card_le_card hsub))
    (Nat.cast_nonneg _) (goldbachG12NormalizedCoefficient_bounds N m).1

/-- Clamp without masking the original body coefficient. -/
theorem clamp_admissible {N : ℕ} (hN : 2 ≤ N) (ε : ℝ) (T V : ℕ → ℝ) :
    G12ClippedWindow.Admissible N ε (goldbachG12NormalizedCoefficient N)
      (G12ClippedWindow.clampLower N ε T V) (G12ClippedWindow.clampUpper N ε V) := by
  have he : G12ClippedWindow.longMask N (fun _ => True) (fun _ => False) =
      goldbachG12NormalizedCoefficient N := by
    funext m
    simp [G12ClippedWindow.longMask]
  rw [← he]
  exact G12ClippedWindow.clamp_admissible hN ε (fun _ => True) (fun _ => False) T V

end G12BandOutput
