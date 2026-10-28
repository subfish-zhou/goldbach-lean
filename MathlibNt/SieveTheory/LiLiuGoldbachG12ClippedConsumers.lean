import MathlibNt.SieveTheory.LiLiuGoldbachG12ClippedMass

noncomputable section
open Classical Finset Filter
open scoped BigOperators Topology
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
open Wu2004MeanValue AnalyticNumberTheory.Sieve AnalyticNumberTheory.LargeSieve
namespace G12ClippedWindow

/-- The high specialization retains the original normalized product coefficient. -/
theorem high_admissible {N : ℕ} (hN : 2 ≤ N) (ε : ℝ) :
    Admissible N ε (goldbachG12NormalizedCoefficient N)
      (G12LowHighOutput.highLo N ε) (goldbachG11PiLiHi N) := by
  intro m hm
  exact ⟨⟨(goldbachG12NormalizedCoefficient_bounds N m).1, le_rfl⟩,
    (G12LowHighOutput.highLo_bounds hN hm).1,
    (G12LowHighOutput.highLo_bounds hN hm).2, le_rfl⟩

theorem high_window (N m : ℕ) (ε : ℝ) :
    window N (G12LowHighOutput.highLo N ε) (goldbachG11PiLiHi N) m =
      G12LowHighOutput.highWindow N ε m := by
  ext r
  simp only [window, mem_filter, G12LowHighOutput.mem_highWindow]


/-- The actual high mass is independent of d. -/
def highMass (N : ℕ) (ε : ℝ) : ℝ :=
  ∑ m ∈ goldbachG12ActiveProductSupport N,
    goldbachG12NormalizedCoefficient N m * (G12LowHighOutput.highWindow N ε m).card


/-- Only the long cofactor is masked; no short-prime selection is hidden here. -/
def longMask (N : ℕ) (cellLong longOK : ℕ → Prop) (m : ℕ) : ℝ :=
  if cellLong m ∧ ¬longOK m then goldbachG12NormalizedCoefficient N m else 0

/-- Normalize an empty upper window to oldLo, rather than asserting an unchecked endpoint ≥ 2. -/
def clampUpper (N : ℕ) (ε : ℝ) (V : ℕ → ℝ) (m : ℕ) : ℝ :=
  max (goldbachG11PiLiLo N ε m) (min (goldbachG11PiLiHi N m) (V m))

def clampLower (N : ℕ) (ε : ℝ) (T V : ℕ → ℝ) (m : ℕ) : ℝ :=
  min (clampUpper N ε V m) (max (goldbachG11PiLiLo N ε m) (T m))

theorem clamp_admissible {N : ℕ} (hN : 2 ≤ N) (ε : ℝ)
    (cellLong longOK : ℕ → Prop) (T V : ℕ → ℝ) :
    Admissible N ε (longMask N cellLong longOK)
      (clampLower N ε T V) (clampUpper N ε V) := by
  intro m hm
  have ho := (goldbachG12PiLiEndpoints_bounds (ε := ε) hN hm).2.1
  refine ⟨?_,?_,min_le_left _ _,?_⟩
  · unfold longMask
    split_ifs
    · exact ⟨(goldbachG12NormalizedCoefficient_bounds N m).1,le_rfl⟩
    · exact ⟨le_rfl,(goldbachG12NormalizedCoefficient_bounds N m).1⟩
  · exact le_min (le_max_left _ _) (le_max_left _ _)
  · exact max_le ho ((min_le_left _ _).trans le_rfl)


end G12ClippedWindow
