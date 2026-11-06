import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring

namespace MathlibNt.SieveTheory

/-- The three lower cutoffs appearing in Suzuki's depth-four recursion are
forced by the terminal lower-Rosser boundary crossing.  This is the first
nontrivial layer after depth two: no source cutoff is silently discarded. -/
theorem lowerRosser_depthFour_terminal_forces_source_cutoffs
    {D p₀ p₁ p₂ q : ℕ}
    (h10 : p₁ < p₀) (h21 : p₂ < p₁) (hq2 : q < p₂)
    (hterminal : D ≤ p₀ * p₁ * p₂ * q ^ 3) :
    D ≤ p₀ ^ 6 ∧
      D ≤ p₀ * p₁ ^ 5 ∧
      D ≤ p₀ * p₁ * p₂ ^ 4 := by
  have hq0 : q ≤ p₀ := (hq2.trans (h21.trans h10)).le
  have hp20 : p₂ ≤ p₀ := (h21.trans h10).le
  have hp10 : p₁ ≤ p₀ := h10.le
  have hq1 : q ≤ p₁ := (hq2.trans h21).le
  have hp21 : p₂ ≤ p₁ := h21.le
  have hq2' : q ≤ p₂ := hq2.le
  constructor
  · calc
      D ≤ p₀ * p₁ * p₂ * q ^ 3 := hterminal
      _ ≤ p₀ * p₀ * p₀ * p₀ ^ 3 := by
        gcongr
      _ = p₀ ^ 6 := by ring
  constructor
  · calc
      D ≤ p₀ * p₁ * p₂ * q ^ 3 := hterminal
      _ ≤ p₀ * p₁ * p₁ * p₁ ^ 3 := by
        gcongr
      _ = p₀ * p₁ ^ 5 := by ring
  · calc
      D ≤ p₀ * p₁ * p₂ * q ^ 3 := hterminal
      _ ≤ p₀ * p₁ * p₂ * p₂ ^ 3 := by
        gcongr
      _ = p₀ * p₁ * p₂ ^ 4 := by ring



end MathlibNt.SieveTheory
