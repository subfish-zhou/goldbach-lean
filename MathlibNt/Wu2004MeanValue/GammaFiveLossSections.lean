import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Geometry of the Gamma₅ loss sections

With B = 1/κ₂, the legal section imposes the extra cutoff t ≤ v/S.
The lemmas below identify both sections on the loss interval, show that
both are empty below it, and remove the extra cutoff above it. They are
parameterized endpoint identities; connecting them to the actual feedback
integrals requires the corresponding change-of-variables identities.
-/

namespace Wu2004MeanValue.GammaFiveLossBudget

/-- Exact full and legal section endpoints throughout the loss interval. -/
theorem loss_section_endpoints {S B v : ℝ}
    (hS : 0 < S) (hB : 1/3 ≤ B) (hBhi : B < 1/2)
    (hA : 5/4 ≤ S*(1-2*B))
    (hv : S*(1-2*B) ≤ v ∧ v ≤ S/3) :
    max (1/S) (max (1-v/S-B) (1-v/S-1/2)) = 1-v/S-B ∧
    min B (min (1-v/S-1/S) ((1-v/S)/2)) = (1-v/S)/2 ∧
    min B (min (1-v/S-1/S) (min ((1-v/S)/2) (v/S))) = v/S := by
  have hBS : S/3 ≤ S*B := by nlinarith
  have hS3 : 3 ≤ S := by nlinarith [hv.1,hv.2]
  have hr : v/S ≤ 1/3 := (div_le_iff₀ hS).mpr (by nlinarith [hv.2])
  have hrlo : 1-2*B ≤ v/S := (le_div_iff₀ hS).mpr (by nlinarith [hv.1])
  have hinv : 1/S ≤ 1/3 := (div_le_iff₀ hS).mpr (by nlinarith)
  have he : v/S*S = v := div_mul_cancel₀ v hS.ne'
  have hlow : 1/S ≤ 1-v/S-B := (div_le_iff₀ hS).mpr (by nlinarith [hv.2])
  have hhalf : (1-v/S)/2 ≤ 1-v/S-1/S := by linarith
  have hfullB : (1-v/S)/2 ≤ B := by linarith
  have hlegal : v/S ≤ (1-v/S)/2 := by linarith
  refine ⟨?_,?_,?_⟩
  · rw [max_eq_left (by linarith : 1-v/S-1/2 ≤ 1-v/S-B), max_eq_right hlow]
  · rw [min_eq_right hhalf, min_eq_right hfullB]
  · rw [min_eq_right hlegal, min_eq_right (hlegal.trans hhalf),
      min_eq_right (hlegal.trans hfullB)]

/-- Above the loss interval, the extra legal upper cutoff is redundant. -/
theorem legal_upper_eq_full_above {S B v : ℝ} (hS : 0 < S) (hv : S/3 ≤ v) :
    min B (min (1-v/S-1/S) (min ((1-v/S)/2) (v/S))) =
      min B (min (1-v/S-1/S) ((1-v/S)/2)) := by
  have h : 1/3 ≤ v/S := (le_div_iff₀ hS).mpr (by nlinarith)
  rw [min_eq_left (by linarith : (1-v/S)/2 ≤ v/S)]

/-- Below the loss interval, even the full section has no interior. -/
theorem full_section_empty_below {S B v : ℝ} (hS : 0 < S)
    (hv : v ≤ S*(1-2*B)) :
    min B (min (1-v/S-1/S) ((1-v/S)/2)) ≤
      max (1/S) (max (1-v/S-B) (1-v/S-1/2)) := by
  have hr : v/S ≤ 1-2*B := (div_le_iff₀ hS).mpr (by nlinarith)
  calc
    min B _ ≤ B := min_le_left _ _
    _ ≤ 1-v/S-B := by linarith
    _ ≤ max (1-v/S-B) (1-v/S-1/2) := le_max_left _ _
    _ ≤ max (1/S) _ := le_max_right _ _

/-- The legal section opens at the middle breakpoint of the loss kernel. -/
theorem legal_section_nonempty_iff {S B v : ℝ} (hS : 0 < S) :
    1-v/S-B < v/S ↔ S*(1-B)/2 < v := by
  have he : v/S*S = v := div_mul_cancel₀ v hS.ne'
  constructor
  · intro h
    have hm := mul_pos (by linarith : 0 < 2*(v/S)-(1-B)) hS
    nlinarith
  · intro h
    have hr : (1-B)/2 < v/S := (lt_div_iff₀ hS).mpr (by nlinarith)
    linarith

/-- The full section opens at the left breakpoint of the loss kernel. -/
theorem full_section_nonempty_iff {S B v : ℝ} (hS : 0 < S) :
    1-v/S-B < (1-v/S)/2 ↔ S*(1-2*B) < v := by
  have he : v/S*S = v := div_mul_cancel₀ v hS.ne'
  constructor
  · intro h
    have hm := mul_pos (by linarith : 0 < v/S-(1-2*B)) hS
    nlinarith
  · intro h
    have hr : 1-2*B < v/S := (lt_div_iff₀ hS).mpr (by nlinarith)
    linarith

end Wu2004MeanValue.GammaFiveLossBudget
