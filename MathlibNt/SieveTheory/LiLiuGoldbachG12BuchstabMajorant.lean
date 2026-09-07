import MathlibNt.SieveTheory.LiLiuGoldbachG12BuchstabMajorantPolynomials

set_option autoImplicit false

namespace LiLiuGoldbachG12BuchstabMajorant

open LiLiuBuchstabSharp

/-- The existing closed delay barrier supplies both G12 constants above 17/4. -/
theorem majorants_existing_tail {u : ℝ} (hu : (17 / 4 : ℝ) ≤ u) :
    LiLiuPrereqBuchstab.buchstab u ≤ (564383 / 1000000 : ℝ) ∧
    LiLiuPrereqBuchstab.buchstab u ≤ (56199 / 100000 : ℝ) := by
  have h := buchstab_sharp_tail_closed hu
  constructor <;> linarith

/-- The first G12 constant on the entire initial unit interval. -/
theorem majorant_broad_first_window {u : ℝ} (hu : 3 ≤ u) (hu' : u ≤ 4) :
    LiLiuPrereqBuchstab.buchstab u ≤ (564383 / 1000000 : ℝ) := by
  have he := (rationalStage_error 1 (u := u) (by norm_num; exact hu)
    (by norm_num; exact hu')).2
  have hp := closure_stage1_upper hu hu'
  have hb := polynomial1_broad (x := 4-u) (by linarith) (by linarith)
  linarith

/-- The second G12 constant from its literal rational starting point to four. -/
theorem majorant_sharp_first_window {u : ℝ}
    (hu : (79 / 25 : ℝ) ≤ u) (hu' : u ≤ 4) :
    LiLiuPrereqBuchstab.buchstab u ≤ (56199 / 100000 : ℝ) := by
  have h3 : (3 : ℝ) ≤ u := by linarith
  have he := (rationalStage_error 1 (u := u) (by norm_num; exact h3)
    (by norm_num; exact hu')).2
  have hp := closure_stage1_upper h3 hu'
  have hb := polynomial1_sharp (x := 4-u) (by linarith) (by linarith)
  linarith

/-- A certified full second interval, not a pointwise numerical sample. -/
theorem majorant_sharp_second_window {u : ℝ} (hu : 4 ≤ u) (hu' : u ≤ 5) :
    LiLiuPrereqBuchstab.buchstab u ≤ (56199 / 100000 : ℝ) := by
  have he := (rationalStage_error 2 (u := u) (by norm_num; exact hu)
    (by norm_num; exact hu')).2
  have hp := closure_stage2_upper hu hu'
  have hb := polynomial2_sharp (x := 5-u) (by linarith) (by linarith)
  linarith

/-- The second G12 constant on the unbounded tail starting at four. -/
theorem majorant_sharp_from_four {u : ℝ} (hu : 4 ≤ u) :
    LiLiuPrereqBuchstab.buchstab u ≤ (56199 / 100000 : ℝ) := by
  by_cases h : u ≤ 5
  · exact majorant_sharp_second_window hu h
  · exact (majorants_existing_tail (by linarith)).2

/-- The author's first G12 pointwise majorant for the actual Buchstab function,
with no upper cutoff and no carried estimate premise. -/
theorem buchstab_le_564383 {u : ℝ} (hu : 3 ≤ u) :
    LiLiuPrereqBuchstab.buchstab u ≤ (564383 / 1000000 : ℝ) := by
  by_cases h : u ≤ 4
  · exact majorant_broad_first_window hu h
  · have hb := majorant_sharp_from_four (u := u) (by linarith)
    linarith

/-- The author's second G12 pointwise majorant for the actual Buchstab function,
with the exact threshold 79/25 and no upper cutoff. -/
theorem buchstab_le_561990 {u : ℝ} (hu : (79 / 25 : ℝ) ≤ u) :
    LiLiuPrereqBuchstab.buchstab u ≤ (56199 / 100000 : ℝ) := by
  by_cases h : u ≤ 4
  · exact majorant_sharp_first_window hu h
  · exact majorant_sharp_from_four (by linarith)

end LiLiuGoldbachG12BuchstabMajorant
