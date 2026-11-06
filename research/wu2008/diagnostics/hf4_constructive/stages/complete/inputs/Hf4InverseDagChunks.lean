import Hf4InverseDagData
import Mathlib.Data.List.TakeDrop

/-! UNCOMPILED generic chunk recombination. This file contains no numerical
`decide`: it combines already-proved bounded arithmetic checks. -/
namespace Hf4Quad.InverseDag
open CheckedDag

theorem checked_prefix_extend (plan : List Step)
    (seeds literals : ℕ → RationalModel.Certificate) (m h : ℚ)
    (start width : ℕ)
    (before : checked seeds literals m h (plan.take start) [] = true)
    (chunk : checkRange plan seeds literals m h start width = true) :
    checked seeds literals m h (plan.take (start+width)) [] = true := by
  rw [List.take_add, checked_append]
  exact Bool.and_eq_true_iff.mpr ⟨before, chunk⟩

theorem checked_from_complete_prefix (plan : List Step)
    (seeds literals : ℕ → RationalModel.Certificate) (m h : ℚ)
    (ok : checked seeds literals m h (plan.take plan.length) [] = true) :
    checked seeds literals m h plan [] = true := by
  simpa only [List.take_length] using ok

end Hf4Quad.InverseDag
