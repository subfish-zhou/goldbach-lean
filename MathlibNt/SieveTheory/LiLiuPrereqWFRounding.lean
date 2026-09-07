import MathlibNt.SieveTheory.LiLiuPrereqWFSmallDensity
import Mathlib.Algebra.Order.Floor.Semiring

/-!
# Exact integer-level transport of the actual small weights

The natural level is `ceil L`, not `floor L + 1`: every test in the
coefficients is a strict comparison of an integer with the real level.
The rounded cutoff is matched using `s = log (ceil L) / log u`.
-/

namespace MathlibNt.SieveTheory.LiLiuPrereqWF.SmallRosser

open ArithmeticFunction Finset
open scoped Classical

theorem nat_lt_real_iff_lt_ceil (n : ℕ) (L : ℝ) :
    (n : ℝ) < L ↔ (n : ℝ) < (⌈L⌉₊ : ℝ) := by
  rw [Nat.cast_lt]
  exact Nat.lt_ceil.symm

theorem integer_cubic_lt_ceil (m p : ℕ) (L : ℝ) (k : ℕ) :
    (m : ℝ) * (p : ℝ) ^ k < L ↔
      (m : ℝ) * (p : ℝ) ^ k < (⌈L⌉₊ : ℝ) := by
  simpa only [Nat.cast_mul, Nat.cast_pow] using
    nat_lt_real_iff_lt_ceil (m * p ^ k) L

theorem lowerAdmissibleSet_ceil (L : ℝ) (s : Finset ℕ) :
    LowerAdmissibleSet (⌈L⌉₊ : ℝ) s ↔ LowerAdmissibleSet L s := by
  unfold LowerAdmissibleSet
  simp only [← integer_cubic_lt_ceil]

theorem upperAdmissibleSet_ceil (L : ℝ) (s : Finset ℕ) :
    UpperAdmissibleSet (⌈L⌉₊ : ℝ) s ↔ UpperAdmissibleSet L s := by
  unfold UpperAdmissibleSet
  simp only [← integer_cubic_lt_ceil]

theorem lowerWeight_ceil (M : ℕ) (L : ℝ) :
    lowerWeight M (⌈L⌉₊ : ℝ) = lowerWeight M L := by
  ext n
  simp only [lowerWeight_apply, lowerAdmissibleSet_ceil, ← nat_lt_real_iff_lt_ceil]

theorem upperWeight_ceil (M : ℕ) (L : ℝ) :
    upperWeight M (⌈L⌉₊ : ℝ) = upperWeight M L := by
  ext n
  simp only [upperWeight_apply, upperAdmissibleSet_ceil, ← nat_lt_real_iff_lt_ceil]

theorem setWeight_ceil (L : ℝ) (s : Finset ℕ) :
    setWeight (⌈L⌉₊ : ℝ) s = setWeight L s := by
  simp only [setWeight, lowerAdmissibleSet_ceil, ← nat_lt_real_iff_lt_ceil]

theorem upperSetWeight_ceil (L : ℝ) (s : Finset ℕ) :
    upperSetWeight (⌈L⌉₊ : ℝ) s = upperSetWeight L s := by
  simp only [upperSetWeight, upperAdmissibleSet_ceil, ← nat_lt_real_iff_lt_ceil]

theorem lowerBoundary_ceil (L : ℝ) (q : ℕ) (s : Finset ℕ) :
    LowerBoundary (⌈L⌉₊ : ℝ) q s ↔ LowerBoundary L q s := by
  unfold LowerBoundary
  simp only [lowerAdmissibleSet_ceil, ← nat_lt_real_iff_lt_ceil,
    ← not_lt, ← integer_cubic_lt_ceil]

theorem upperBoundary_ceil (L : ℝ) (q : ℕ) (s : Finset ℕ) :
    UpperBoundary (⌈L⌉₊ : ℝ) q s ↔ UpperBoundary L q s := by
  unfold UpperBoundary
  simp only [upperAdmissibleSet_ceil, ← nat_lt_real_iff_lt_ceil,
    ← not_lt, ← integer_cubic_lt_ceil]

theorem densityDefects_ceil (L : ℝ) (g : ℕ → ℝ) (ps : List ℕ) :
    lowerDensityDefect (⌈L⌉₊ : ℝ) g ps = lowerDensityDefect L g ps ∧
    upperDensityDefect (⌈L⌉₊ : ℝ) g ps = upperDensityDefect L g ps := by
  induction ps with
  | nil => exact ⟨rfl, rfl⟩
  | cons p ps ih =>
      simp only [lowerDensityDefect, upperDensityDefect, ih.1, ih.2,
        lowerBoundaryDensity, upperBoundaryDensity, lowerBoundary_ceil, upperBoundary_ceil,
        and_self]

/-- The coordinate uses the rounded level but the original real cutoff. -/
noncomputable def roundedSieveCoordinate (L u : ℝ) : ℝ :=
  Real.log (⌈L⌉₊ : ℝ) / Real.log u

theorem roundedSieveCoordinate_pos {L u : ℝ} (hL : 1 < L) (hu : 1 < u) :
    0 < roundedSieveCoordinate L u :=
  div_pos (Real.log_pos (hL.trans_le (Nat.le_ceil L))) (Real.log_pos hu)

theorem roundedSieveCoordinate_cutoff {L u : ℝ} (hL : 1 < L) (hu : 1 < u) :
    (⌈L⌉₊ : ℝ) ^ (1 / roundedSieveCoordinate L u) = u := by
  have hR : 0 < (⌈L⌉₊ : ℝ) := lt_trans zero_lt_one (hL.trans_le (Nat.le_ceil L))
  have hlog : Real.log (⌈L⌉₊ : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (hL.trans_le (Nat.le_ceil L)))
  rw [Real.rpow_def_of_pos hR]
  unfold roundedSieveCoordinate
  field_simp
  exact Real.exp_log (by linarith)

theorem roundedSieveCoordinate_prime_cutoff {L u : ℝ}
    (hL : 1 < L) (hu : 1 < u) (p : ℕ) :
    p < ⌈(⌈L⌉₊ : ℝ) ^ (1 / roundedSieveCoordinate L u)⌉₊ ↔ (p : ℝ) < u := by
  rw [roundedSieveCoordinate_cutoff hL hu, Nat.lt_ceil]

theorem roundedSieveCoordinate_carrier (P : Finset ℕ) {L u : ℝ}
    (hL : 1 < L) (hu : 1 < u) :
    P.filter (fun p : ℕ => p.Prime ∧
      p < ⌈(⌈L⌉₊ : ℝ) ^ (1 / roundedSieveCoordinate L u)⌉₊) =
    P.filter (fun p : ℕ => p.Prime ∧ (p : ℝ) < u) := by
  ext p
  simp only [Finset.mem_filter, roundedSieveCoordinate_prime_cutoff hL hu]

theorem small_rounded_cutoff_bounds {D ε : ℝ}
    (hD : 2 ≤ D) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    2 ≤ ⌈D ^ (ε ^ 2)⌉₊ ∧ ⌈D ^ (ε ^ 2)⌉₊ ≤ ⌈D ^ ε⌉₊ := by
  constructor
  · have hu : (1 : ℝ) < D ^ (ε ^ 2) :=
      Real.one_lt_rpow (by linarith) (sq_pos_of_pos hε)
    have hn : 1 < ⌈D ^ (ε ^ 2)⌉₊ := Nat.lt_ceil.mpr (by simpa using hu)
    omega
  · exact Nat.ceil_mono
      (Real.rpow_le_rpow_of_exponent_le (by linarith) (by nlinarith))

end MathlibNt.SieveTheory.LiLiuPrereqWF.SmallRosser
