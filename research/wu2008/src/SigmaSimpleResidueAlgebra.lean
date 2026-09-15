import SigmaHermiteActualAssembly
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.FieldTheory.Separable

noncomputable section
namespace SigmaSimpleResiduePrimitive
open Polynomial Complex Set
open scoped BigOperators

/-- Lagrange interpolation divided by the original simple-pole product. -/
theorem lagrange_fraction (s : Finset ℂ) (R : ℂ[X])
    (hR : R.degree < s.card) (t : ℂ) (ht : ∀ z ∈ s, t-z ≠ 0) :
    R.eval t / (∏ z ∈ s, (t-z)) =
      ∑ z ∈ s, (R.eval z / (∏ w ∈ s.erase z, (z-w))) / (t-z) := by
  classical
  have he := congrArg (Polynomial.eval t)
    (Lagrange.eq_interpolate (s := s) (v := id) Function.injective_id.injOn hR)
  rw [Lagrange.interpolate_eq_sum] at he
  simp only [eval_finsetSum, eval_mul, eval_C, eval_prod, eval_sub, eval_X, id_eq] at he
  rw [he, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro z hz
  rw [← Finset.mul_prod_erase s (fun w => t-w) hz]
  have hp : (∏ w ∈ s.erase z, (t-w)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro w hw
    exact ht w (Finset.mem_of_mem_erase hw)
  field_simp

/-- Exact complex roots and exact product-form residues; no chosen root table. -/
def residue (R B : ℝ[X]) (z : ℂ) : ℂ :=
  (R.map Complex.ofRealHom).eval z /
    ((B.map Complex.ofRealHom).leadingCoeff *
      ∏ w ∈ (B.map Complex.ofRealHom).roots.toFinset.erase z, (z-w))

def simplePrimitive (R B : ℝ[X]) (t : ℝ) : ℝ :=
  ∑ z ∈ (B.map Complex.ofRealHom).roots.toFinset,
    SigmaRationalOuterFTC.rootPrimitive z.re z.im (residue R B z).re
      (residue R B z).im t

end SigmaSimpleResiduePrimitive
