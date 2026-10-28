import MathlibNt.SieveTheory.Distribution.LiuPan.LiuPanSignedResidualSplit
import MathlibNt.SieveTheory.Selberg.Liu.LiuSelbergEvenAssembly
import MathlibNt.SieveTheory.Distribution.LiuPan.LiuPanPrimePowerLargeSieve

/-!
# Combined inverse-log discrepancy for Liu's Pan endpoint

The Type I endpoint, Type II endpoint, and complete signed-main kernel are
recombined before taking an absolute value.  Vaughan's finite identity then
identifies this expression with the source-weighted `Λ / log` discrepancy.
The already separated prime-power correction remains on its own power-saving
scale.

The older componentwise contracts are intentionally left unchanged.  Their
degenerate or conductor-one endpoint behavior does not prove the combined
estimate introduced here.
-/

open scoped BigOperators

namespace MathlibNt.SieveTheory.LiuWeight

open Filter Finset
open AnalyticNumberTheory.Sieve

/-! ## Exact finite combination -/

/-- The Type I endpoint, Type II endpoint, and complete signed main, combined
inside one absolute value before any analytic estimate is applied. -/
noncomputable def liuPanCombinedInverseLogDiscrepancy
    (main : ℝ → ℝ) (y X q l : ℕ) (f : ℕ → ℝ) (u v : ℕ) : ℝ :=
  |panPieceSum y X q l f
        (fun y q l => apV1 y q l u / Real.log (y : ℝ)) +
    panPieceSum y X q l f
        (fun y q l => apV3 y q l u v / Real.log (y : ℝ)) +
    liuPanSignedMainSum main y X q l f u v|



/-- Maximum of the exact combined discrepancy over canonical reduced residues. -/
noncomputable def liuPanCombinedInverseLogMaxL
    (main : ℝ → ℝ) (y X q : ℕ) (f : ℕ → ℝ) (u v : ℕ) : ℝ :=
  let S := unitResidues q
  if h : S.Nonempty then
    (S.image (fun l =>
      liuPanCombinedInverseLogDiscrepancy main y X q l f u v)).max'
        (Finset.image_nonempty.mpr h)
  else 0

/-- Maximum of the exact combined discrepancy over `y ≤ x`. -/
noncomputable def liuPanCombinedInverseLogMaxY
    (main : ℝ → ℝ) (X q x : ℕ) (f : ℕ → ℝ) (u v : ℕ) : ℝ :=
  ((range (x + 1)).image (fun y =>
    liuPanCombinedInverseLogMaxL main y X q f u v)).max'
      (Finset.image_nonempty.mpr ⟨0, by simp⟩)

/-- The zero modulus has no canonical reduced residue. -/
@[simp] theorem liuPanCombinedInverseLogMaxL_zero
    (main : ℝ → ℝ) (y X : ℕ) (f : ℕ → ℝ) (u v : ℕ) :
    liuPanCombinedInverseLogMaxL main y X 0 f u v = 0 := by
  simp [liuPanCombinedInverseLogMaxL]

/-- Modulus one uses its unique canonical residue `0`. -/
@[simp] theorem liuPanCombinedInverseLogMaxL_one
    (main : ℝ → ℝ) (y X : ℕ) (f : ℕ → ℝ) (u v : ℕ) :
    liuPanCombinedInverseLogMaxL main y X 1 f u v =
      liuPanCombinedInverseLogDiscrepancy main y X 1 0 f u v := by
  simp [liuPanCombinedInverseLogMaxL]

/-- The zero-modulus `y`-maximum is canonically zero. -/
@[simp] theorem liuPanCombinedInverseLogMaxY_zero
    (main : ℝ → ℝ) (X x : ℕ) (f : ℕ → ℝ) (u v : ℕ) :
    liuPanCombinedInverseLogMaxY main X 0 x f u v = 0 := by
  unfold liuPanCombinedInverseLogMaxY
  apply le_antisymm
  · apply Finset.max'_le
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨y, hy, rfl⟩
    simp
  · apply Finset.le_max'
    exact Finset.mem_image.mpr ⟨0, by simp, by simp⟩





/-! ## Exact correction separation and maxima -/




/-! ## Source-family analytic input -/






/-! ## Source-family and little-oh consumers -/





end MathlibNt.SieveTheory.LiuWeight
