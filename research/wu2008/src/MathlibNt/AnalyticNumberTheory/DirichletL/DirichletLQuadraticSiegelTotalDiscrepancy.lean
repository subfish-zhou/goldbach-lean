import MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLQuadraticSiegelDiscrepancyControl

/-!
# Total control of the quadratic Siegel convolution discrepancy

The floor sum is split at `m`.  On `d < m`, the floor error is at most one
and `|Re χ(d)| ≤ 1`, so the complete short contribution costs at most `m`.
On `d ≥ m`, the existing Pólya--Vinogradov/Abel estimate controls the
floor-weighted tail.  The final theorem inserts this honest total estimate
back into the square-lower-bound/Pólya--Vinogradov bridge.

This closes the discrepancy-control layer.  It does not by itself prove a
large-conductor Siegel lower bound: optimizing this one-fold square estimate
leaves an error on the scale forced by `sqrt q (1 + log q)`.  A genuine
higher-convolution or power-amplification producer is still required before
one can derive `L(1,χ) ≫_η q⁻η`.
-/

open Complex Finset
open scoped BigOperators Real

namespace DirichletCharacter

/-- A real quotient differs from its natural-number floor by at most one. -/
lemma abs_natDiv_cast_sub_div_le_one (X d : ℕ) (hd : 1 ≤ d) :
    |((X / d : ℕ) : ℝ) - (X : ℝ) / (d : ℝ)| ≤ 1 := by
  have hdpos : 0 < d := by omega
  have hdR : (0 : ℝ) < d := by exact_mod_cast hdpos
  have hdecomp :
      (X : ℝ) = (d : ℝ) * ((X / d : ℕ) : ℝ) + ((X % d : ℕ) : ℝ) := by
    exact_mod_cast (Nat.div_add_mod X d).symm
  have hquot :
      (X : ℝ) / (d : ℝ) =
        ((X / d : ℕ) : ℝ) + ((X % d : ℕ) : ℝ) / (d : ℝ) := by
    rw [div_eq_iff hdR.ne', add_mul, div_mul_cancel₀ _ hdR.ne']
    simpa [mul_comm] using hdecomp
  have hrnonneg : 0 ≤ ((X % d : ℕ) : ℝ) / (d : ℝ) := by positivity
  have hrle : ((X % d : ℕ) : ℝ) / (d : ℝ) ≤ 1 := by
    rw [div_le_one hdR]
    exact_mod_cast (Nat.mod_lt X hdpos).le
  rw [hquot]
  rw [show ((X / d : ℕ) : ℝ) -
      (((X / d : ℕ) : ℝ) + ((X % d : ℕ) : ℝ) / (d : ℝ)) =
        -(((X % d : ℕ) : ℝ) / (d : ℝ)) by ring,
      abs_neg, abs_of_nonneg hrnonneg]
  exact hrle

/-- The entire short floor-error segment costs at most the cutoff `m`. -/
lemma abs_quadratic_shortFloorError_le
    {q : ℕ} (χ : DirichletCharacter ℂ q) (X m : ℕ) :
    |∑ d ∈ Ico 1 m,
        (((X / d : ℕ) : ℝ) * (χ d).re -
          (X : ℝ) * ((χ d).re / (d : ℝ)))| ≤ (m : ℝ) := by
  calc
    |∑ d ∈ Ico 1 m,
        (((X / d : ℕ) : ℝ) * (χ d).re -
          (X : ℝ) * ((χ d).re / (d : ℝ)))|
        ≤ ∑ d ∈ Ico 1 m,
            |((X / d : ℕ) : ℝ) * (χ d).re -
              (X : ℝ) * ((χ d).re / (d : ℝ))| :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _d ∈ Ico 1 m, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro d hd
      rw [mem_Ico] at hd
      have hfloor := abs_natDiv_cast_sub_div_le_one X d hd.1
      have hchi : |(χ d).re| ≤ 1 :=
        (Complex.abs_re_le_norm _).trans (DirichletCharacter.norm_le_one χ d)
      have heq :
          ((X / d : ℕ) : ℝ) * (χ d).re -
              (X : ℝ) * ((χ d).re / (d : ℝ)) =
            (((X / d : ℕ) : ℝ) - (X : ℝ) / (d : ℝ)) * (χ d).re := by
        ring
      rw [heq, abs_mul]
      exact mul_le_one₀ hfloor (abs_nonneg _) hchi
    _ = ((Ico 1 m).card : ℝ) := by simp
    _ ≤ (m : ℝ) := by
      rw [Nat.card_Ico]
      exact_mod_cast (Nat.sub_le m 1)

/-- Total discrepancy bound: short floor error plus the oscillatory long tail. -/
theorem IsPrimitive.abs_quadraticSiegelConvolutionDiscrepancy_le
    {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)
    (hq : 1 < q) {m X : ℕ} (hm : 1 ≤ m) (hmX : m ≤ X) :
    |quadraticSiegelConvolutionDiscrepancy χ X m| ≤
      (m : ℝ) +
        (8 * Real.sqrt q * (1 + Real.log q)) * ((X / m : ℕ) : ℝ) := by
  have hunion : Icc 1 X = Ico 1 m ∪ Icc m X := by
    ext d
    simp only [mem_Icc, mem_union, mem_Ico]
    omega
  have hdisj : Disjoint (Ico 1 m) (Icc m X) := by
    rw [Finset.disjoint_left]
    intro d hd1 hd2
    rw [mem_Ico] at hd1
    rw [mem_Icc] at hd2
    omega
  have hD :
      quadraticSiegelConvolutionDiscrepancy χ X m =
        (∑ d ∈ Ico 1 m,
          (((X / d : ℕ) : ℝ) * (χ d).re -
            (X : ℝ) * ((χ d).re / (d : ℝ)))) +
        ∑ d ∈ Icc m X, ((X / d : ℕ) : ℝ) * (χ d).re := by
    rw [quadraticSiegelConvolutionDiscrepancy_eq_floorSum_sub, hunion,
      Finset.sum_union hdisj, Finset.mul_sum]
    rw [Finset.sum_sub_distrib]
    ring
  rw [hD]
  calc
    |(∑ d ∈ Ico 1 m,
          (((X / d : ℕ) : ℝ) * (χ d).re -
            (X : ℝ) * ((χ d).re / (d : ℝ)))) +
        ∑ d ∈ Icc m X, ((X / d : ℕ) : ℝ) * (χ d).re| ≤
      |∑ d ∈ Ico 1 m,
          (((X / d : ℕ) : ℝ) * (χ d).re -
            (X : ℝ) * ((χ d).re / (d : ℝ)))| +
        |∑ d ∈ Icc m X, ((X / d : ℕ) : ℝ) * (χ d).re| := abs_add_le _ _
    _ ≤ (m : ℝ) +
        (8 * Real.sqrt q * (1 + Real.log q)) * ((X / m : ℕ) : ℝ) := by
      gcongr
      · exact abs_quadratic_shortFloorError_le χ X m
      · exact hχ.abs_floorWeighted_character_tail_le hq hm hmX


end DirichletCharacter