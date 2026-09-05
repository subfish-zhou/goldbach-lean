

import MathlibNt.AnalyticNumberTheory.LargeSieve.BombieriDavenport
import MathlibNt.AnalyticNumberTheory.Vaughan.ActualVaughanTypeIIBlockOrdinaryLS

/-!
 # Rank-one rectangular primitive L¹ means

This leaf separates the elementary rectangular part of a Type-II first moment
from the genuinely hyperbolic prefix problem.  A rank-one rectangle is paid by
two one-dimensional weighted primitive large sieves and one Cauchy--Schwarz
inequality.  The sole remaining interface says that an actual collected
Vaughan hyperbolic shell is dominated by finitely many such rectangles.

This module is intentionally not imported by a canonical facade.
-/

namespace AnalyticNumberTheory.LargeSieve

open Classical Finset
open scoped BigOperators

noncomputable section

/-- Weighted primitive first moment of a rank-one rectangular character sum.
The conductor set is explicit so the same theorem applies to one production
conductor block. -/
def rankOneRectangularWeightedPrimitiveMean
    (a b : ℤ → ℂ) (Ma Mb : ℤ) (Na Nb : ℕ) (S : Finset ℕ) : ℝ :=
  ∑ q ∈ S, ((q : ℝ) / (q.totient : ℝ)) *
    ∑ χ : PrimitiveCharacter q,
      ‖∑ m ∈ Finset.Icc (Ma + 1) (Ma + Na),
          a m * χ.1 (m : ZMod q)‖ *
        ‖∑ n ∈ Finset.Icc (Mb + 1) (Mb + Nb),
          b n * χ.1 (n : ZMod q)‖

lemma rankOneRectangularWeightedPrimitiveMean_nonneg
    (a b : ℤ → ℂ) (Ma Mb : ℤ) (Na Nb : ℕ) (S : Finset ℕ) :
    0 ≤ rankOneRectangularWeightedPrimitiveMean a b Ma Mb Na Nb S := by
  unfold rankOneRectangularWeightedPrimitiveMean
  positivity

/-- The elementary rectangular theorem.  After flattening the finite dependent
family `(q,χ)`, Cauchy gives two square ledgers; each is exactly one invocation
of the one-dimensional weighted primitive large sieve. -/
theorem rankOneRectangularWeightedPrimitiveMean_sq_le
    (a b : ℤ → ℂ) (Ma Mb : ℤ) (Na Nb Q : ℕ) (hQ : 0 < Q)
    (S : Finset ℕ) (hS : S ⊆ Finset.Icc 1 Q) :
    rankOneRectangularWeightedPrimitiveMean a b Ma Mb Na Nb S ^ 2 ≤
      (largeSieveBound Na (1 / (Q : ℝ) ^ 2) *
        ∑ m ∈ Finset.Icc (Ma + 1) (Ma + Na), ‖a m‖ ^ 2) *
      (largeSieveBound Nb (1 / (Q : ℝ) ^ 2) *
        ∑ n ∈ Finset.Icc (Mb + 1) (Mb + Nb), ‖b n‖ ^ 2) := by
  let w : ℕ → ℝ := fun q => (q : ℝ) / (q.totient : ℝ)
  let A : (q : ℕ) → PrimitiveCharacter q → ℝ := fun q χ =>
    ‖∑ m ∈ Finset.Icc (Ma + 1) (Ma + Na), a m * χ.1 (m : ZMod q)‖
  let B : (q : ℕ) → PrimitiveCharacter q → ℝ := fun q χ =>
    ‖∑ n ∈ Finset.Icc (Mb + 1) (Mb + Nb), b n * χ.1 (n : ZMod q)‖
  let T := S.sigma (fun q => (Finset.univ : Finset (PrimitiveCharacter q)))
  have hflat : rankOneRectangularWeightedPrimitiveMean a b Ma Mb Na Nb S =
      ∑ x ∈ T, (Real.sqrt (w x.1)) * A x.1 x.2 *
        ((Real.sqrt (w x.1)) * B x.1 x.2) := by
    unfold rankOneRectangularWeightedPrimitiveMean
    dsimp [T]
    rw [Finset.sum_sigma]
    apply Finset.sum_congr rfl
    intro q hq
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro χ hχ
    have hw : 0 ≤ w q := by dsimp [w]; positivity
    calc
      ((q : ℝ) / (q.totient : ℝ)) * (A q χ * B q χ) =
          (Real.sqrt (w q) * Real.sqrt (w q)) * (A q χ * B q χ) := by
            rw [Real.mul_self_sqrt hw]
      _ = Real.sqrt (w q) * A q χ * (Real.sqrt (w q) * B q χ) := by ring
  rw [hflat]
  refine (Finset.sum_mul_sq_le_sq_mul_sq T
    (fun x => Real.sqrt (w x.1) * A x.1 x.2)
    (fun x => Real.sqrt (w x.1) * B x.1 x.2)).trans ?_
  have hAflat :
      (∑ x ∈ T, (Real.sqrt (w x.1) * A x.1 x.2) ^ 2) =
        ∑ q ∈ S, w q * ∑ χ : PrimitiveCharacter q, A q χ ^ 2 := by
    dsimp [T]
    rw [Finset.sum_sigma]
    apply Finset.sum_congr rfl
    intro q hq
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro χ hχ
    have hw : 0 ≤ w q := by dsimp [w]; positivity
    rw [mul_pow, Real.sq_sqrt hw]
  have hBflat :
      (∑ x ∈ T, (Real.sqrt (w x.1) * B x.1 x.2) ^ 2) =
        ∑ q ∈ S, w q * ∑ χ : PrimitiveCharacter q, B q χ ^ 2 := by
    dsimp [T]
    rw [Finset.sum_sigma]
    apply Finset.sum_congr rfl
    intro q hq
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro χ hχ
    have hw : 0 ≤ w q := by dsimp [w]; positivity
    rw [mul_pow, Real.sq_sqrt hw]
  rw [hAflat, hBflat]
  apply mul_le_mul
  · calc
      (∑ q ∈ S, w q * ∑ χ : PrimitiveCharacter q, A q χ ^ 2) ≤
          ∑ q ∈ Finset.Icc 1 Q,
            w q * ∑ χ : PrimitiveCharacter q, A q χ ^ 2 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hS
        intro q hq hnot
        exact mul_nonneg (by dsimp [w]; positivity)
          (Finset.sum_nonneg fun χ hχ => sq_nonneg _)
      _ ≤ largeSieveBound Na (1 / (Q : ℝ) ^ 2) *
          ∑ m ∈ Finset.Icc (Ma + 1) (Ma + Na), ‖a m‖ ^ 2 := by
        simpa [w, A] using weighted_primitive_bombieri_davenport a Ma Na Q hQ
  · calc
      (∑ q ∈ S, w q * ∑ χ : PrimitiveCharacter q, B q χ ^ 2) ≤
          ∑ q ∈ Finset.Icc 1 Q,
            w q * ∑ χ : PrimitiveCharacter q, B q χ ^ 2 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hS
        intro q hq hnot
        exact mul_nonneg (by dsimp [w]; positivity)
          (Finset.sum_nonneg fun χ hχ => sq_nonneg _)
      _ ≤ largeSieveBound Nb (1 / (Q : ℝ) ^ 2) *
          ∑ n ∈ Finset.Icc (Mb + 1) (Mb + Nb), ‖b n‖ ^ 2 := by
        simpa [w, B] using weighted_primitive_bombieri_davenport b Mb Nb Q hQ
  · exact Finset.sum_nonneg fun q hq => mul_nonneg (by dsimp [w]; positivity)
      (Finset.sum_nonneg fun χ hχ => sq_nonneg _)
  · unfold largeSieveBound
    positivity

/-- Unsquared form convenient for finite shell assembly. -/
theorem rankOneRectangularWeightedPrimitiveMean_le
    (a b : ℤ → ℂ) (Ma Mb : ℤ) (Na Nb Q : ℕ) (hQ : 0 < Q)
    (S : Finset ℕ) (hS : S ⊆ Finset.Icc 1 Q) :
    rankOneRectangularWeightedPrimitiveMean a b Ma Mb Na Nb S ≤
      Real.sqrt (largeSieveBound Na (1 / (Q : ℝ) ^ 2) *
        ∑ m ∈ Finset.Icc (Ma + 1) (Ma + Na), ‖a m‖ ^ 2) *
      Real.sqrt (largeSieveBound Nb (1 / (Q : ℝ) ^ 2) *
        ∑ n ∈ Finset.Icc (Mb + 1) (Mb + Nb), ‖b n‖ ^ 2) := by
  have hs := rankOneRectangularWeightedPrimitiveMean_sq_le
    a b Ma Mb Na Nb Q hQ S hS
  have hA : 0 ≤ largeSieveBound Na (1 / (Q : ℝ) ^ 2) *
      ∑ m ∈ Finset.Icc (Ma + 1) (Ma + Na), ‖a m‖ ^ 2 := by
    unfold largeSieveBound
    positivity
  have hB : 0 ≤ largeSieveBound Nb (1 / (Q : ℝ) ^ 2) *
      ∑ n ∈ Finset.Icc (Mb + 1) (Mb + Nb), ‖b n‖ ^ 2 := by
    unfold largeSieveBound
    positivity
  have hright : 0 ≤
      Real.sqrt (largeSieveBound Na (1 / (Q : ℝ) ^ 2) *
        ∑ m ∈ Finset.Icc (Ma + 1) (Ma + Na), ‖a m‖ ^ 2) *
      Real.sqrt (largeSieveBound Nb (1 / (Q : ℝ) ^ 2) *
        ∑ n ∈ Finset.Icc (Mb + 1) (Mb + Nb), ‖b n‖ ^ 2) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  apply (sq_le_sq₀ (rankOneRectangularWeightedPrimitiveMean_nonneg
    a b Ma Mb Na Nb S) hright).mp
  rw [mul_pow, Real.sq_sqrt hA, Real.sq_sqrt hB]
  exact hs

/-- The unique analytic residual: separation of one actual hyperbolic collected
shell into finitely many rank-one rectangles.  Everything after this interface
is the proved rectangular theorem above and finite summation. -/
def VaughanTypeIIHyperbolicSeparation
    {ι : Type*} [Fintype ι]
    (N u v k l : ℕ) (S : Finset ℕ)
    (left right : ι → ℤ → ℂ) (leftStart rightStart : ι → ℤ)
    (leftLength rightLength : ι → ℕ) : Prop :=
  blockWeightedVaughanActualCollectedShellMean N u v k l S ≤
    ∑ i : ι, rankOneRectangularWeightedPrimitiveMean
      (left i) (right i) (leftStart i) (rightStart i)
      (leftLength i) (rightLength i) S

/-- A separated actual shell is paid solely by the two one-dimensional large
sieves for each rank-one rectangle. -/
theorem blockWeightedVaughanActualCollectedShellMean_le_of_hyperbolicSeparation
    {ι : Type*} [Fintype ι]
    (N u v k l Q : ℕ) (hQ : 0 < Q) (S : Finset ℕ)
    (hS : S ⊆ Finset.Icc 1 Q)
    (left right : ι → ℤ → ℂ) (leftStart rightStart : ι → ℤ)
    (leftLength rightLength : ι → ℕ)
    (hsep : VaughanTypeIIHyperbolicSeparation N u v k l S
      left right leftStart rightStart leftLength rightLength) :
    blockWeightedVaughanActualCollectedShellMean N u v k l S ≤
      ∑ i : ι,
        Real.sqrt (largeSieveBound (leftLength i) (1 / (Q : ℝ) ^ 2) *
          ∑ m ∈ Finset.Icc (leftStart i + 1) (leftStart i + leftLength i),
            ‖left i m‖ ^ 2) *
        Real.sqrt (largeSieveBound (rightLength i) (1 / (Q : ℝ) ^ 2) *
          ∑ n ∈ Finset.Icc (rightStart i + 1) (rightStart i + rightLength i),
            ‖right i n‖ ^ 2) := by
  refine hsep.trans ?_
  exact Finset.sum_le_sum fun i hi =>
    rankOneRectangularWeightedPrimitiveMean_le
      (left i) (right i) (leftStart i) (rightStart i)
      (leftLength i) (rightLength i) Q hQ S hS

/-- Connection to the actual Vaughan fixed-conductor-block L¹ mean.  The only
premise not discharged by existing finite decomposition or one-dimensional
large sieve is `VaughanTypeIIHyperbolicSeparation`, once for each active shell. -/
theorem exactVaughanTypeII_blockWeighted_mean_le_of_hyperbolicSeparation
    {ι : Type*} [Fintype ι]
    (N u v Q : ℕ) (hQ : 0 < Q) (S : Finset ℕ)
    (hS : S ⊆ Finset.Icc 1 Q)
    (left right : ℕ × ℕ → ι → ℤ → ℂ)
    (leftStart rightStart : ℕ × ℕ → ι → ℤ)
    (leftLength rightLength : ℕ × ℕ → ι → ℕ)
    (hsep : ∀ kl ∈ vaughanTypeIIActiveCanonicalRectangles N u v,
      VaughanTypeIIHyperbolicSeparation N u v kl.1 kl.2 S
        (left kl) (right kl) (leftStart kl) (rightStart kl)
        (leftLength kl) (rightLength kl)) :
    typeIIBlockWeightedPrimitiveMean
        (vaughanTypeIICoeff vaughanUnitIntegerCoeff u v) N S ≤
      ∑ kl ∈ vaughanTypeIIActiveCanonicalRectangles N u v,
        ∑ i : ι,
          Real.sqrt (largeSieveBound (leftLength kl i) (1 / (Q : ℝ) ^ 2) *
            ∑ m ∈ Finset.Icc (leftStart kl i + 1)
              (leftStart kl i + leftLength kl i), ‖left kl i m‖ ^ 2) *
          Real.sqrt (largeSieveBound (rightLength kl i) (1 / (Q : ℝ) ^ 2) *
            ∑ n ∈ Finset.Icc (rightStart kl i + 1)
              (rightStart kl i + rightLength kl i), ‖right kl i n‖ ^ 2) := by
  refine (blockWeightedExactVaughanTypeII_le_active_collected_shells N u v S).trans ?_
  apply Finset.sum_le_sum
  intro kl hkl
  exact blockWeightedVaughanActualCollectedShellMean_le_of_hyperbolicSeparation
    N u v kl.1 kl.2 Q hQ S hS
    (left kl) (right kl) (leftStart kl) (rightStart kl)
    (leftLength kl) (rightLength kl) (hsep kl hkl)

end

end AnalyticNumberTheory.LargeSieve
