/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nous Research
-/
import MathlibNt.AnalyticNumberTheory.Chen1973.Chen1973Lemma6M2Bound

/-!
# Chen 1973, Lemma 6, equation (12)

This module performs the finite, source-faithful part of (12).  In particular
`chen1973Lemma6ActualPhi` is the switched von-Mangoldt/Perron kernel itself; no
free function called `Phi` occurs in any statement below.  The unconditional
Bromwich theorem imported through Lemma 5 identifies every occurrence of
`chen1973PerronKernelFinite` with Chen's vertical integral.

The paper subsequently replaces `1 / φ(l)` by `O(log x / l)` and pays the
outer squarefree `3^ν/φ` sum by `O((log x)^5)`.  These two scalar estimates are
kept as two separately typed inequalities in the final theorem, rather than
being hidden in a hypothesis having equation (12) itself as its conclusion.
-/

noncomputable section

open Classical Complex Finset
open scoped BigOperators ArithmeticFunction

namespace AnalyticNumberTheory.LargeSieve

/-- The actual `Φ(x/(p₁p₂),χ)` after unconditional Bromwich inversion: it is
the finite switched `Λ(n)` sum with Chen's literal Perron kernel.  The source's
factor `1 / log(x/(p₁p₂))` is *outside* `Φ` in (12), so it is deliberately not
part of this definition. -/
def chen1973Lemma6ActualPhi (x d : ℕ) (χ : PrimitiveCharacter d)
    (pp : ℕ × ℕ) : ℂ :=
  ∑ n ∈ chen1973Lemma5NCarrier x pp,
    ((ArithmeticFunction.vonMangoldt n : ℝ) *
      chen1973PerronKernelFinite (x : ℝ)
        ((x : ℝ) / ((pp.1 : ℝ) * pp.2 * n)) : ℂ) * χ.1 (n : ZMod d)

/-- Regroup the actual primitive twist by prime pairs.  This is the finite
counterpart of inserting the unconditional Bromwich formula; no interchange
of conditionally convergent infinite sums is involved. -/
theorem chen1973Lemma6_primitiveTwist_eq_actualPhi
    (x d : ℕ) (χ : PrimitiveCharacter d) :
    chen1973Lemma5PrimitiveTwist x d χ =
      star (χ.1 (x : ZMod d)) *
        ∑ pp ∈ chen1973Lemma5PrimePairs x,
          (Real.log ((x : ℝ) / ((pp.1 : ℝ) * pp.2)))⁻¹ *
            chen1973Lemma6ActualPhi x d χ pp *
            χ.1 ((pp.1 * pp.2 : ℕ) : ZMod d) := by
  classical
  unfold chen1973Lemma5PrimitiveTwist chen1973Lemma6ActualPhi
  congr 1
  apply Finset.sum_congr rfl
  intro pp hpp
  rw [mul_assoc, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have hcast : ((pp.1 * pp.2 * n : ℕ) : ZMod d) =
      ((pp.1 * pp.2 : ℕ) : ZMod d) * (n : ZMod d) := by
    norm_cast
  rw [hcast, map_mul]
  unfold chen1973Lemma5SmoothedWeight
  push_cast
  ring

/-- The same finite Bromwich regrouping after retaining exactly the source
prime-pair condition `(p₁p₂,d)=1`. -/
theorem chen1973Lemma6_primitiveTwistCoprime_eq_actualPhi
    (x l d : ℕ) (χ : PrimitiveCharacter l) :
    chen1973Lemma5PrimitiveTwistCoprime x l d χ =
      star (χ.1 (x : ZMod l)) *
        ∑ pp ∈ (chen1973Lemma5PrimePairs x).filter
            (fun pp => Nat.Coprime (pp.1 * pp.2) d),
          (Real.log ((x : ℝ) / ((pp.1 : ℝ) * pp.2)))⁻¹ *
            chen1973Lemma6ActualPhi x l χ pp *
            χ.1 ((pp.1 * pp.2 : ℕ) : ZMod l) := by
  classical
  unfold chen1973Lemma5PrimitiveTwistCoprime chen1973Lemma6ActualPhi
  congr 1
  apply Finset.sum_congr rfl
  intro pp hpp
  rw [mul_assoc, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have hcast : ((pp.1 * pp.2 * n : ℕ) : ZMod l) =
      ((pp.1 * pp.2 : ℕ) : ZMod l) * (n : ZMod l) := by
    norm_cast
  rw [hcast, map_mul]
  unfold chen1973Lemma5SmoothedWeight
  push_cast
  ring

/-- The conductor expression before the paper replaces `φ(l)` by `l/log x`.
The parameter `m` is exactly the source coprimality grouping
`(p₁p₂,m)=1`. -/
def chen1973Lemma6NmTotient (x D m : ℕ) : ℝ :=
  ∑ l ∈ (Finset.range (D + 1)).filter
      (fun l => Nat.Coprime l x ∧ Squarefree l),
    ((ArithmeticFunction.moebius l : ℤ) : ℝ) ^ 2 *
      (3 : ℝ) ^ l.primeFactors.card / Nat.totient l *
      ‖∑ χ : PrimitiveCharacter l,
        if χ.1 = 1 then 0 else
          star (χ.1 (x : ZMod l)) *
            ∑ pp ∈ (chen1973Lemma5PrimePairs x).filter
                (fun pp => Nat.Coprime (pp.1 * pp.2) m),
              (Real.log ((x : ℝ) / ((pp.1 : ℝ) * pp.2)))⁻¹ *
                chen1973Lemma6ActualPhi x l χ pp *
                χ.1 ((pp.1 * pp.2 : ℕ) : ZMod l)‖

/-- The literal `N_m` weight printed after (12), with `l` rather than
`φ(l)` in the denominator. -/
def chen1973Lemma6Nm (x D m : ℕ) : ℝ :=
  ∑ l ∈ (Finset.range (D + 1)).filter
      (fun l => Nat.Coprime l x ∧ Squarefree l),
    |((ArithmeticFunction.moebius l : ℤ) : ℝ)| *
      (3 : ℝ) ^ l.primeFactors.card / l *
      ‖∑ χ : PrimitiveCharacter l,
        if χ.1 = 1 then 0 else
          star (χ.1 (x : ZMod l)) *
            ∑ pp ∈ (chen1973Lemma5PrimePairs x).filter
                (fun pp => Nat.Coprime (pp.1 * pp.2) m),
              (Real.log ((x : ℝ) / ((pp.1 : ℝ) * pp.2)))⁻¹ *
                chen1973Lemma6ActualPhi x l χ pp *
                χ.1 ((pp.1 * pp.2 : ℕ) : ZMod l)‖

/-- A total finite maximum over the printed range `1 < m ≤ M`.
The modulus cutoff `D` in `N_m` and the upper endpoint `M` of the maximum are
kept separate: on p. 119 they are respectively `x^(1/2-ε)` and `x^(1/2)`.
Inserting `0` makes the definition total when that range is empty. -/
def chen1973Lemma6NmMax (x D M : ℕ) : ℝ :=
  ({0} ∪ (Finset.Icc 2 M).image (chen1973Lemma6Nm x D)).max'
    (by simp)

theorem chen1973Lemma6Nm_le_max {x D M m : ℕ} (hm : 2 ≤ m) (hmM : m ≤ M) :
    chen1973Lemma6Nm x D m ≤ chen1973Lemma6NmMax x D M := by
  unfold chen1973Lemma6NmMax
  apply Finset.le_max'
  simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_image]
  exact Or.inr ⟨m, by simp [hm, hmM], rfl⟩

theorem chen1973Lemma6NmMax_nonneg (x D M : ℕ) :
    0 ≤ chen1973Lemma6NmMax x D M := by
  unfold chen1973Lemma6NmMax
  apply Finset.le_max'
  simp

/-- This identity is valid only under the deliberately strong hypothesis that
one fixed `m` is coprime to every prime pair.  It is not the outer-`d`
regrouping used in equation (12). -/
theorem chen1973Lemma5M2_eq_NmTotient_of_allPrimePairsCoprime
    {x D m : ℕ}
    (hpair : ∀ pp ∈ chen1973Lemma5PrimePairs x,
      Nat.Coprime (pp.1 * pp.2) m) :
    chen1973Lemma5M2 x D = chen1973Lemma6NmTotient x D m := by
  classical
  unfold chen1973Lemma5M2 chen1973Lemma5M2InnerMajorant
    chen1973Lemma6NmTotient
  apply Finset.sum_congr rfl
  intro l hl
  congr 1
  apply congrArg norm
  apply Finset.sum_congr rfl
  intro χ hχ
  split_ifs with hprincipal
  · rfl
  rw [chen1973Lemma6_primitiveTwist_eq_actualPhi]
  rw [Finset.filter_eq_self.2 (fun pp hpp => hpair pp hpp)]

/-- The genuine outer `d` carrier immediately before (12), reusing the
Lemma-5 source definition rather than introducing a second carrier. -/
def chen1973Lemma6OuterDivisors (x D : ℕ) : Finset ℕ :=
  chen1973Lemma5M2OuterDivisors x D

/-- The p. 119 outer weight `3^ν(d)|μ(d)|/φ(d)`. -/
def chen1973Lemma6OuterWeight (d : ℕ) : ℝ :=
  chen1973Lemma5M2OuterWeight d

theorem chen1973Lemma6OuterWeight_nonneg (d : ℕ) :
    0 ≤ chen1973Lemma6OuterWeight d := by
  unfold chen1973Lemma6OuterWeight chen1973Lemma5M2OuterWeight
  positivity

/-- At a fixed outer divisor, the Lemma-5 inner source is exactly the
totient-denominator `N_d` ledger used before equation (12). -/
theorem chen1973Lemma5M2SourceInner_eq_NmTotient (x D d : ℕ) :
    chen1973Lemma5M2SourceInner x D d = chen1973Lemma6NmTotient x D d := by
  classical
  unfold chen1973Lemma5M2SourceInner chen1973Lemma6NmTotient
  simp_rw [chen1973Lemma6_primitiveTwistCoprime_eq_actualPhi]

/-- The expression after the true outer-`d` regrouping and before replacing
the inner reciprocal totient by the literal reciprocal modulus in `N_d`. -/
def chen1973Lemma6OuterTotientSum (x D : ℕ) : ℝ :=
  ∑ d ∈ chen1973Lemma6OuterDivisors x D,
    chen1973Lemma6OuterWeight d * chen1973Lemma6NmTotient x D d

/-- The true p. 119 outer grouping is unconditional: both sides are the same
outer-`d` / inner-`l` source, with `(p₁p₂,d)=1` retained before norms. -/
theorem chen1973Lemma5M2Source_eq_outerTotientSum (x D : ℕ) :
    chen1973Lemma5M2Source x D = chen1973Lemma6OuterTotientSum x D := by
  classical
  unfold chen1973Lemma5M2Source chen1973Lemma6OuterTotientSum
    chen1973Lemma6OuterDivisors chen1973Lemma6OuterWeight
  simp_rw [chen1973Lemma5M2SourceInner_eq_NmTotient]

/-- The same outer grouping after the pointwise totient-to-modulus estimate. -/
def chen1973Lemma6OuterLiteralSum (x D : ℕ) : ℝ :=
  ∑ d ∈ chen1973Lemma6OuterDivisors x D,
    chen1973Lemma6OuterWeight d * chen1973Lemma6Nm x D d

/-- Total p. 119 outer weight, estimated there by `O((log x)^5)`. -/
def chen1973Lemma6OuterWeightSum (x D : ℕ) : ℝ :=
  ∑ d ∈ chen1973Lemma6OuterDivisors x D, chen1973Lemma6OuterWeight d

/-- The genuine source regrouping proposition preceding (12).  It is a proved
fact, not a caller-supplied equation-(12) hypothesis. -/
def Chen1973Equation12OuterGrouping (x D : ℕ) : Prop :=
  chen1973Lemma5M2Source x D = chen1973Lemma6OuterTotientSum x D

theorem chen1973Lemma6_outerGrouping (x D : ℕ) :
    Chen1973Equation12OuterGrouping x D :=
  chen1973Lemma5M2Source_eq_outerTotientSum x D

/-- Source equation (12), consuming the two-layer source object and conditional
only on the two scalar estimates printed immediately after the now-proved
outer grouping: the pointwise
`φ(l)`-to-`l` replacement and the total outer-weight bound.  No single `m` is
chosen uniformly for all prime pairs. -/
theorem chen1973Lemma6_equation12_of_outerGrouping
    {x D M : ℕ} (hx : 1 ≤ x) (hDM : D ≤ M)
    (htotient : ∀ d ∈ chen1973Lemma6OuterDivisors x D,
      chen1973Lemma6NmTotient x D d ≤ Real.log x * chen1973Lemma6Nm x D d)
    (hweight : chen1973Lemma6OuterWeightSum x D ≤ Real.log x ^ 5) :
    chen1973Lemma5M2Source x D ≤
      Real.log x ^ 6 * chen1973Lemma6NmMax x D M := by
  have hlog : 0 ≤ Real.log x := Real.log_nonneg (by exact_mod_cast hx)
  have htotientSum :
      chen1973Lemma6OuterTotientSum x D ≤
        Real.log x * chen1973Lemma6OuterLiteralSum x D := by
    unfold chen1973Lemma6OuterTotientSum chen1973Lemma6OuterLiteralSum
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro d hd
    calc
      chen1973Lemma6OuterWeight d * chen1973Lemma6NmTotient x D d ≤
          chen1973Lemma6OuterWeight d *
            (Real.log x * chen1973Lemma6Nm x D d) :=
        mul_le_mul_of_nonneg_left (htotient d hd)
          (chen1973Lemma6OuterWeight_nonneg d)
      _ = Real.log x *
          (chen1973Lemma6OuterWeight d * chen1973Lemma6Nm x D d) := by ring
  have hliteralMax :
      chen1973Lemma6OuterLiteralSum x D ≤
        chen1973Lemma6OuterWeightSum x D * chen1973Lemma6NmMax x D M := by
    unfold chen1973Lemma6OuterLiteralSum chen1973Lemma6OuterWeightSum
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro d hd
    have hdmem := (Finset.mem_filter.mp hd).1
    have hdIcc := Finset.mem_Icc.mp hdmem
    exact mul_le_mul_of_nonneg_left
      (chen1973Lemma6Nm_le_max hdIcc.1 (hdIcc.2.trans hDM))
      (chen1973Lemma6OuterWeight_nonneg d)
  calc
    chen1973Lemma5M2Source x D ≤ chen1973Lemma6OuterTotientSum x D :=
      (chen1973Lemma5M2Source_eq_outerTotientSum x D).le
    _ ≤ Real.log x * chen1973Lemma6OuterLiteralSum x D := htotientSum
    _ ≤ Real.log x *
        (chen1973Lemma6OuterWeightSum x D * chen1973Lemma6NmMax x D M) :=
      mul_le_mul_of_nonneg_left hliteralMax hlog
    _ ≤ Real.log x *
        (Real.log x ^ 5 * chen1973Lemma6NmMax x D M) := by
      apply mul_le_mul_of_nonneg_left _ hlog
      exact mul_le_mul_of_nonneg_right hweight (chen1973Lemma6NmMax_nonneg x D M)
    _ = Real.log x ^ 6 * chen1973Lemma6NmMax x D M := by ring

end AnalyticNumberTheory.LargeSieve