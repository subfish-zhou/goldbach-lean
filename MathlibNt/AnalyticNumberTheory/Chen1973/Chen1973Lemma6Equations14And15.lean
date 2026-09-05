/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nous Research
-/
import MathlibNt.AnalyticNumberTheory.Chen1973.Chen1973Lemma6M2Bound
import MathlibNt.AnalyticNumberTheory.Chen1973.Chen1973Lemma3LFourthMoment

/-!
# Chen 1973, Lemma 6, equations (14) and (15)

This file freezes the finite algebra on p. 120.  All Dirichlet polynomials use
natural order.  In particular, no conditionally convergent `tsum` is used.
Equation (14) is separated into its finite large-sieve term and the literal
truncation remainder.  Equation (15) is the fourth moment of the finite
Möbius polynomial.  The final two results record the actual unconditional
Lemma 3 calls needed on the adjacent Cauchy circle.
-/

noncomputable section

open Classical Complex Finset
open scoped BigOperators ArithmeticFunction

namespace AnalyticNumberTheory.LargeSieve

/-- Chen's natural-order polynomial `S(H,s,χ)`. -/
abbrev chen1973Lemma6NaturalMobiusPolynomial {d : ℕ} (H : ℕ) (s : ℂ)
    (χ : PrimitiveCharacter d) : ℂ :=
  chen1973Lemma6MobiusPartialSum H s χ

/-- The natural-order truncation of `L(s,χ)` used on p. 120. -/
def chen1973Lemma6NaturalLPolynomial {d : ℕ} (H : ℕ) (s : ℂ)
    (χ : PrimitiveCharacter d) : ℂ :=
  ∑ n ∈ Icc 1 H, (n : ℂ) ^ (-s) * χ.1 (n : ZMod d)

/-- The actual expression `1-L(s,χ)S(H,s,χ)`. -/
def chen1973Lemma6OneSubLS {d : ℕ} (H : ℕ) (s : ℂ)
    (χ : PrimitiveCharacter d) : ℂ :=
  1 - chen1973PrimitiveLValue d s χ *
    chen1973Lemma6NaturalMobiusPolynomial H s χ

/-- A generic finite product coefficient.  Keeping the two cpow factors here
avoids any appeal to an infinite Dirichlet-series product. -/
def chen1973Lemma6ProductCoefficient (H : ℕ) (A B : ℕ → ℂ) (m : ℤ) : ℂ :=
  ∑ ab ∈ (Icc 1 H).product (Icc 1 H),
    if (ab.1 * ab.2 : ℤ) = m then A ab.1 * B ab.2 else 0

/-- Exact collection of a product of two natural-order finite polynomials. -/
theorem chen1973Lemma6_product_sum_eq_collected
    (H : ℕ) (A B : ℕ → ℂ) {d : ℕ} (χ : PrimitiveCharacter d) :
    (∑ a ∈ Icc 1 H, A a * χ.1 (a : ZMod d)) *
        (∑ b ∈ Icc 1 H, B b * χ.1 (b : ZMod d)) =
      ∑ m ∈ Icc (1 : ℤ) (H * H : ℕ),
        chen1973Lemma6ProductCoefficient H A B m * χ.1 (m : ZMod d) := by
  calc
    _ = ∑ ab ∈ (Icc 1 H).product (Icc 1 H),
        (A ab.1 * χ.1 (ab.1 : ZMod d)) *
          (B ab.2 * χ.1 (ab.2 : ZMod d)) := by
      rw [Finset.sum_mul]
      simp_rw [Finset.mul_sum]
      exact (Finset.sum_product (Icc 1 H) (Icc 1 H)
        (fun ab => (A ab.1 * χ.1 (ab.1 : ZMod d)) *
          (B ab.2 * χ.1 (ab.2 : ZMod d)))).symm
    _ = ∑ ab ∈ (Icc 1 H).product (Icc 1 H),
        (A ab.1 * B ab.2) * χ.1 ((ab.1 * ab.2 : ℕ) : ZMod d) := by
      apply Finset.sum_congr rfl
      intro ab hab
      rw [show ((ab.1 * ab.2 : ℕ) : ZMod d) =
        (ab.1 : ZMod d) * (ab.2 : ZMod d) by norm_num, map_mul]
      ring
    _ = _ := by
      symm
      unfold chen1973Lemma6ProductCoefficient
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro ab hab
      have habm := Finset.mem_product.mp hab
      let p : ℤ := ab.1 * ab.2
      have hp : p ∈ Icc (1 : ℤ) (H * H : ℕ) :=
        chen1973_pair_product_mem habm.1 habm.2
      rw [Finset.sum_eq_single p]
      · simp [p]
      · intro m hm hmp
        have hne : (ab.1 * ab.2 : ℤ) ≠ m := by
          intro h
          apply hmp
          simpa [p] using h.symm
        simp [hne]
      · intro hnot
        exact False.elim (hnot hp)

/-- The finite coefficient `C_H(n)/n^s` in the product approximation to
`1-LS`.  It is deliberately a finite convolution. -/
def chen1973Lemma6CHWeightedCoefficient (H : ℕ) (s : ℂ) (m : ℤ) : ℂ :=
  (if m = 1 then 1 else 0) -
    chen1973Lemma6ProductCoefficient H
      (fun n => (n : ℂ) ^ (-s))
      (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ) / (n : ℂ) ^ s) m

/-- The p. 120 finite convolution identity. -/
theorem chen1973Lemma6_one_sub_finiteLS_eq_CH
    {H d : ℕ} (hH : 0 < H) (s : ℂ) (χ : PrimitiveCharacter d) :
    1 - chen1973Lemma6NaturalLPolynomial H s χ *
        chen1973Lemma6NaturalMobiusPolynomial H s χ =
      ∑ m ∈ Icc (1 : ℤ) (H * H : ℕ),
        chen1973Lemma6CHWeightedCoefficient H s m * χ.1 (m : ZMod d) := by
  have hone : (1 : ℤ) ∈ Icc (1 : ℤ) (H * H : ℕ) := by
    simp only [mem_Icc]
    constructor
    · rfl
    · exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hH.ne' hH.ne')
  have hdelta :
      (∑ m ∈ Icc (1 : ℤ) (H * H : ℕ),
        (if m = 1 then 1 else 0) * χ.1 (m : ZMod d)) = 1 := by
    rw [Finset.sum_eq_single 1]
    · simp
    · intro m hm hm1
      simp [hm1]
    · exact fun h => False.elim (h hone)
  have hprod := chen1973Lemma6_product_sum_eq_collected H
    (fun n => (n : ℂ) ^ (-s))
    (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ) / (n : ℂ) ^ s) χ
  unfold chen1973Lemma6NaturalLPolynomial
  unfold chen1973Lemma6NaturalMobiusPolynomial chen1973Lemma6MobiusPartialSum
  have hmob :
      (∑ n ∈ Icc 1 H,
        ((ArithmeticFunction.moebius n : ℤ) : ℂ) * χ.1 (n : ZMod d) / (n : ℂ) ^ s) =
      ∑ n ∈ Icc 1 H,
        (((ArithmeticFunction.moebius n : ℤ) : ℂ) / (n : ℂ) ^ s) *
          χ.1 (n : ZMod d) := by
    apply Finset.sum_congr rfl
    intro n hn
    ring
  rw [hmob]
  rw [hprod]
  rw [← hdelta]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro m hm
  unfold chen1973Lemma6CHWeightedCoefficient
  ring

/-- Exact decomposition of the actual `1-LS`: finite convolution minus the
literal finite-truncation remainder. -/
theorem chen1973Lemma6_oneSubLS_eq_CH_sub_remainder
    {H d : ℕ} (hH : 0 < H) (s : ℂ) (χ : PrimitiveCharacter d) :
    chen1973Lemma6OneSubLS H s χ =
      (∑ m ∈ Icc (1 : ℤ) (H * H : ℕ),
        chen1973Lemma6CHWeightedCoefficient H s m * χ.1 (m : ZMod d)) -
      (chen1973PrimitiveLValue d s χ -
        chen1973Lemma6NaturalLPolynomial H s χ) *
          chen1973Lemma6NaturalMobiusPolynomial H s χ := by
  rw [← chen1973Lemma6_one_sub_finiteLS_eq_CH hH]
  unfold chen1973Lemma6OneSubLS
  ring

/-- The coefficient `j(n)/n^s` in `S(H,s,χ)^2`. -/
def chen1973Lemma6MobiusSquareCoefficient (H : ℕ) (s : ℂ) (m : ℤ) : ℂ :=
  chen1973Lemma6ProductCoefficient H
    (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ) / (n : ℂ) ^ s)
    (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ) / (n : ℂ) ^ s) m

/-- Exact finite `j`-coefficient expansion used in (15). -/
theorem chen1973Lemma6_mobiusPolynomial_sq_eq_collected
    (H : ℕ) (s : ℂ) {d : ℕ} (χ : PrimitiveCharacter d) :
    chen1973Lemma6NaturalMobiusPolynomial H s χ ^ 2 =
      ∑ m ∈ Icc (1 : ℤ) (H * H : ℕ),
        chen1973Lemma6MobiusSquareCoefficient H s m * χ.1 (m : ZMod d) := by
  rw [pow_two]
  simpa [chen1973Lemma6MobiusSquareCoefficient,
    chen1973Lemma6NaturalMobiusPolynomial, chen1973Lemma6MobiusPartialSum,
    div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
    (chen1973Lemma6_product_sum_eq_collected H
      (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ) / (n : ℂ) ^ s)
      (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ) / (n : ℂ) ^ s) χ)

/-- Complex-coefficient form of Chen's equation (3).  The factor `2` is the
explicit cost of applying the real sharp large sieve to real and imaginary
parts. -/
theorem chen1973Lemma2_equationThree_complex_unconditional
    (c : ℤ → ℂ) (M : ℤ) (N D Q : ℕ) (hD : 0 < D) :
    ∃ C : ℝ, 0 < C ∧
      (∑ q ∈ Ioc D Q, (1 / (q.totient : ℝ)) *
        ∑ χ : PrimitiveCharacter q,
          ‖∑ n ∈ Icc (M + 1) (M + N), c n * χ.1 (n : ZMod q)‖ ^ 2) ≤
        2 * C * ((Q : ℝ) + (N : ℝ) / D) *
          ∑ n ∈ Icc (M + 1) (M + N), ‖c n‖ ^ 2 := by
  obtain ⟨C, hC, h3⟩ := chen1973Lemma2_equationThree_of_equationTwo
    (chen1973Lemma2_equationTwo_of_fareyEquationFour chen1973FareyEquationFour)
  refine ⟨C, hC, ?_⟩
  let aR : ℤ → ℝ := fun n => (c n).re
  let aI : ℤ → ℝ := fun n => (c n).im
  have hp (q : ℕ) (χ : PrimitiveCharacter q) :
      ‖∑ n ∈ Icc (M + 1) (M + N), c n * χ.1 (n : ZMod q)‖ ^ 2 ≤
        2 * (‖chen1973PrimitiveAmplitude aR M N q χ‖ ^ 2 +
          ‖chen1973PrimitiveAmplitude aI M N q χ‖ ^ 2) := by
    let AR := chen1973PrimitiveAmplitude aR M N q χ
    let AI := chen1973PrimitiveAmplitude aI M N q χ
    have heq : (∑ n ∈ Icc (M + 1) (M + N), c n * χ.1 (n : ZMod q)) =
        AR + I * AI := by
      dsimp [AR, AI, chen1973PrimitiveAmplitude]
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro n hn
      dsimp [aR, aI]
      calc
        c n * χ.1 (n : ZMod q) =
            (((c n).re : ℂ) + ((c n).im : ℂ) * I) * χ.1 (n : ZMod q) := by
              rw [Complex.re_add_im]
        _ = ((c n).re : ℂ) * χ.1 (n : ZMod q) +
            I * (((c n).im : ℂ) * χ.1 (n : ZMod q)) := by ring
    rw [heq]
    have h := norm_add_le AR (I * AI)
    have hI : ‖I * AI‖ = ‖AI‖ := by simp
    rw [hI] at h
    have hsquare : ‖AR + I * AI‖ ^ 2 ≤ (‖AR‖ + ‖AI‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h 2
    dsimp [AR, AI]
    nlinarith [sq_nonneg (‖AR‖ - ‖AI‖)]
  have hR := h3 aR M N D Q hD
  have hI := h3 aI M N D Q hD
  calc
    _ ≤ ∑ q ∈ Ioc D Q, (1 / (q.totient : ℝ)) *
        ∑ χ : PrimitiveCharacter q,
          2 * (‖chen1973PrimitiveAmplitude aR M N q χ‖ ^ 2 +
            ‖chen1973PrimitiveAmplitude aI M N q χ‖ ^ 2) := by
      apply Finset.sum_le_sum
      intro q hq
      exact mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum fun χ hχ => hp q χ) (by positivity)
    _ = 2 * ((∑ q ∈ Ioc D Q, (1 / (q.totient : ℝ)) *
          ∑ χ : PrimitiveCharacter q, ‖chen1973PrimitiveAmplitude aR M N q χ‖ ^ 2) +
        (∑ q ∈ Ioc D Q, (1 / (q.totient : ℝ)) *
          ∑ χ : PrimitiveCharacter q, ‖chen1973PrimitiveAmplitude aI M N q χ‖ ^ 2)) := by
      simp_rw [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum]
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib]
      have hmul (a b : ℝ) : a * (2 * b) = 2 * (a * b) := by ring
      simp_rw [hmul]
      rw [← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ 2 * (C * ((Q : ℝ) + (N : ℝ) / D) * chen1973CoefficientEnergy aR M N +
        C * ((Q : ℝ) + (N : ℝ) / D) * chen1973CoefficientEnergy aI M N) := by
      gcongr
    _ = 2 * C * ((Q : ℝ) + (N : ℝ) / D) *
        ∑ n ∈ Icc (M + 1) (M + N), ‖c n‖ ^ 2 := by
      unfold chen1973CoefficientEnergy
      rw [show 2 * C * ((Q : ℝ) + (N : ℝ) / D) *
          (∑ n ∈ Icc (M + 1) (M + N), ‖c n‖ ^ 2) =
        2 * (C * ((Q : ℝ) + (N : ℝ) / D) *
          ∑ n ∈ Icc (M + 1) (M + N), ‖c n‖ ^ 2) by ring]
      apply congrArg (fun z : ℝ => 2 * z)
      rw [← mul_add, ← Finset.sum_add_distrib]
      apply congrArg (fun z : ℝ => C * ((Q : ℝ) + (N : ℝ) / D) * z)
      apply Finset.sum_congr rfl
      intro n hn
      dsimp [aR, aI]
      rw [Complex.sq_norm]
      simp only [Complex.normSq_apply, sq_abs]
      ring

/-- Equation (14), finite large-sieve term.  This is an unconditional call to
Chen's sharp Lemma 2; `Re(s)≥1` is retained because it is the source range in
which the adjacent truncation theorem is used. -/
theorem chen1973Lemma6_equation14_finite_second_moment
    (H D Q : ℕ) (s : ℂ) (hD : 0 < D) (_hs : 1 ≤ s.re) :
    ∃ C : ℝ, 0 < C ∧
      (∑ d ∈ Ioc D Q, (1 / (d.totient : ℝ)) *
        ∑ χ : PrimitiveCharacter d,
          ‖∑ m ∈ Icc (1 : ℤ) (H * H : ℕ),
            chen1973Lemma6CHWeightedCoefficient H s m * χ.1 (m : ZMod d)‖ ^ 2) ≤
        2 * C * ((Q : ℝ) + ((H * H : ℕ) : ℝ) / D) *
          ∑ m ∈ Icc (1 : ℤ) (H * H : ℕ),
            ‖chen1973Lemma6CHWeightedCoefficient H s m‖ ^ 2 := by
  simpa using chen1973Lemma2_equationThree_complex_unconditional
    (chen1973Lemma6CHWeightedCoefficient H s) 0 (H * H) D Q hD

/-- The literal truncation-remainder ledger in (14).  This is not an
Eq. (14)-shaped assumption: it is the concrete error
`(L-P_H) S(H)` appearing in the exact convolution identity. -/
def chen1973Lemma6Equation14RemainderMoment
    (H D Q : ℕ) (s : ℂ) : ℝ :=
  ∑ d ∈ Ioc D Q, (1 / (d.totient : ℝ)) *
    ∑ χ : PrimitiveCharacter d,
      ‖(chen1973PrimitiveLValue d s χ -
          chen1973Lemma6NaturalLPolynomial H s χ) *
        chen1973Lemma6NaturalMobiusPolynomial H s χ‖ ^ 2

/-- Equation (14) with the actual `1-L(s,χ)S(H,s,χ)` on the left.  The sharp
Lemma 2 payment is internal; only the literal Abel-truncation remainder remains
visible for the subsequent p. 120 scalar estimate. -/
theorem chen1973Lemma6_equation14_weighted_second_moment
    (H D Q : ℕ) (s : ℂ) (hH : 0 < H) (hD : 0 < D) (hs : 1 ≤ s.re) :
    ∃ C : ℝ, 0 < C ∧
      (∑ d ∈ Ioc D Q, (1 / (d.totient : ℝ)) *
        ∑ χ : PrimitiveCharacter d,
          ‖chen1973Lemma6OneSubLS H s χ‖ ^ 2) ≤
        4 * C * ((Q : ℝ) + ((H * H : ℕ) : ℝ) / D) *
          (∑ m ∈ Icc (1 : ℤ) (H * H : ℕ),
            ‖chen1973Lemma6CHWeightedCoefficient H s m‖ ^ 2) +
        2 * chen1973Lemma6Equation14RemainderMoment H D Q s := by
  obtain ⟨C, hC, hfinite⟩ :=
    chen1973Lemma6_equation14_finite_second_moment H D Q s hD hs
  refine ⟨C, hC, ?_⟩
  let F : (d : ℕ) → PrimitiveCharacter d → ℂ := fun d χ =>
    ∑ m ∈ Icc (1 : ℤ) (H * H : ℕ),
      chen1973Lemma6CHWeightedCoefficient H s m * χ.1 (m : ZMod d)
  let R : (d : ℕ) → PrimitiveCharacter d → ℂ := fun d χ =>
    (chen1973PrimitiveLValue d s χ -
      chen1973Lemma6NaturalLPolynomial H s χ) *
        chen1973Lemma6NaturalMobiusPolynomial H s χ
  have hp (d : ℕ) (χ : PrimitiveCharacter d) :
      ‖chen1973Lemma6OneSubLS H s χ‖ ^ 2 ≤
        2 * ‖F d χ‖ ^ 2 + 2 * ‖R d χ‖ ^ 2 := by
    rw [chen1973Lemma6_oneSubLS_eq_CH_sub_remainder hH]
    change ‖F d χ - R d χ‖ ^ 2 ≤ _
    have hn := norm_sub_le (F d χ) (R d χ)
    have hsquare : ‖F d χ - R d χ‖ ^ 2 ≤
        (‖F d χ‖ + ‖R d χ‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hn 2
    nlinarith [sq_nonneg (‖F d χ‖ - ‖R d χ‖)]
  calc
    _ ≤ ∑ d ∈ Ioc D Q, (1 / (d.totient : ℝ)) *
        ∑ χ : PrimitiveCharacter d,
          (2 * ‖F d χ‖ ^ 2 + 2 * ‖R d χ‖ ^ 2) := by
      apply Finset.sum_le_sum
      intro d hd
      exact mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum fun χ hχ => hp d χ) (by positivity)
    _ = 2 * (∑ d ∈ Ioc D Q, (1 / (d.totient : ℝ)) *
          ∑ χ : PrimitiveCharacter d, ‖F d χ‖ ^ 2) +
        2 * chen1973Lemma6Equation14RemainderMoment H D Q s := by
      change _ = 2 * (∑ d ∈ Ioc D Q, (1 / (d.totient : ℝ)) *
          ∑ χ : PrimitiveCharacter d, ‖F d χ‖ ^ 2) +
        2 * (∑ d ∈ Ioc D Q, (1 / (d.totient : ℝ)) *
          ∑ χ : PrimitiveCharacter d, ‖R d χ‖ ^ 2)
      simp_rw [Finset.sum_add_distrib, mul_add, ← Finset.mul_sum]
      rw [Finset.sum_add_distrib]
      have hmul (a b : ℝ) : a * (2 * b) = 2 * (a * b) := by ring
      simp_rw [hmul]
      rw [← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ 2 * (2 * C * ((Q : ℝ) + ((H * H : ℕ) : ℝ) / D) *
          ∑ m ∈ Icc (1 : ℤ) (H * H : ℕ),
            ‖chen1973Lemma6CHWeightedCoefficient H s m‖ ^ 2) +
        2 * chen1973Lemma6Equation14RemainderMoment H D Q s := by
      gcongr
    _ = _ := by ring

/-- Equation (15): the actual fourth moment of the natural-order Möbius
polynomial, before the elementary `|j(n)|≤τ(n)` scalar simplification. -/
theorem chen1973Lemma6_equation15_fourth_moment
    (H D Q : ℕ) (s : ℂ) (hD : 0 < D) (_hs : (1 : ℝ) / 2 ≤ s.re) :
    ∃ C : ℝ, 0 < C ∧
      (∑ d ∈ Ioc D Q, (1 / (d.totient : ℝ)) *
        ∑ χ : PrimitiveCharacter d,
          ‖chen1973Lemma6NaturalMobiusPolynomial H s χ‖ ^ 4) ≤
        2 * C * ((Q : ℝ) + ((H * H : ℕ) : ℝ) / D) *
          ∑ m ∈ Icc (1 : ℤ) (H * H : ℕ),
            ‖chen1973Lemma6MobiusSquareCoefficient H s m‖ ^ 2 := by
  obtain ⟨C, hC, hbound⟩ := chen1973Lemma2_equationThree_complex_unconditional
    (chen1973Lemma6MobiusSquareCoefficient H s) 0 (H * H) D Q hD
  refine ⟨C, hC, ?_⟩
  rw [show (∑ d ∈ Ioc D Q, (1 / (d.totient : ℝ)) *
      ∑ χ : PrimitiveCharacter d,
        ‖chen1973Lemma6NaturalMobiusPolynomial H s χ‖ ^ 4) =
    ∑ d ∈ Ioc D Q, (1 / (d.totient : ℝ)) *
      ∑ χ : PrimitiveCharacter d,
        ‖∑ m ∈ Icc (1 : ℤ) (H * H : ℕ),
          chen1973Lemma6MobiusSquareCoefficient H s m * χ.1 (m : ZMod d)‖ ^ 2 by
    apply Finset.sum_congr rfl
    intro d hd
    congr 1
    apply Finset.sum_congr rfl
    intro χ hχ
    rw [← chen1973Lemma6_mobiusPolynomial_sq_eq_collected]
    rw [norm_pow]
    ring]
  simpa only [Int.zero_add] using hbound

/-- The corrected unrestricted-height Lemma 3 input used after (15). -/
theorem chen1973Lemma6_L_fourth_moment_corrected
    {Q : ℕ} (s : ℂ) (hQ : 2 ≤ Q)
    (hs : Chen1973Lemma3Domain s s.re s.im) :
    chen1973Lemma3FourthMoment Q s ≤
      21000000 * (Q : ℝ) ^ 2 * ‖s‖ ^ 2 *
        Real.log ((Q : ℝ) * (1 + ‖s‖)) ^ 4 :=
  chen1973Lemma3_corrected_endpoint_unconditional s hQ hs

/-- The bounded-height Lemma 3 specialization used uniformly on Chen's small
Cauchy circle.  The concrete height inequality is retained, not hidden in an
Eq. (15)-shaped premise. -/
theorem chen1973Lemma6_L_fourth_moment_bounded_height
    {Q A : ℕ} (s : ℂ) (hQ : 2 ≤ Q)
    (hs : Chen1973Lemma3Domain s s.re s.im)
    (hheight : ‖s‖ ≤ (Q : ℝ) ^ A) :
    chen1973Lemma3FourthMoment Q s ≤
      21000000 * (A + 2 : ℕ) ^ 4 * (Q : ℝ) ^ 2 * ‖s‖ ^ 2 *
        Real.log Q ^ 4 :=
  chen1973Lemma3_bounded_height_specialization_unconditional s hQ hs hheight

end AnalyticNumberTheory.LargeSieve
