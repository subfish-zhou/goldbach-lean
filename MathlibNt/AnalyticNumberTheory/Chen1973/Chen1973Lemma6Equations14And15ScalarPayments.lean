/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nous Research
-/
import MathlibNt.AnalyticNumberTheory.Chen1973.Chen1973Lemma6Equations14And15

/-!
# Chen 1973, Lemma 6, equations (14) and (15): scalar payments

This file pays the elementary scalar estimates left after the exact finite
expansions in `Chen1973Lemma6Equations14And15`.  Each payment is a separate
result.  The coefficient estimates apply only to Chen's literal coefficients;
there is no arbitrary-coefficient strengthening.
-/

noncomputable section

open Classical Complex Finset
open scoped BigOperators ArithmeticFunction

namespace AnalyticNumberTheory.LargeSieve

open MathlibNt.SieveTheory.LiuWeight

private lemma chen1973Lemma6_moebius_complex_norm_le_one (n : ℕ) :
    ‖((ArithmeticFunction.moebius n : ℤ) : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_intCast]
  exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n)

/-- Trivial harmonic majorant for Chen's literal Möbius polynomial on the
`Re(s) ≥ 1` line used in equation (14). -/
theorem chen1973Lemma6_mobiusPolynomial_norm_le_harmonic
    {H d : ℕ} {s : ℂ} (hs : 1 ≤ s.re) (χ : PrimitiveCharacter d) :
    ‖chen1973Lemma6NaturalMobiusPolynomial H s χ‖ ≤ liuHarmonic H := by
  unfold chen1973Lemma6NaturalMobiusPolynomial chen1973Lemma6MobiusPartialSum
  calc
    ‖∑ n ∈ Icc 1 H,
        ((ArithmeticFunction.moebius n : ℤ) : ℂ) * χ.1 (n : ZMod d) /
          (n : ℂ) ^ s‖ ≤
      ∑ n ∈ Icc 1 H,
        ‖((ArithmeticFunction.moebius n : ℤ) : ℂ) * χ.1 (n : ZMod d) /
          (n : ℂ) ^ s‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Icc 1 H, (n : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro n hn
      have hnpos : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
      rw [norm_div, norm_mul]
      rw [Complex.norm_natCast_cpow_of_pos (by exact_mod_cast hnpos)]
      have hμ := chen1973Lemma6_moebius_complex_norm_le_one n
      have hχ := DirichletCharacter.norm_le_one χ.1 (n : ZMod d)
      have hnum : ‖((ArithmeticFunction.moebius n : ℤ) : ℂ)‖ *
          ‖χ.1 (n : ZMod d)‖ ≤ 1 :=
        mul_le_one₀ hμ (norm_nonneg _) hχ
      calc
        ‖((ArithmeticFunction.moebius n : ℤ) : ℂ)‖ * ‖χ.1 (n : ZMod d)‖ /
            (n : ℝ) ^ s.re ≤ 1 / (n : ℝ) ^ s.re := by gcongr
        _ = (n : ℝ) ^ (-s.re) := by
          rw [one_div, Real.rpow_neg hnpos.le]
        _ ≤ (n : ℝ) ^ (-1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (mem_Icc.mp hn).1)
            (by linarith)
        _ = (n : ℝ)⁻¹ := Real.rpow_neg_one _
    _ = liuHarmonic H := rfl

private lemma chen1973Lemma6_card_primitive_le_totient (q : ℕ) (hq : 0 < q) :
    Fintype.card (PrimitiveCharacter q) ≤ q.totient := by
  exact primitiveCharacter_card_le_totient_basic q hq

/-- Pointwise Abel--Pólya--Vinogradov payment for the literal remainder in
(14).  The source range `Re(s) ≥ 1` is explicit. -/
theorem chen1973Lemma6_equation14_remainder_pointwise
    {H d : ℕ} {s : ℂ} (hd : 1 < d) (hs : 1 ≤ s.re)
    (χ : PrimitiveCharacter d) :
    ‖(chen1973PrimitiveLValue d s χ -
          chen1973Lemma6NaturalLPolynomial H s χ) *
        chen1973Lemma6NaturalMobiusPolynomial H s χ‖ ≤
      (40 * ‖s‖ * Real.sqrt d * Real.log d *
        (((H + 1 : ℕ) : ℝ) ^ (-s.re))) * liuHarmonic H := by
  letI : NeZero d := ⟨Nat.ne_zero_of_lt hd⟩
  have hdomain : Chen1973Lemma3Domain s s.re s.im := by
    constructor
    · apply Complex.ext <;> simp
    · linarith
  have htail := chen1973_LFunction_sub_polynomial_le_forty hd χ H s hdomain
  have hpoly := chen1973Lemma6_mobiusPolynomial_norm_le_harmonic (H := H) hs χ
  unfold chen1973PrimitiveLValue
  rw [dif_pos hd]
  change ‖(χ.1.LFunction s - chen1973DirichletPolynomial H s χ) *
      chen1973Lemma6NaturalMobiusPolynomial H s χ‖ ≤ _
  rw [norm_mul]
  exact mul_le_mul htail hpoly (norm_nonneg _) (by positivity)

/-- The equation-(14) remainder moment is paid by the explicit finite
PV--Abel scalar sum; no remainder-shaped premise is retained. -/
theorem chen1973Lemma6_equation14_remainderMoment_le_explicit
    (H D Q : ℕ) (s : ℂ) (hD : 0 < D) (hs : 1 ≤ s.re) :
    chen1973Lemma6Equation14RemainderMoment H D Q s ≤
      ∑ d ∈ Ioc D Q,
        ((40 * ‖s‖ * Real.sqrt d * Real.log d *
          (((H + 1 : ℕ) : ℝ) ^ (-s.re))) * liuHarmonic H) ^ 2 := by
  unfold chen1973Lemma6Equation14RemainderMoment
  apply Finset.sum_le_sum
  intro d hd
  have hdD := (mem_Ioc.mp hd).1
  have hdpos : 0 < d := by omega
  have hd1 : 1 < d := by omega
  have hφpos : (0 : ℝ) < d.totient := by
    exact_mod_cast Nat.totient_pos.mpr hdpos
  let B : ℝ := (40 * ‖s‖ * Real.sqrt d * Real.log d *
      (((H + 1 : ℕ) : ℝ) ^ (-s.re))) * liuHarmonic H
  have hpoint : ∀ χ : PrimitiveCharacter d,
      ‖(chen1973PrimitiveLValue d s χ -
          chen1973Lemma6NaturalLPolynomial H s χ) *
        chen1973Lemma6NaturalMobiusPolynomial H s χ‖ ^ 2 ≤ B ^ 2 := by
    intro χ
    exact pow_le_pow_left₀ (norm_nonneg _)
      (chen1973Lemma6_equation14_remainder_pointwise hd1 hs χ) 2
  have hcardNat := chen1973Lemma6_card_primitive_le_totient d hdpos
  have hcard : (Fintype.card (PrimitiveCharacter d) : ℝ) ≤ d.totient := by
    exact_mod_cast hcardNat
  calc
    (1 / (d.totient : ℝ)) *
        ∑ χ : PrimitiveCharacter d,
          ‖(chen1973PrimitiveLValue d s χ -
              chen1973Lemma6NaturalLPolynomial H s χ) *
            chen1973Lemma6NaturalMobiusPolynomial H s χ‖ ^ 2 ≤
      (1 / (d.totient : ℝ)) * ∑ _χ : PrimitiveCharacter d, B ^ 2 := by
        exact mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum fun χ hχ => hpoint χ) (by positivity)
    _ = (1 / (d.totient : ℝ)) *
        (Fintype.card (PrimitiveCharacter d) : ℝ) * B ^ 2 := by simp; ring
    _ ≤ B ^ 2 := by
      have hw : (1 / (d.totient : ℝ)) *
          (Fintype.card (PrimitiveCharacter d) : ℝ) ≤ 1 := by
        rw [one_div, inv_mul_le_one₀ hφpos]
        exact hcard
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hw (sq_nonneg B)

/-- Logarithmic form of the Abel--PV remainder payment.  Positivity of `H`
is stated because it is exactly what makes `1 + log H` a nonnegative majorant
for the finite harmonic factor. -/
theorem chen1973Lemma6_equation14_remainderMoment_le_log_explicit
    (H D Q : ℕ) (s : ℂ) (hH : 0 < H) (hD : 0 < D) (hs : 1 ≤ s.re) :
    chen1973Lemma6Equation14RemainderMoment H D Q s ≤
      ∑ d ∈ Ioc D Q,
        ((40 * ‖s‖ * Real.sqrt d * Real.log d *
          (((H + 1 : ℕ) : ℝ) ^ (-s.re))) *
            (1 + Real.log H)) ^ 2 := by
  refine (chen1973Lemma6_equation14_remainderMoment_le_explicit H D Q s hD hs).trans ?_
  apply Finset.sum_le_sum
  intro d hd
  have hdIoc := Finset.mem_Ioc.mp hd
  have hd1 : 1 < d := by omega
  have hlogd : 0 ≤ Real.log d := Real.log_nonneg (by exact_mod_cast hd1.le)
  have hA : 0 ≤ 40 * ‖s‖ * Real.sqrt d * Real.log d *
      (((H + 1 : ℕ) : ℝ) ^ (-s.re)) := by positivity
  have hh := liuHarmonic_le_one_add_log H
  have hbase := mul_le_mul_of_nonneg_left hh hA
  exact pow_le_pow_left₀ (mul_nonneg hA (by unfold liuHarmonic; positivity)) hbase 2

/-- The `m=1` coefficient in Chen's finite convolution vanishes. -/
private lemma chen1973Lemma6_CHWeightedCoefficient_one
    {H : ℕ} (hH : 0 < H) (s : ℂ) :
    chen1973Lemma6CHWeightedCoefficient H s 1 = 0 := by
  unfold chen1973Lemma6CHWeightedCoefficient chen1973Lemma6ProductCoefficient
  simp only [if_pos]
  rw [Finset.sum_eq_single (1, 1)]
  · norm_num
  · intro ab hab habne
    by_cases hp : (ab.1 * ab.2 : ℤ) = 1
    · have hpNat : ab.1 * ab.2 = 1 := by exact_mod_cast hp
      obtain ⟨ha, hb⟩ := mul_eq_one.mp hpNat
      apply False.elim
      apply habne
      apply Prod.ext
      · exact ha
      · exact hb
    · simp [hp]
  · intro hnot
    have h1H : 1 ≤ H := hH
    exact False.elim (hnot (by simp [h1H]))

/-- The finite convolution coefficient `C_H(m)/mˢ` in (14) has the same
weighted divisor majorant as the source uses.  The hypothesis `Re(s) ≥ 1` is
the literal equation-(14) range. -/
theorem chen1973Lemma6_CHWeightedCoefficient_norm_le
    {H : ℕ} (hH : 0 < H) {s : ℂ} {m : ℤ} (hs : 1 ≤ s.re)
    (hm : m ∈ Icc (1 : ℤ) (H * H : ℕ)) :
    ‖chen1973Lemma6CHWeightedCoefficient H s m‖ ≤
      (m.toNat.divisors.card : ℝ) * (m.toNat : ℝ) ^ (-(1 / 2 : ℝ)) := by
  by_cases hm1 : m = 1
  · subst m
    rw [chen1973Lemma6_CHWeightedCoefficient_one hH]
    norm_num [Nat.divisors]
  have hmposZ : 0 < m := lt_of_lt_of_le Int.zero_lt_one (mem_Icc.mp hm).1
  have hmpos : 0 < m.toNat := by omega
  have hmone : (1 : ℝ) ≤ m.toNat := by exact_mod_cast hmpos
  unfold chen1973Lemma6CHWeightedCoefficient
  rw [if_neg hm1, zero_sub, norm_neg]
  unfold chen1973Lemma6ProductCoefficient
  rw [← Finset.sum_filter]
  calc
    ‖∑ ab ∈ chen1973PairFiber H m,
        (ab.1 : ℂ) ^ (-s) *
          (((ArithmeticFunction.moebius ab.2 : ℤ) : ℂ) / (ab.2 : ℂ) ^ s)‖ ≤
      ∑ ab ∈ chen1973PairFiber H m,
        ‖(ab.1 : ℂ) ^ (-s) *
          (((ArithmeticFunction.moebius ab.2 : ℤ) : ℂ) / (ab.2 : ℂ) ^ s)‖ :=
        norm_sum_le _ _
    _ ≤ (chen1973PairFiber H m).card •
        ((m.toNat : ℝ) ^ (-(1 / 2 : ℝ))) := by
      apply Finset.sum_le_card_nsmul
      intro ab hab
      rw [chen1973PairFiber, Finset.mem_filter] at hab
      have habmem := Finset.mem_product.mp hab.1
      have hapos : (0 : ℝ) < ab.1 := by exact_mod_cast
        (lt_of_lt_of_le Nat.zero_lt_one (mem_Icc.mp habmem.1).1)
      have hbpos : (0 : ℝ) < ab.2 := by exact_mod_cast
        (lt_of_lt_of_le Nat.zero_lt_one (mem_Icc.mp habmem.2).1)
      have hprodNat : ab.1 * ab.2 = m.toNat := by
        have hmn : (m.toNat : ℤ) = m := Int.toNat_of_nonneg hmposZ.le
        exact_mod_cast hab.2.trans hmn.symm
      rw [norm_mul, norm_div]
      have hnorma : ‖(ab.1 : ℂ) ^ (-s)‖ = (ab.1 : ℝ) ^ (-s.re) := by
        simpa only [Complex.neg_re] using
          Complex.norm_natCast_cpow_of_pos (by exact_mod_cast hapos) (-s)
      have hnormb : ‖(ab.2 : ℂ) ^ s‖ = (ab.2 : ℝ) ^ s.re :=
        Complex.norm_natCast_cpow_of_pos (by exact_mod_cast hbpos) s
      rw [hnorma, hnormb]
      have hμ := chen1973Lemma6_moebius_complex_norm_le_one ab.2
      have hden : 0 < (ab.2 : ℝ) ^ s.re := Real.rpow_pos_of_pos hbpos _
      calc
        (ab.1 : ℝ) ^ (-s.re) *
            (‖((ArithmeticFunction.moebius ab.2 : ℤ) : ℂ)‖ /
              (ab.2 : ℝ) ^ s.re) ≤
          (ab.1 : ℝ) ^ (-s.re) * (1 / (ab.2 : ℝ) ^ s.re) := by
            gcongr
        _ = ((ab.1 : ℝ) * (ab.2 : ℝ)) ^ (-s.re) := by
          rw [one_div, ← Real.rpow_neg hbpos.le,
            ← Real.mul_rpow hapos.le hbpos.le]
        _ = (m.toNat : ℝ) ^ (-s.re) := by
          congr 1
          exact_mod_cast hprodNat
        _ ≤ (m.toNat : ℝ) ^ (-(1 / 2 : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le hmone (by linarith)
    _ ≤ (m.toNat.divisors.card : ℝ) *
        (m.toNat : ℝ) ^ (-(1 / 2 : ℝ)) := by
      simp only [nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right
        (by exact_mod_cast chen1973PairFiber_card_le_divisors hm)
        (Real.rpow_nonneg (by positivity) _)

/-- The `C_H` divisor-energy payment in equation (14). -/
theorem chen1973Lemma6_CHWeightedCoefficient_energy_le_harmonic_four
    (H : ℕ) (hH : 0 < H) (s : ℂ) (hs : 1 ≤ s.re) :
    (∑ m ∈ Icc (1 : ℤ) (H * H : ℕ),
      ‖chen1973Lemma6CHWeightedCoefficient H s m‖ ^ 2) ≤
      liuHarmonic (H * H) ^ 4 := by
  calc
    _ ≤ ∑ m ∈ Icc (1 : ℤ) (H * H : ℕ),
        ((m.toNat.divisors.card : ℝ) ^ 2) * (m.toNat : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro m hm
      have h := chen1973Lemma6_CHWeightedCoefficient_norm_le hH hs hm
      have hsq := pow_le_pow_left₀ (norm_nonneg _) h 2
      calc
        ‖chen1973Lemma6CHWeightedCoefficient H s m‖ ^ 2 ≤
            ((m.toNat.divisors.card : ℝ) *
              (m.toNat : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 := hsq
        _ = ((m.toNat.divisors.card : ℝ) ^ 2) * (m.toNat : ℝ)⁻¹ := by
          have hmpos : (0 : ℝ) < m.toNat := by
            exact_mod_cast (show 0 < m.toNat by
              have : 0 < m := lt_of_lt_of_le Int.zero_lt_one (mem_Icc.mp hm).1
              omega)
          rw [mul_pow]
          congr 1
          rw [← Real.rpow_natCast, ← Real.rpow_mul hmpos.le]
          norm_num
          exact Real.rpow_neg_one _
    _ = ∑ n ∈ Icc 1 (H * H),
        ((n.divisors.card : ℝ) ^ 2) * (n : ℝ)⁻¹ := by
      simpa using sum_Icc_int_toNat_eq_sum_Icc
        (F := fun n => ((n.divisors.card : ℝ) ^ 2) * (n : ℝ)⁻¹) (H * H)
    _ ≤ liuHarmonic (H * H) ^ 4 :=
      divisorSquareWeightedPrefix_le_fourth_harmonic (H * H)

/-- Explicit `log⁴` version of the `C_H` energy payment. -/
theorem chen1973Lemma6_CHWeightedCoefficient_energy_le_log_four
    (H : ℕ) (hH : 0 < H) (s : ℂ) (hs : 1 ≤ s.re) :
    (∑ m ∈ Icc (1 : ℤ) (H * H : ℕ),
      ‖chen1973Lemma6CHWeightedCoefficient H s m‖ ^ 2) ≤
      (1 + Real.log (H * H : ℕ)) ^ 4 := by
  exact (chen1973Lemma6_CHWeightedCoefficient_energy_le_harmonic_four H hH s hs).trans
    (pow_le_pow_left₀ (by unfold liuHarmonic; positivity)
      (liuHarmonic_le_one_add_log (H * H)) 4)

/-- The literal coefficient `j(m)` in (15), including its `m⁻ˢ` weight, is
bounded by `τ(m)m⁻¹/²` on Chen's half-plane. -/
theorem chen1973Lemma6_mobiusSquareCoefficient_norm_le
    {H : ℕ} {s : ℂ} {m : ℤ}
    (hs : Chen1973Lemma3Domain s s.re s.im)
    (hm : m ∈ Icc (1 : ℤ) (H * H : ℕ)) :
    ‖chen1973Lemma6MobiusSquareCoefficient H s m‖ ≤
      (m.toNat.divisors.card : ℝ) * (m.toNat : ℝ) ^ (-(1 / 2 : ℝ)) := by
  have hmposZ : 0 < m := lt_of_lt_of_le Int.zero_lt_one (mem_Icc.mp hm).1
  have hmpos : 0 < m.toNat := by omega
  have hmone : (1 : ℝ) ≤ m.toNat := by exact_mod_cast hmpos
  unfold chen1973Lemma6MobiusSquareCoefficient chen1973Lemma6ProductCoefficient
  rw [← Finset.sum_filter]
  calc
    ‖∑ ab ∈ chen1973PairFiber H m,
        (((ArithmeticFunction.moebius ab.1 : ℤ) : ℂ) / (ab.1 : ℂ) ^ s) *
          (((ArithmeticFunction.moebius ab.2 : ℤ) : ℂ) / (ab.2 : ℂ) ^ s)‖ ≤
      ∑ ab ∈ chen1973PairFiber H m,
        ‖(((ArithmeticFunction.moebius ab.1 : ℤ) : ℂ) / (ab.1 : ℂ) ^ s) *
          (((ArithmeticFunction.moebius ab.2 : ℤ) : ℂ) / (ab.2 : ℂ) ^ s)‖ :=
        norm_sum_le _ _
    _ ≤ (chen1973PairFiber H m).card •
        ((m.toNat : ℝ) ^ (-(1 / 2 : ℝ))) := by
      apply Finset.sum_le_card_nsmul
      intro ab hab
      rw [chen1973PairFiber, Finset.mem_filter] at hab
      have habmem := Finset.mem_product.mp hab.1
      have hapos : (0 : ℝ) < ab.1 := by exact_mod_cast
        (lt_of_lt_of_le Nat.zero_lt_one (mem_Icc.mp habmem.1).1)
      have hbpos : (0 : ℝ) < ab.2 := by exact_mod_cast
        (lt_of_lt_of_le Nat.zero_lt_one (mem_Icc.mp habmem.2).1)
      have hprodNat : ab.1 * ab.2 = m.toNat := by
        have hmn : (m.toNat : ℤ) = m := Int.toNat_of_nonneg hmposZ.le
        exact_mod_cast hab.2.trans hmn.symm
      rw [norm_mul, norm_div, norm_div]
      have hnorma : ‖(ab.1 : ℂ) ^ s‖ = (ab.1 : ℝ) ^ s.re :=
        Complex.norm_natCast_cpow_of_pos (by exact_mod_cast hapos) s
      have hnormb : ‖(ab.2 : ℂ) ^ s‖ = (ab.2 : ℝ) ^ s.re :=
        Complex.norm_natCast_cpow_of_pos (by exact_mod_cast hbpos) s
      rw [hnorma, hnormb]
      have hμa := chen1973Lemma6_moebius_complex_norm_le_one ab.1
      have hμb := chen1973Lemma6_moebius_complex_norm_le_one ab.2
      have hdena : 0 < (ab.1 : ℝ) ^ s.re := Real.rpow_pos_of_pos hapos _
      have hdenb : 0 < (ab.2 : ℝ) ^ s.re := Real.rpow_pos_of_pos hbpos _
      calc
        ‖((ArithmeticFunction.moebius ab.1 : ℤ) : ℂ)‖ /
              (ab.1 : ℝ) ^ s.re *
            (‖((ArithmeticFunction.moebius ab.2 : ℤ) : ℂ)‖ /
              (ab.2 : ℝ) ^ s.re) ≤
          1 / ((ab.1 : ℝ) ^ s.re) * (1 / ((ab.2 : ℝ) ^ s.re)) := by
            gcongr
        _ = ((ab.1 : ℝ) * (ab.2 : ℝ)) ^ (-s.re) := by
          rw [one_div, one_div, ← Real.rpow_neg hapos.le,
            ← Real.rpow_neg hbpos.le, ← Real.mul_rpow hapos.le hbpos.le]
        _ = (m.toNat : ℝ) ^ (-s.re) := by
          congr 1
          exact_mod_cast hprodNat
        _ ≤ (m.toNat : ℝ) ^ (-(1 / 2 : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le hmone (by linarith [hs.2])
    _ ≤ (m.toNat.divisors.card : ℝ) *
        (m.toNat : ℝ) ^ (-(1 / 2 : ℝ)) := by
      simp only [nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right
        (by exact_mod_cast chen1973PairFiber_card_le_divisors hm)
        (Real.rpow_nonneg (by positivity) _)

/-- Weighted divisor-square payment for the literal `j(m)` coefficients in
(15).  This is the finite form of `|j(m)| ≤ τ(m)` followed by
`∑ τ(m)²/m ≪ log⁴`. -/
theorem chen1973Lemma6_mobiusSquareCoefficient_energy_le_harmonic_four
    (H : ℕ) (s : ℂ) (hs : Chen1973Lemma3Domain s s.re s.im) :
    (∑ m ∈ Icc (1 : ℤ) (H * H : ℕ),
      ‖chen1973Lemma6MobiusSquareCoefficient H s m‖ ^ 2) ≤
      liuHarmonic (H * H) ^ 4 := by
  calc
    _ ≤ ∑ m ∈ Icc (1 : ℤ) (H * H : ℕ),
        ((m.toNat.divisors.card : ℝ) ^ 2) * (m.toNat : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro m hm
      have h := chen1973Lemma6_mobiusSquareCoefficient_norm_le hs hm
      have hsq := pow_le_pow_left₀ (norm_nonneg _) h 2
      calc
        ‖chen1973Lemma6MobiusSquareCoefficient H s m‖ ^ 2 ≤
            ((m.toNat.divisors.card : ℝ) *
              (m.toNat : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 := hsq
        _ = ((m.toNat.divisors.card : ℝ) ^ 2) * (m.toNat : ℝ)⁻¹ := by
          have hmpos : (0 : ℝ) < m.toNat := by
            exact_mod_cast (show 0 < m.toNat by
              have : 0 < m := lt_of_lt_of_le Int.zero_lt_one (mem_Icc.mp hm).1
              omega)
          rw [mul_pow]
          congr 1
          rw [← Real.rpow_natCast, ← Real.rpow_mul hmpos.le]
          norm_num
          exact Real.rpow_neg_one _
    _ = ∑ n ∈ Icc 1 (H * H),
        ((n.divisors.card : ℝ) ^ 2) * (n : ℝ)⁻¹ := by
      simpa using sum_Icc_int_toNat_eq_sum_Icc
        (F := fun n => ((n.divisors.card : ℝ) ^ 2) * (n : ℝ)⁻¹) (H * H)
    _ ≤ liuHarmonic (H * H) ^ 4 :=
      divisorSquareWeightedPrefix_le_fourth_harmonic (H * H)

/-- Explicit logarithmic version of the (15) coefficient energy. -/
theorem chen1973Lemma6_mobiusSquareCoefficient_energy_le_log_four
    (H : ℕ) (s : ℂ) (hs : Chen1973Lemma3Domain s s.re s.im) :
    (∑ m ∈ Icc (1 : ℤ) (H * H : ℕ),
      ‖chen1973Lemma6MobiusSquareCoefficient H s m‖ ^ 2) ≤
      (1 + Real.log (H * H : ℕ)) ^ 4 := by
  exact (chen1973Lemma6_mobiusSquareCoefficient_energy_le_harmonic_four H s hs).trans
    (pow_le_pow_left₀ (by unfold liuHarmonic; positivity)
      (liuHarmonic_le_one_add_log (H * H)) 4)

/-- Equation (15) after paying its literal weighted divisor-square energy. -/
theorem chen1973Lemma6_equation15_scalar_paid
    (H D Q : ℕ) (s : ℂ) (hD : 0 < D)
    (hs : Chen1973Lemma3Domain s s.re s.im) :
    ∃ C : ℝ, 0 < C ∧
      (∑ d ∈ Ioc D Q, (1 / (d.totient : ℝ)) *
        ∑ χ : PrimitiveCharacter d,
          ‖chen1973Lemma6NaturalMobiusPolynomial H s χ‖ ^ 4) ≤
        2 * C * ((Q : ℝ) + ((H * H : ℕ) : ℝ) / D) *
          (1 + Real.log (H * H : ℕ)) ^ 4 := by
  obtain ⟨C, hC, h15⟩ :=
    chen1973Lemma6_equation15_fourth_moment H D Q s hD hs.2
  refine ⟨C, hC, h15.trans ?_⟩
  gcongr
  exact chen1973Lemma6_mobiusSquareCoefficient_energy_le_log_four H s hs

/-- The finite Abel--PV remainder summed over Chen's literal conductor interval
`D < d ≤ Q`.  The hypotheses `0 < H`, `0 < D`, and `D < Q` are exactly the
nonempty source regime; the constant `40` and every height factor remain
visible. -/
theorem chen1973Lemma6_equation14_remainderMoment_final_scalar
    (H D Q : ℕ) (s : ℂ) (hH : 0 < H) (hD : 0 < D) (hDQ : D < Q)
    (hs : 1 ≤ s.re) :
    chen1973Lemma6Equation14RemainderMoment H D Q s ≤
      (Q : ℝ) *
        ((40 * ‖s‖ * Real.sqrt Q * Real.log Q *
          (((H + 1 : ℕ) : ℝ) ^ (-s.re))) *
            (1 + Real.log H)) ^ 2 := by
  refine (chen1973Lemma6_equation14_remainderMoment_le_log_explicit
    H D Q s hH hD hs).trans ?_
  let B : ℝ := (40 * ‖s‖ * Real.sqrt Q * Real.log Q *
      (((H + 1 : ℕ) : ℝ) ^ (-s.re))) * (1 + Real.log H)
  calc
    (∑ d ∈ Ioc D Q,
        ((40 * ‖s‖ * Real.sqrt d * Real.log d *
          (((H + 1 : ℕ) : ℝ) ^ (-s.re))) *
            (1 + Real.log H)) ^ 2) ≤
        (Ioc D Q).card • (B ^ 2) := by
      apply Finset.sum_le_card_nsmul
      intro d hd
      have hdI := mem_Ioc.mp hd
      have hd1 : 1 < d := by omega
      have hQ1 : 1 < Q := by omega
      have hsqrt : Real.sqrt d ≤ Real.sqrt Q :=
        Real.sqrt_le_sqrt (by exact_mod_cast hdI.2)
      have hlog : Real.log d ≤ Real.log Q :=
        Real.log_le_log (by exact_mod_cast (show 0 < d by omega))
          (by exact_mod_cast hdI.2)
      have hnonnegd : 0 ≤ 40 * ‖s‖ * Real.sqrt d * Real.log d *
          (((H + 1 : ℕ) : ℝ) ^ (-s.re)) := by positivity
      have hnonnegQ : 0 ≤ 40 * ‖s‖ * Real.sqrt Q * Real.log Q *
          (((H + 1 : ℕ) : ℝ) ^ (-s.re)) := by positivity
      have hmain : 40 * ‖s‖ * Real.sqrt d * Real.log d *
          (((H + 1 : ℕ) : ℝ) ^ (-s.re)) ≤
          40 * ‖s‖ * Real.sqrt Q * Real.log Q *
          (((H + 1 : ℕ) : ℝ) ^ (-s.re)) := by gcongr
      have hlogH : 0 ≤ 1 + Real.log H := by
        exact add_nonneg zero_le_one
          (Real.log_nonneg (by exact_mod_cast hH))
      apply pow_le_pow_left₀ (mul_nonneg hnonnegd hlogH) _ 2
      exact mul_le_mul_of_nonneg_right hmain hlogH
    _ = ((Ioc D Q).card : ℝ) * B ^ 2 := by simp
    _ ≤ (Q : ℝ) * B ^ 2 := by
      gcongr
      exact_mod_cast (show (Ioc D Q).card ≤ Q by simp)

/-- Final scalar form of equation (14).  It combines the sharp finite second
moment, the literal `C_H` divisor energy, and the summed Abel--PV remainder.
No equation-(14)-shaped hypothesis is retained. -/
theorem chen1973Lemma6_equation14_final_scalar_paid
    (H D Q : ℕ) (s : ℂ) (hH : 0 < H) (hD : 0 < D) (hDQ : D < Q)
    (hs : 1 ≤ s.re) :
    ∃ C : ℝ, 0 < C ∧
      (∑ d ∈ Ioc D Q, (1 / (d.totient : ℝ)) *
        ∑ χ : PrimitiveCharacter d, ‖chen1973Lemma6OneSubLS H s χ‖ ^ 2) ≤
        4 * C * ((Q : ℝ) + ((H * H : ℕ) : ℝ) / D) *
            (1 + Real.log (H * H : ℕ)) ^ 4 +
          2 * (Q : ℝ) *
            ((40 * ‖s‖ * Real.sqrt Q * Real.log Q *
              (((H + 1 : ℕ) : ℝ) ^ (-s.re))) *
                (1 + Real.log H)) ^ 2 := by
  obtain ⟨C, hC, h14⟩ :=
    chen1973Lemma6_equation14_weighted_second_moment H D Q s hH hD hs
  refine ⟨C, hC, h14.trans ?_⟩
  have hE :=
    chen1973Lemma6_CHWeightedCoefficient_energy_le_log_four H hH s hs
  have hR := chen1973Lemma6_equation14_remainderMoment_final_scalar
    H D Q s hH hD hDQ hs
  have hfac : 0 ≤ 4 * C * ((Q : ℝ) + ((H * H : ℕ) : ℝ) / D) := by
    positivity
  calc
    4 * C * ((Q : ℝ) + ((H * H : ℕ) : ℝ) / D) *
          (∑ m ∈ Icc (1 : ℤ) (H * H : ℕ),
            ‖chen1973Lemma6CHWeightedCoefficient H s m‖ ^ 2) +
        2 * chen1973Lemma6Equation14RemainderMoment H D Q s ≤
      4 * C * ((Q : ℝ) + ((H * H : ℕ) : ℝ) / D) *
          (1 + Real.log (H * H : ℕ)) ^ 4 +
        2 * ((Q : ℝ) *
          ((40 * ‖s‖ * Real.sqrt Q * Real.log Q *
            (((H + 1 : ℕ) : ℝ) ^ (-s.re))) *
              (1 + Real.log H)) ^ 2) := by gcongr
    _ = _ := by ring

/-- Final `log⁴` endpoint for equation (15), with Chen's actual half-plane
encoded by `Chen1973Lemma3Domain` and the literal `H,D,Q` ranges unchanged. -/
theorem chen1973Lemma6_equation15_final_log_power
    (H D Q : ℕ) (s : ℂ) (hD : 0 < D)
    (hs : Chen1973Lemma3Domain s s.re s.im) :
    ∃ C : ℝ, 0 < C ∧
      (∑ d ∈ Ioc D Q, (1 / (d.totient : ℝ)) *
        ∑ χ : PrimitiveCharacter d,
          ‖chen1973Lemma6NaturalMobiusPolynomial H s χ‖ ^ 4) ≤
        2 * C * ((Q : ℝ) + ((H * H : ℕ) : ℝ) / D) *
          (1 + Real.log (H * H : ℕ)) ^ 4 :=
  chen1973Lemma6_equation15_scalar_paid H D Q s hD hs

end AnalyticNumberTheory.LargeSieve
