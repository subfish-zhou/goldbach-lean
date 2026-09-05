import MathlibNt.AnalyticNumberTheory.Chen1973.Chen1973Lemma3LFourthMoment
import Mathlib.Tactic

noncomputable section
open Complex Finset
open scoped BigOperators ArithmeticFunction
namespace AnalyticNumberTheory.LargeSieve
open MathlibNt.SieveTheory.LiuWeight
set_option maxHeartbeats 1600000

def primitiveWeightedFourthMoment (Q : ℕ) (s : ℂ) : ℝ :=
  ∑ q ∈ Icc 1 Q, ((q : ℝ) / q.totient) *
    ∑ χ : PrimitiveCharacter q, ‖chen1973PrimitiveLValue q s χ‖ ^ 4

lemma primitive_card_le_totient (q : ℕ) (hq : 0 < q) :
    Fintype.card (PrimitiveCharacter q) ≤ q.totient := by
  letI : NeZero q := ⟨Nat.ne_of_gt hq⟩
  calc
    _ ≤ Fintype.card (DirichletCharacter ℂ q) :=
      @Fintype.card_subtype_le (DirichletCharacter ℂ q) _ (fun χ => χ.IsPrimitive) _
    _ = q.totient := by
      have h := DirichletCharacter.sum_char_inv_mul_char_eq ℂ
        (a := (1 : ZMod q)) isUnit_one (1 : ZMod q)
      simpa using h

lemma weighted_polynomial_fourth_le
    (h2 : Chen1973Lemma2EquationTwo) (N Q : ℕ) (s : ℂ)
    (hs : Chen1973Lemma3Domain s s.re s.im) :
    (∑ q ∈ Icc 1 Q, ((q : ℝ) / q.totient) * ∑ χ : PrimitiveCharacter q,
      ‖chen1973PrimitivePolynomialValue q N s χ‖ ^ 4) ≤
      2 * (((Q : ℝ) ^ 2 + Real.pi * ((N * N : ℕ) : ℝ)) *
        liuHarmonic (N * N) ^ 4) := by
  calc
    _ ≤ ∑ q ∈ Icc 1 Q, ((q : ℝ) / q.totient) * ∑ χ : PrimitiveCharacter q,
        ‖chen1973DirichletPolynomial N s χ‖ ^ 4 := by
      apply Finset.sum_le_sum
      intro q hq
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro χ hχ
      by_cases h : 1 < q
      · simp [chen1973PrimitivePolynomialValue, h]
      · simp [chen1973PrimitivePolynomialValue, h]
    _ ≤ 2 * (((Q : ℝ) ^ 2 + Real.pi * ((N * N : ℕ) : ℝ)) *
        ∑ m ∈ Icc (1 : ℤ) (N * N : ℕ), ‖chen1973PairCoefficient N s m‖ ^ 2) :=
      chen1973Lemma2_source_call_on_pairCoefficient h2 N Q s
    _ ≤ _ := by
      gcongr
      exact chen1973_pairCoefficient_energy_le_harmonic_four N s hs

lemma weighted_truncation_error_scalar
    {Q : ℕ} {s : ℂ} (hQ : 2 ≤ Q)
    (hs : Chen1973Lemma3Domain s s.re s.im) :
    (∑ q ∈ Icc 1 Q, ((q : ℝ) / q.totient) * ∑ χ : PrimitiveCharacter q,
      ‖chen1973PrimitiveLValue q s χ -
        chen1973PrimitivePolynomialValue q (chen1973Lemma3Cutoff Q s) s χ‖ ^ 4) ≤
      2560000 * (Q : ℝ) ^ 2 * ‖s‖ ^ 2 * chen1973Lemma3LogScale Q s ^ 4 := by
  let N := chen1973Lemma3Cutoff Q s
  let L := chen1973Lemma3LogScale Q s
  have hQr : (0 : ℝ) < Q := by positivity
  calc
    _ ≤ ∑ q ∈ Icc 1 Q, 2560000 * ‖s‖ ^ 2 * (Q : ℝ) * L ^ 4 := by
      apply Finset.sum_le_sum
      intro q hq
      have hq0 : 0 < q := (Finset.mem_Icc.mp hq).1
      have hqQ := (Finset.mem_Icc.mp hq).2
      have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr hq0
      have hcard : (Fintype.card (PrimitiveCharacter q) : ℝ) ≤ q.totient := by
        exact_mod_cast primitive_card_le_totient q hq0
      have hsum : (∑ χ : PrimitiveCharacter q,
          ‖chen1973PrimitiveLValue q s χ - chen1973PrimitivePolynomialValue q N s χ‖ ^ 4) ≤
          (Fintype.card (PrimitiveCharacter q) : ℝ) *
            (40 * ‖s‖ * Real.sqrt q * Real.log q * (((N + 1 : ℕ) : ℝ) ^ (-s.re))) ^ 4 := by
        by_cases hq1 : 1 < q
        · letI : NeZero q := ⟨Nat.ne_zero_of_lt hq1⟩
          calc
            _ ≤ ∑ _χ : PrimitiveCharacter q,
                (40 * ‖s‖ * Real.sqrt q * Real.log q * (((N + 1 : ℕ) : ℝ) ^ (-s.re))) ^ 4 := by
              apply Finset.sum_le_sum
              intro χ hχ
              have h := pow_le_pow_left₀ (norm_nonneg _)
                (chen1973_LFunction_sub_polynomial_le_forty hq1 χ N s hs) 4
              simpa [chen1973PrimitiveLValue, chen1973PrimitivePolynomialValue, hq1] using h
            _ = _ := by simp
        · have : q = 1 := by omega
          subst q
          simp
      have hraw := chen1973Lemma3_truncation_pointwise_scalar hQ hq0 hqQ hs
      calc
        _ ≤ ((q : ℝ) / q.totient) * ((q.totient : ℝ) *
            (40 * ‖s‖ * Real.sqrt q * Real.log q * (((N + 1 : ℕ) : ℝ) ^ (-s.re))) ^ 4) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact hsum.trans (mul_le_mul_of_nonneg_right hcard (by positivity))
        _ = (q : ℝ) *
            (40 * ‖s‖ * Real.sqrt q * Real.log q * (((N + 1 : ℕ) : ℝ) ^ (-s.re))) ^ 4 := by
          field_simp
        _ ≤ (q : ℝ) * (2560000 * ‖s‖ ^ 2 * (q : ℝ) ^ 2 / (Q : ℝ) ^ 2 * L ^ 4) := by
          exact mul_le_mul_of_nonneg_left hraw (by positivity)
        _ ≤ (Q : ℝ) * (2560000 * ‖s‖ ^ 2 * (Q : ℝ) ^ 2 / (Q : ℝ) ^ 2 * L ^ 4) := by
          gcongr
        _ = _ := by field_simp
    _ = _ := by
      simp only [Finset.sum_const, nsmul_eq_mul, Nat.card_Icc]
      norm_num
      ring

lemma weighted_fourth_finite_assembly
    (h2 : Chen1973Lemma2EquationTwo) (N Q : ℕ) (s : ℂ)
    (hs : Chen1973Lemma3Domain s s.re s.im) :
    primitiveWeightedFourthMoment Q s ≤
      16 * (((Q : ℝ) ^ 2 + Real.pi * ((N * N : ℕ) : ℝ)) * liuHarmonic (N * N) ^ 4) +
      8 * ∑ q ∈ Icc 1 Q, ((q : ℝ) / q.totient) * ∑ χ : PrimitiveCharacter q,
        ‖chen1973PrimitiveLValue q s χ - chen1973PrimitivePolynomialValue q N s χ‖ ^ 4 := by
  calc
    _ ≤ ∑ q ∈ Icc 1 Q, ((q : ℝ) / q.totient) * ∑ χ : PrimitiveCharacter q,
        8 * (‖chen1973PrimitivePolynomialValue q N s χ‖ ^ 4 +
          ‖chen1973PrimitiveLValue q s χ - chen1973PrimitivePolynomialValue q N s χ‖ ^ 4) := by
      apply Finset.sum_le_sum
      intro q hq
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Finset.sum_le_sum fun χ hχ => norm_four_le_eight_add_norm_sub_four _ _
    _ = 8 * (∑ q ∈ Icc 1 Q, ((q : ℝ) / q.totient) * ∑ χ : PrimitiveCharacter q,
          ‖chen1973PrimitivePolynomialValue q N s χ‖ ^ 4) +
        8 * ∑ q ∈ Icc 1 Q, ((q : ℝ) / q.totient) * ∑ χ : PrimitiveCharacter q,
          ‖chen1973PrimitiveLValue q s χ - chen1973PrimitivePolynomialValue q N s χ‖ ^ 4 := by
      simp_rw [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum]
      simp_rw [mul_add, Finset.sum_add_distrib]
      simp only [Finset.mul_sum]
      apply congrArg₂ (· + ·)
      · apply Finset.sum_congr rfl
        intro q hq
        apply Finset.sum_congr rfl
        intro χ hχ
        ring
      · apply Finset.sum_congr rfl
        intro q hq
        apply Finset.sum_congr rfl
        intro χ hχ
        ring
    _ ≤ _ := by
      have h := weighted_polynomial_fourth_le h2 N Q s hs
      linarith

theorem primitiveWeightedFourthMoment_corrected_endpoint
    (h2 : Chen1973Lemma2EquationTwo) {Q : ℕ} (s : ℂ) (hQ : 2 ≤ Q)
    (hs : Chen1973Lemma3Domain s s.re s.im) :
    primitiveWeightedFourthMoment Q s ≤
      21000000 * (Q : ℝ) ^ 2 * ‖s‖ ^ 2 *
        Real.log ((Q : ℝ) * (1 + ‖s‖)) ^ 4 := by
  let N := chen1973Lemma3Cutoff Q s
  let L := chen1973Lemma3LogScale Q s
  have hfin := weighted_fourth_finite_assembly h2 N Q s hs
  have hH := chen1973Lemma3_harmonic_le_logScale (Q := Q) (s := s) hQ
  have hH0 : 0 ≤ liuHarmonic (N * N) := by
    unfold liuHarmonic
    positivity
  have hH4 : liuHarmonic (N * N) ^ 4 ≤ (6 * L) ^ 4 := by
    exact pow_le_pow_left₀ hH0 (by simpa [N, L] using hH) 4
  have herr := weighted_truncation_error_scalar (Q := Q) (s := s) hQ hs
  have hn := chen1973Lemma3_norm_half hs
  have hn0 : 0 ≤ ‖s‖ := norm_nonneg s
  have hQr : (0 : ℝ) ≤ Q := by positivity
  have hN := chen1973Lemma3Cutoff_le Q s
  have hN2 : (((N * N : ℕ) : ℝ)) ≤ (Q : ℝ) ^ 2 * ‖s‖ ^ 2 := by
    dsimp [N]
    norm_num [Nat.cast_mul]
    nlinarith
  have hq2 : (Q : ℝ) ^ 2 ≤ 4 * (Q : ℝ) ^ 2 * ‖s‖ ^ 2 := by
    nlinarith [sq_nonneg ((Q : ℝ) * (2 * ‖s‖ - 1))]
  have hpi : Real.pi ≤ 4 := Real.pi_lt_four.le
  have hscale :
      (Q : ℝ) ^ 2 + Real.pi * (((N * N : ℕ) : ℝ)) ≤
        8 * (Q : ℝ) ^ 2 * ‖s‖ ^ 2 := by
    calc
      _ ≤ (Q : ℝ) ^ 2 + 4 * (((N * N : ℕ) : ℝ)) := by gcongr
      _ ≤ (Q : ℝ) ^ 2 + 4 * ((Q : ℝ) ^ 2 * ‖s‖ ^ 2) := by gcongr
      _ ≤ _ := by linarith
  have hL0 : 0 ≤ L := (chen1973Lemma3_logScale_pos (Q := Q) (s := s) hQ).le
  calc
    primitiveWeightedFourthMoment Q s ≤
        16 * (((Q : ℝ) ^ 2 + Real.pi * (((N * N : ℕ) : ℝ))) *
          liuHarmonic (N * N) ^ 4) +
        8 * ∑ q ∈ Icc 1 Q, ((q : ℝ) / q.totient) * ∑ χ : PrimitiveCharacter q,
          ‖chen1973PrimitiveLValue q s χ -
            chen1973PrimitivePolynomialValue q N s χ‖ ^ 4 := hfin
    _ ≤ 16 * ((8 * (Q : ℝ) ^ 2 * ‖s‖ ^ 2) * (6 * L) ^ 4) +
        8 * (2560000 * (Q : ℝ) ^ 2 * ‖s‖ ^ 2 * L ^ 4) := by gcongr
    _ = 20645888 * (Q : ℝ) ^ 2 * ‖s‖ ^ 2 * L ^ 4 := by ring
    _ ≤ 21000000 * (Q : ℝ) ^ 2 * ‖s‖ ^ 2 * L ^ 4 := by gcongr; norm_num

end AnalyticNumberTheory.LargeSieve
