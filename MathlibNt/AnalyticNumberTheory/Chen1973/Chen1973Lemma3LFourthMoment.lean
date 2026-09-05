/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nous Research
-/
import MathlibNt.AnalyticNumberTheory.LargeSieve.PrefixMaximal
import MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLQuadraticPolyaVinogradovExplicit
import MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLConditionalValueSeries
import MathlibNt.AnalyticNumberTheory.Chen1973.Chen1973Lemma2PrimitiveLargeSieve
import MathlibNt.AnalyticNumberTheory.Vaughan.VaughanTypeIIActualTensorMomentExplicit

/-!
# Chen 1973, Lemma 3: source-order fourth-moment reductions

This file follows pp. 114--115 of Chen's original paper sentence by sentence.
It defines the literal half-plane, primitive-character fourth moment, truncating
Dirichlet polynomial, its collected two-factor coefficients, and the exact
fourfold expansion used in Chen's invocation of Lemma 2.

The source's final analytic estimate is not packaged as a `Prop`.  The first
unproved printed step is recorded at the end of this file after the proved
finite identities and the actual Lemma 2 call.
-/

noncomputable section

open Complex Finset
open scoped BigOperators

namespace AnalyticNumberTheory.LargeSieve

open DirichletLAbelWeightVariation DirichletLConditionalValueSeries
open MathlibNt.SieveTheory.LiuWeight

/-- The literal domain sentence `s = σ + it`, `σ ≥ 1/2` on p. 114. -/
def Chen1973Lemma3Domain (s : ℂ) (σ t : ℝ) : Prop :=
  s = σ + t * I ∧ (1 : ℝ) / 2 ≤ σ

lemma Chen1973Lemma3Domain.re_eq {s : ℂ} {σ t : ℝ}
    (hs : Chen1973Lemma3Domain s σ t) : s.re = σ := by
  rw [hs.1]
  simp

lemma Chen1973Lemma3Domain.re_pos {s : ℂ} {σ t : ℝ}
    (hs : Chen1973Lemma3Domain s σ t) : 0 < s.re := by
  rw [hs.re_eq]
  linarith [hs.2]

/-- `L(s,χ)` on the nonprincipal primitive range `q > 1`.  The source's
starred family excludes the exceptional principal character at modulus `1`; we
therefore set that term to zero explicitly (and also totalize modulus `0`). -/
def chen1973PrimitiveLValue (q : ℕ) (s : ℂ) (χ : PrimitiveCharacter q) : ℂ :=
  if hq : 1 < q then
    letI : NeZero q := ⟨Nat.ne_zero_of_lt hq⟩
    χ.1.LFunction s
  else 0

/-- Chen's literal sum `∑_{q≤Q} ∑*_{χ_q} |L(s,χ_q)|⁴`. -/
def chen1973Lemma3FourthMoment (Q : ℕ) (s : ℂ) : ℝ :=
  ∑ q ∈ Icc 1 Q, ∑ χ : PrimitiveCharacter q,
    ‖chen1973PrimitiveLValue q s χ‖ ^ 4

/-- The integer `[Q |s|]` selected in the proof on p. 115. -/
def chen1973Lemma3Cutoff (Q : ℕ) (s : ℂ) : ℕ :=
  ⌊(Q : ℝ) * ‖s‖⌋₊

/-- The strict floor endpoint needed in the truncation-error scalar ledger; unlike
`1 ≤ Q‖s‖`, this is valid without a small-height assumption. -/
theorem chen1973Lemma3Cutoff_lt_succ (Q : ℕ) (s : ℂ) :
    (Q : ℝ) * ‖s‖ < chen1973Lemma3Cutoff Q s + 1 := by
  unfold chen1973Lemma3Cutoff
  exact Nat.lt_floor_add_one ((Q : ℝ) * ‖s‖)

/-- The companion non-strict floor inequality. -/
theorem chen1973Lemma3Cutoff_le (Q : ℕ) (s : ℂ) :
    (chen1973Lemma3Cutoff Q s : ℝ) ≤ (Q : ℝ) * ‖s‖ := by
  unfold chen1973Lemma3Cutoff
  exact Nat.floor_le (mul_nonneg (Nat.cast_nonneg Q) (norm_nonneg s))

/-- The finite Dirichlet polynomial `∑_{n=1}^N χ(n)/n^s`. -/
def chen1973DirichletPolynomial (N : ℕ) (s : ℂ) {q : ℕ}
    (χ : PrimitiveCharacter q) : ℂ :=
  ∑ n ∈ Icc 1 N, (n : ℂ) ^ (-s) * χ.1 (n : ZMod q)

/-- A single coefficient after squaring and collecting equal products. -/
def chen1973PairCoefficient (N : ℕ) (s : ℂ) (m : ℤ) : ℂ :=
  ∑ ab ∈ (Icc 1 N).product (Icc 1 N),
    if (ab.1 * ab.2 : ℤ) = m then
      (ab.1 : ℂ) ^ (-s) * (ab.2 : ℂ) ^ (-s)
    else 0

/-- The first finite algebraic step in the fourfold expansion: squaring the
Dirichlet polynomial and collecting the two numerator variables. -/
theorem chen1973DirichletPolynomial_sq_eq_pair_sum
    (N : ℕ) (s : ℂ) {q : ℕ} (χ : PrimitiveCharacter q) :
    chen1973DirichletPolynomial N s χ ^ 2 =
      ∑ ab ∈ (Icc 1 N).product (Icc 1 N),
        ((ab.1 : ℂ) ^ (-s) * (ab.2 : ℂ) ^ (-s)) *
          χ.1 ((ab.1 * ab.2 : ℕ) : ZMod q) := by
  rw [pow_two]
  unfold chen1973DirichletPolynomial
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  calc
    (∑ a ∈ Icc 1 N, ∑ b ∈ Icc 1 N,
        ((a : ℂ) ^ (-s) * χ.1 (a : ZMod q)) *
          ((b : ℂ) ^ (-s) * χ.1 (b : ZMod q))) =
      ∑ ab ∈ (Icc 1 N).product (Icc 1 N),
        (((ab.1 : ℂ) ^ (-s) * χ.1 (ab.1 : ZMod q)) *
          ((ab.2 : ℂ) ^ (-s) * χ.1 (ab.2 : ZMod q))) := by
        exact (Finset.sum_product (Icc 1 N) (Icc 1 N)
          (fun ab => (((ab.1 : ℂ) ^ (-s) * χ.1 (ab.1 : ZMod q)) *
            ((ab.2 : ℂ) ^ (-s) * χ.1 (ab.2 : ZMod q))))).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro ab hab
      rw [show ((ab.1 * ab.2 : ℕ) : ZMod q) =
        (ab.1 : ZMod q) * (ab.2 : ZMod q) by norm_num, map_mul]
      ring

/-- Every product of two integers in `[1,N]` lies in `[1,N²]`. -/
lemma chen1973_pair_product_mem {N a b : ℕ}
    (ha : a ∈ Icc 1 N) (hb : b ∈ Icc 1 N) :
    (a * b : ℤ) ∈ Icc (1 : ℤ) ((N * N : ℕ) : ℤ) := by
  rw [mem_Icc] at ha hb ⊢
  constructor
  · exact_mod_cast Nat.mul_pos ha.1 hb.1
  · exact_mod_cast Nat.mul_le_mul ha.2 hb.2

/-- Collecting equal products is an exact finite reindexing. -/
theorem chen1973_pairCoefficient_character_sum_eq
    (N : ℕ) (s : ℂ) {q : ℕ} (χ : PrimitiveCharacter q) :
    (∑ m ∈ Icc (1 : ℤ) (N * N : ℕ),
        chen1973PairCoefficient N s m * χ.1 (m : ZMod q)) =
      ∑ ab ∈ (Icc 1 N).product (Icc 1 N),
        ((ab.1 : ℂ) ^ (-s) * (ab.2 : ℂ) ^ (-s)) *
          χ.1 ((ab.1 * ab.2 : ℕ) : ZMod q) := by
  unfold chen1973PairCoefficient
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ab hab
  have hab' := Finset.mem_product.mp hab
  let p : ℤ := ab.1 * ab.2
  have hp : p ∈ Icc (1 : ℤ) (N * N : ℕ) :=
    chen1973_pair_product_mem hab'.1 hab'.2
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

/-- Chen's finite fourfold expansion, in the collected form to which Lemma 2
is applied: the fourth power of the original norm is the square norm of the
pair-coefficient character polynomial. -/
theorem chen1973DirichletPolynomial_norm_four_eq_pair_norm_sq
    (N : ℕ) (s : ℂ) {q : ℕ} (χ : PrimitiveCharacter q) :
    ‖chen1973DirichletPolynomial N s χ‖ ^ 4 =
      ‖∑ m ∈ Icc (1 : ℤ) (N * N : ℕ),
        chen1973PairCoefficient N s m * χ.1 (m : ZMod q)‖ ^ 2 := by
  have hsq := chen1973DirichletPolynomial_sq_eq_pair_sum N s χ
  have hcollect := chen1973_pairCoefficient_character_sum_eq N s χ
  calc
    ‖chen1973DirichletPolynomial N s χ‖ ^ 4 =
        ‖chen1973DirichletPolynomial N s χ ^ 2‖ ^ 2 := by
      rw [norm_pow]
      ring
    _ = ‖∑ ab ∈ (Icc 1 N).product (Icc 1 N),
        ((ab.1 : ℂ) ^ (-s) * (ab.2 : ℂ) ^ (-s)) *
          χ.1 ((ab.1 * ab.2 : ℕ) : ZMod q)‖ ^ 2 := by rw [hsq]
    _ = ‖∑ m ∈ Icc (1 : ℤ) (N * N : ℕ),
        chen1973PairCoefficient N s m * χ.1 (m : ZMod q)‖ ^ 2 := by
      rw [hcollect]

/-! ## The printed truncation sentence -/

/-- A primitive character of modulus `q>1` is not principal. -/
lemma chen1973_primitive_ne_one {q : ℕ} [NeZero q] (hq : 1 < q)
    (χ : PrimitiveCharacter q) : χ.1 ≠ 1 := by
  intro h
  have hc := primitive_conductor χ
  rw [h, DirichletCharacter.conductor_one] at hc
  omega

/-- On the source range `q>1`, the finite polynomial is the natural partial
sum used by the already formalized conditional Dirichlet series.  The extra
index `0` vanishes. -/
theorem chen1973DirichletPolynomial_eq_sum_range
    {q : ℕ} [NeZero q] (hq : 1 < q) (χ : PrimitiveCharacter q)
    (N : ℕ) (s : ℂ) :
    chen1973DirichletPolynomial N s χ =
      ∑ n ∈ range (N + 1), cpowWeight s n * χ.1 n := by
  have hχ : χ.1 ≠ 1 := chen1973_primitive_ne_one hq χ
  unfold chen1973DirichletPolynomial
  calc
    (∑ n ∈ Icc 1 N, (n : ℂ) ^ (-s) * χ.1 (n : ZMod q)) =
        ∑ n ∈ Icc 1 N, cpowWeight s n * χ.1 n := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [cpowWeight_nat_eq]
    _ = ∑ n ∈ range (N + 1), cpowWeight s n * χ.1 n := by
      apply Finset.sum_subset
      · intro n hn
        rw [mem_Icc] at hn
        exact mem_range.mpr (by omega)
      · intro n hnRange hnIcc
        have hnlt : n < N + 1 := mem_range.mp hnRange
        have hn0 : n = 0 := by
          by_contra hn
          apply hnIcc
          rw [mem_Icc]
          omega
        subst n
        have hzero : χ.1 (0 : ℕ) = 0 := by
          letI : Fact (1 < q) := ⟨hq⟩
          simpa only [Nat.cast_zero] using
            (MulChar.map_nonunit χ.1 (a := (0 : ZMod q)) not_isUnit_zero)
        rw [hzero]
        simp

/-- The exact, already closed Abel-truncation inequality in the order used on
p. 115.  This proves the finite truncation mechanism and its `|s|/σ` decay,
but has the elementary prefix constant `q`, not yet Chen's sharper
`q^(1/2) log q` constant. -/
theorem chen1973_LFunction_sub_polynomial_coarse
    {q : ℕ} [NeZero q] (hq : 1 < q) (χ : PrimitiveCharacter q)
    (N : ℕ) (s : ℂ) (hs : 0 < s.re) :
    ‖χ.1.LFunction s - chen1973DirichletPolynomial N s χ‖ ≤
      q * (((N + 1 : ℕ) : ℝ) ^ (-s.re) +
        (‖s‖ / s.re) * ((N + 1 : ℕ) : ℝ) ^ (-s.re)) := by
  have hχ : χ.1 ≠ 1 := chen1973_primitive_ne_one hq χ
  have htail := norm_orderedValueSeries_sub_sum_range_le
    χ.1 hχ s hs (m := N + 1) (by omega)
  rw [orderedValueSeries_eq_LFunction_of_re_pos χ.1 hχ s hs,
    ← chen1973DirichletPolynomial_eq_sum_range hq χ N s] at htail
  exact htail

/-- Chen p. 115, first printed estimate before suppressing constants: combine
primitive Pólya--Vinogradov with the general-`s` Abel tail.  The same numerical
prefix constant works for every primitive `χ`, every `N`, and every `s` in the
right half-plane. -/
theorem chen1973_LFunction_sub_polynomial_polyaVinogradov
    {q : ℕ} [NeZero q] (hq : 1 < q) (χ : PrimitiveCharacter q)
    (N : ℕ) (s : ℂ) (hs : 0 < s.re) :
    ‖χ.1.LFunction s - chen1973DirichletPolynomial N s χ‖ ≤
      (4 * Real.sqrt q * (1 + Real.log q)) *
        (((N + 1 : ℕ) : ℝ) ^ (-s.re) +
          (‖s‖ / s.re) * ((N + 1 : ℕ) : ℝ) ^ (-s.re)) := by
  have hχ : χ.1 ≠ 1 := chen1973_primitive_ne_one hq χ
  have hprefix : ∀ M : ℕ,
      ‖∑ n ∈ range M, χ.1 (n : ZMod q)‖ ≤
        4 * Real.sqrt q * (1 + Real.log q) := by
    intro M
    exact χ.2.norm_sum_range_le_four_mul_sqrt_q_mul_one_add_log hq M
  have htail := DirichletCharacter.norm_LFunction_sub_sum_le_of_prefix_bound
    χ.1 hχ s hs (4 * Real.sqrt q * (1 + Real.log q)) hprefix
    (m := N + 1) (by omega)
  rw [← chen1973DirichletPolynomial_eq_sum_range hq χ N s] at htail
  exact htail

/-- The literal Vinogradov form of the preceding estimate.  The constant `40`
is absolute and uniform; `σ ≥ 1/2` absorbs both the Abel endpoint and the
factor `1/σ`, while `q>1` absorbs `1 + log q` into `log q`. -/
theorem chen1973_LFunction_sub_polynomial_le_forty
    {q : ℕ} [NeZero q] (hq : 1 < q) (χ : PrimitiveCharacter q)
    (N : ℕ) (s : ℂ) (hs : Chen1973Lemma3Domain s s.re s.im) :
    ‖χ.1.LFunction s - chen1973DirichletPolynomial N s χ‖ ≤
      40 * ‖s‖ * Real.sqrt q * Real.log q *
        (((N + 1 : ℕ) : ℝ) ^ (-s.re)) := by
  have hspos : 0 < s.re := hs.re_pos
  have hbase := chen1973_LFunction_sub_polynomial_polyaVinogradov
    hq χ N s hspos
  have hlog0 : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq.le)
  have hlogLower : (2 / 3 : ℝ) ≤ Real.log q := by
    have h2 : (2 / 3 : ℝ) ≤ Real.log (2 : ℝ) := by
      have h := Real.le_log_one_add_of_nonneg (show (0 : ℝ) ≤ 1 by norm_num)
      norm_num at h ⊢
      exact h
    have hmono : Real.log (2 : ℝ) ≤ Real.log (q : ℝ) := by
      apply Real.log_le_log
      · norm_num
      · exact_mod_cast (show 2 ≤ q by omega)
    exact h2.trans hmono
  have hsNorm : s.re ≤ ‖s‖ := Complex.re_le_norm s
  have hσ : (1 / 2 : ℝ) ≤ s.re := hs.2
  have hsNorm0 : 0 ≤ ‖s‖ := norm_nonneg s
  have hfactor :
      4 * Real.sqrt q * (1 + Real.log q) *
          (((N + 1 : ℕ) : ℝ) ^ (-s.re) +
            (‖s‖ / s.re) * ((N + 1 : ℕ) : ℝ) ^ (-s.re)) ≤
        40 * ‖s‖ * Real.sqrt q * Real.log q *
          (((N + 1 : ℕ) : ℝ) ^ (-s.re)) := by
    let p : ℝ := (((N + 1 : ℕ) : ℝ) ^ (-s.re))
    have hp0 : 0 ≤ p := by dsimp [p]; positivity
    have hsdiv : ‖s‖ / s.re ≤ 2 * ‖s‖ := by
      rw [div_le_iff₀ hspos]
      nlinarith
    have hone : 1 ≤ 2 * ‖s‖ := by nlinarith
    have hlog : 1 + Real.log q ≤ (5 / 2 : ℝ) * Real.log q := by
      nlinarith
    have hsqrt : 0 ≤ Real.sqrt q := Real.sqrt_nonneg _
    have hsum : 1 + ‖s‖ / s.re ≤ 4 * ‖s‖ := by linarith
    have hcombined :
        (1 + Real.log q) * (1 + ‖s‖ / s.re) ≤
          10 * ‖s‖ * Real.log q := by
      calc
        _ ≤ ((5 / 2 : ℝ) * Real.log q) * (4 * ‖s‖) :=
          mul_le_mul hlog hsum (by positivity) (by positivity)
        _ = _ := by ring
    change 4 * Real.sqrt q * (1 + Real.log q) *
        (p + (‖s‖ / s.re) * p) ≤
      40 * ‖s‖ * Real.sqrt q * Real.log q * p
    calc
      _ = 4 * Real.sqrt q *
          ((1 + Real.log q) * (1 + ‖s‖ / s.re)) * p := by ring
      _ ≤ 4 * Real.sqrt q * (10 * ‖s‖ * Real.log q) * p := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hcombined (mul_nonneg (by norm_num) hsqrt)) hp0
      _ = _ := by ring
  exact hbase.trans hfactor

/-! ## Pair-coefficient energy -/

/-- The bounded factorization fibre collected by `chen1973PairCoefficient`. -/
def chen1973PairFiber (N : ℕ) (m : ℤ) : Finset (ℕ × ℕ) :=
  ((Icc 1 N).product (Icc 1 N)).filter fun ab => (ab.1 * ab.2 : ℤ) = m

lemma chen1973PairFiber_card_le_divisors {N : ℕ} {m : ℤ}
    (hm : m ∈ Icc (1 : ℤ) (N * N : ℕ)) :
    (chen1973PairFiber N m).card ≤ m.toNat.divisors.card := by
  apply Finset.card_le_card_of_injOn (fun ab : ℕ × ℕ => ab.1)
  · intro ab hab
    change ab ∈ chen1973PairFiber N m at hab
    rw [chen1973PairFiber, Finset.mem_filter] at hab
    have habmem := Finset.mem_product.mp hab.1
    have hmpos : 0 < m := lt_of_lt_of_le Int.zero_lt_one (Finset.mem_Icc.mp hm).1
    have hmn : (m.toNat : ℤ) = m := Int.toNat_of_nonneg hmpos.le
    apply Nat.mem_divisors.mpr
    constructor
    · refine ⟨ab.2, ?_⟩
      exact_mod_cast (hab.2.trans hmn.symm).symm
    · omega
  · intro ab₁ hab₁ ab₂ hab₂ hfst
    change ab₁ ∈ chen1973PairFiber N m at hab₁
    change ab₂ ∈ chen1973PairFiber N m at hab₂
    rw [chen1973PairFiber, Finset.mem_filter] at hab₁ hab₂
    have hprod : ab₁.1 * ab₁.2 = ab₂.1 * ab₂.2 := by
      exact_mod_cast hab₁.2.trans hab₂.2.symm
    apply Prod.ext hfst
    apply Nat.eq_of_mul_eq_mul_left
    · have hmem := (Finset.mem_product.mp hab₁.1).1
      exact lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hmem).1
    · simpa [hfst] using hprod

lemma chen1973_pairCoefficient_norm_le
    {N : ℕ} {s : ℂ} {m : ℤ}
    (hs : Chen1973Lemma3Domain s s.re s.im)
    (hm : m ∈ Icc (1 : ℤ) (N * N : ℕ)) :
    ‖chen1973PairCoefficient N s m‖ ≤
      (m.toNat.divisors.card : ℝ) * (m.toNat : ℝ) ^ (-(1 / 2 : ℝ)) := by
  have hmposZ : 0 < m := lt_of_lt_of_le Int.zero_lt_one (Finset.mem_Icc.mp hm).1
  have hmpos : 0 < m.toNat := by omega
  have hmone : (1 : ℝ) ≤ m.toNat := by exact_mod_cast hmpos
  unfold chen1973PairCoefficient
  rw [← Finset.sum_filter]
  calc
    ‖∑ ab ∈ chen1973PairFiber N m,
        (ab.1 : ℂ) ^ (-s) * (ab.2 : ℂ) ^ (-s)‖ ≤
      ∑ ab ∈ chen1973PairFiber N m,
        ‖(ab.1 : ℂ) ^ (-s) * (ab.2 : ℂ) ^ (-s)‖ := norm_sum_le _ _
    _ ≤ (chen1973PairFiber N m).card •
        ((m.toNat : ℝ) ^ (-(1 / 2 : ℝ))) := by
      apply Finset.sum_le_card_nsmul
      intro ab hab
      rw [chen1973PairFiber, Finset.mem_filter] at hab
      have habmem := Finset.mem_product.mp hab.1
      have hapos : (0 : ℝ) < ab.1 := by exact_mod_cast
        (lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp habmem.1).1)
      have hbpos : (0 : ℝ) < ab.2 := by exact_mod_cast
        (lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp habmem.2).1)
      have hprodNat : ab.1 * ab.2 = m.toNat := by
        have hmn : (m.toNat : ℤ) = m := Int.toNat_of_nonneg hmposZ.le
        exact_mod_cast hab.2.trans hmn.symm
      rw [norm_mul]
      change ‖((ab.1 : ℝ) : ℂ) ^ (-s)‖ * ‖((ab.2 : ℝ) : ℂ) ^ (-s)‖ ≤ _
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hapos,
        Complex.norm_cpow_eq_rpow_re_of_pos hbpos]
      simp only [neg_re]
      rw [← Real.mul_rpow hapos.le hbpos.le]
      have hprodR : (ab.1 : ℝ) * (ab.2 : ℝ) = (m.toNat : ℝ) := by
        exact_mod_cast hprodNat
      rw [hprodR]
      exact Real.rpow_le_rpow_of_exponent_le hmone (by linarith [hs.2])
    _ ≤ (m.toNat.divisors.card : ℝ) *
        (m.toNat : ℝ) ^ (-(1 / 2 : ℝ)) := by
      simp only [nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right
        (by exact_mod_cast chen1973PairFiber_card_le_divisors hm)
        (Real.rpow_nonneg (by positivity) _)

/-- Chen's collected coefficients have divisor-square energy bounded by four
harmonic factors.  This is the `∑ d(n)²/n` step on p. 115. -/
theorem chen1973_pairCoefficient_energy_le_harmonic_four
    (N : ℕ) (s : ℂ) (hs : Chen1973Lemma3Domain s s.re s.im) :
    (∑ m ∈ Icc (1 : ℤ) (N * N : ℕ),
      ‖chen1973PairCoefficient N s m‖ ^ 2) ≤
      liuHarmonic (N * N) ^ 4 := by
  calc
    (∑ m ∈ Icc (1 : ℤ) (N * N : ℕ),
        ‖chen1973PairCoefficient N s m‖ ^ 2) ≤
      ∑ m ∈ Icc (1 : ℤ) (N * N : ℕ),
        ((m.toNat.divisors.card : ℝ) ^ 2) * (m.toNat : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro m hm
      have h := chen1973_pairCoefficient_norm_le hs hm
      have hnon : 0 ≤ ‖chen1973PairCoefficient N s m‖ := norm_nonneg _
      have hsq := pow_le_pow_left₀ hnon h 2
      calc
        ‖chen1973PairCoefficient N s m‖ ^ 2 ≤
            ((m.toNat.divisors.card : ℝ) *
              (m.toNat : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 := hsq
        _ = ((m.toNat.divisors.card : ℝ) ^ 2) * (m.toNat : ℝ)⁻¹ := by
          have hmpos : (0 : ℝ) < m.toNat := by
            exact_mod_cast (show 0 < m.toNat by
              have : 0 < m := lt_of_lt_of_le Int.zero_lt_one
                (Finset.mem_Icc.mp hm).1
              omega)
          rw [mul_pow]
          congr 1
          rw [← Real.rpow_natCast]
          rw [← Real.rpow_mul hmpos.le]
          norm_num
          exact Real.rpow_neg_one _
    _ = ∑ n ∈ Icc 1 (N * N),
        ((n.divisors.card : ℝ) ^ 2) * (n : ℝ)⁻¹ := by
      simpa using sum_Icc_int_toNat_eq_sum_Icc
        (F := fun n => ((n.divisors.card : ℝ) ^ 2) * (n : ℝ)⁻¹) (N * N)
    _ ≤ liuHarmonic (N * N) ^ 4 :=
      divisorSquareWeightedPrefix_le_fourth_harmonic (N * N)

/-! ## The fourfold expansion followed by the literal Lemma 2 call -/

/-- The literal call to Chen's source equation (2).  Since the current source
module states (2) for real coefficient sequences, we apply it to real and
imaginary parts; the elementary complex split costs the absolute factor `2`.
No modern large-sieve constant is substituted. -/
theorem chen1973Lemma2_source_call_on_pairCoefficient
    (h2 : Chen1973Lemma2EquationTwo) (N Q : ℕ) (s : ℂ) :
    (∑ q ∈ Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
      ∑ χ : PrimitiveCharacter q,
        ‖chen1973DirichletPolynomial N s χ‖ ^ 4) ≤
      2 * (((Q : ℝ) ^ 2 + Real.pi * ((N * N : ℕ) : ℝ)) *
        ∑ m ∈ Icc (1 : ℤ) (N * N : ℕ),
          ‖chen1973PairCoefficient N s m‖ ^ 2) := by
  let c : ℤ → ℂ := chen1973PairCoefficient N s
  let aR : ℤ → ℝ := fun m => (c m).re
  let aI : ℤ → ℝ := fun m => (c m).im
  have hpoint : ∀ q : ℕ, ∀ χ : PrimitiveCharacter q,
      ‖∑ m ∈ Icc (1 : ℤ) (N * N : ℕ), c m * χ.1 (m : ZMod q)‖ ^ 2 ≤
        2 * (‖chen1973PrimitiveAmplitude aR 0 (N * N) q χ‖ ^ 2 +
          ‖chen1973PrimitiveAmplitude aI 0 (N * N) q χ‖ ^ 2) := by
    intro q χ
    let AR := chen1973PrimitiveAmplitude aR 0 (N * N) q χ
    let AI := chen1973PrimitiveAmplitude aI 0 (N * N) q χ
    have hdecomp :
        (∑ m ∈ Icc (1 : ℤ) (N * N : ℕ), c m * χ.1 (m : ZMod q)) =
          AR + I * AI := by
      dsimp [AR, AI, chen1973PrimitiveAmplitude]
      simp only [Int.zero_add]
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro m hm
      dsimp [aR, aI]
      calc
        c m * χ.1 (m : ZMod q) =
            (((c m).re : ℂ) + ((c m).im : ℂ) * I) * χ.1 (m : ZMod q) := by
              rw [Complex.re_add_im]
        _ = ((c m).re : ℂ) * χ.1 (m : ZMod q) +
            I * (((c m).im : ℂ) * χ.1 (m : ZMod q)) := by ring
    rw [hdecomp]
    have hadd := norm_add_le AR (I * AI)
    have hI : ‖I * AI‖ = ‖AI‖ := by simp
    rw [hI] at hadd
    have hnonR : 0 ≤ ‖AR‖ := norm_nonneg _
    have hnonI : 0 ≤ ‖AI‖ := norm_nonneg _
    have hsquare : ‖AR + I * AI‖ ^ 2 ≤ (‖AR‖ + ‖AI‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hadd 2
    dsimp [AR, AI]
    nlinarith [sq_nonneg (‖AR‖ - ‖AI‖)]
  have hR := h2 aR 0 (N * N) Q
  have hI := h2 aI 0 (N * N) Q
  calc
    (∑ q ∈ Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ : PrimitiveCharacter q,
          ‖chen1973DirichletPolynomial N s χ‖ ^ 4) =
      ∑ q ∈ Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ : PrimitiveCharacter q,
          ‖∑ m ∈ Icc (1 : ℤ) (N * N : ℕ),
            c m * χ.1 (m : ZMod q)‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro q hq
        congr 1
        apply Finset.sum_congr rfl
        intro χ hχ
        simpa only [c] using
          chen1973DirichletPolynomial_norm_four_eq_pair_norm_sq N s χ
    _ ≤ ∑ q ∈ Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ : PrimitiveCharacter q,
          2 * (‖chen1973PrimitiveAmplitude aR 0 (N * N) q χ‖ ^ 2 +
            ‖chen1973PrimitiveAmplitude aI 0 (N * N) q χ‖ ^ 2) := by
      apply Finset.sum_le_sum
      intro q hq
      apply mul_le_mul_of_nonneg_left
      · exact Finset.sum_le_sum fun χ hχ => hpoint q χ
      · positivity
    _ = 2 * ((∑ q ∈ Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
          ∑ χ : PrimitiveCharacter q,
            ‖chen1973PrimitiveAmplitude aR 0 (N * N) q χ‖ ^ 2) +
        (∑ q ∈ Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
          ∑ χ : PrimitiveCharacter q,
            ‖chen1973PrimitiveAmplitude aI 0 (N * N) q χ‖ ^ 2)) := by
      simp_rw [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum]
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib]
      have hmul (a b : ℝ) : a * (2 * b) = 2 * (a * b) := by ring
      simp_rw [hmul]
      rw [← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ 2 * ((((Q : ℝ) ^ 2 + Real.pi * ((N * N : ℕ) : ℝ)) *
          chen1973CoefficientEnergy aR 0 (N * N)) +
        (((Q : ℝ) ^ 2 + Real.pi * ((N * N : ℕ) : ℝ)) *
          chen1973CoefficientEnergy aI 0 (N * N))) := by
      gcongr
    _ = 2 * (((Q : ℝ) ^ 2 + Real.pi * ((N * N : ℕ) : ℝ)) *
        ∑ m ∈ Icc (1 : ℤ) (N * N : ℕ), ‖c m‖ ^ 2) := by
      unfold chen1973CoefficientEnergy
      simp only [Int.zero_add]
      apply congrArg (fun x : ℝ => 2 * x)
      rw [← mul_add, ← Finset.sum_add_distrib]
      apply congrArg (fun x : ℝ =>
        ((Q : ℝ) ^ 2 + Real.pi * ((N * N : ℕ) : ℝ)) * x)
      apply Finset.sum_congr rfl
      intro m hm
      dsimp [aR, aI]
      rw [Complex.sq_norm]
      simp only [Complex.normSq_apply, sq_abs]
      ring
    _ = _ := by rfl

/-- The actual large-sieve inequality obtained by applying Chen's Lemma 2 to
the collected coefficient sequence from the fourfold expansion.  No asymptotic
or divisor-square energy estimate is assumed here. -/
theorem chen1973Lemma2_call_on_pairCoefficient
    (N Q : ℕ) (s : ℂ) (hQ : 0 < Q) :
    (∑ q ∈ Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
      ∑ χ : PrimitiveCharacter q,
        ‖chen1973DirichletPolynomial N s χ‖ ^ 4) ≤
      primitiveLargeSieveConstant (N * N) Q *
        ∑ m ∈ Icc (1 : ℤ) (N * N : ℕ),
          ‖chen1973PairCoefficient N s m‖ ^ 2 := by
  have hLS := weighted_primitive_bombieri_davenport_explicit'
    (chen1973PairCoefficient N s) 0 (N * N) Q hQ
  simpa only [Int.zero_add, chen1973DirichletPolynomial_norm_four_eq_pair_norm_sq]
    using hLS

/-! ## Modulus one and the final finite fourth-moment assembly -/

/-- The value at modulus one is zero under the source convention used here. -/
@[simp] theorem chen1973PrimitiveLValue_one
    (s : ℂ) (χ : PrimitiveCharacter 1) :
    chen1973PrimitiveLValue 1 s χ = 0 := by
  simp [chen1973PrimitiveLValue]

/-- The matching source-family convention for the truncating polynomial. -/
def chen1973PrimitivePolynomialValue (q N : ℕ) (s : ℂ)
    (χ : PrimitiveCharacter q) : ℂ :=
  if 1 < q then chen1973DirichletPolynomial N s χ else 0

@[simp] theorem chen1973PrimitivePolynomialValue_one
    (N : ℕ) (s : ℂ) (χ : PrimitiveCharacter 1) :
    chen1973PrimitivePolynomialValue 1 N s χ = 0 := by
  simp [chen1973PrimitivePolynomialValue]

/-- Removing the harmless weight `q / φ(q)` from the polynomial fourth moment.
This is the exact finite-polynomial contribution in Chen's final display. -/
theorem chen1973DirichletPolynomial_fourthMoment_le
    (h2 : Chen1973Lemma2EquationTwo) (N Q : ℕ) (s : ℂ)
    (hs : Chen1973Lemma3Domain s s.re s.im) :
    (∑ q ∈ Icc 1 Q, ∑ χ : PrimitiveCharacter q,
      ‖chen1973DirichletPolynomial N s χ‖ ^ 4) ≤
      2 * (((Q : ℝ) ^ 2 + Real.pi * ((N * N : ℕ) : ℝ)) *
        liuHarmonic (N * N) ^ 4) := by
  calc
    (∑ q ∈ Icc 1 Q, ∑ χ : PrimitiveCharacter q,
        ‖chen1973DirichletPolynomial N s χ‖ ^ 4) ≤
      ∑ q ∈ Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ : PrimitiveCharacter q,
          ‖chen1973DirichletPolynomial N s χ‖ ^ 4 := by
      apply Finset.sum_le_sum
      intro q hq
      have hqpos : 0 < q := (Finset.mem_Icc.mp hq).1
      have hφpos : (0 : ℝ) < q.totient := by
        exact_mod_cast Nat.totient_pos.mpr hqpos
      have hφle : (q.totient : ℝ) ≤ q := by
        exact_mod_cast Nat.totient_le q
      have hone : (1 : ℝ) ≤ (q : ℝ) / q.totient := by
        rw [le_div_iff₀ hφpos]
        simpa [one_mul] using hφle
      exact le_mul_of_one_le_left (Finset.sum_nonneg fun χ hχ => by positivity) hone
    _ ≤ 2 * (((Q : ℝ) ^ 2 + Real.pi * ((N * N : ℕ) : ℝ)) *
        ∑ m ∈ Icc (1 : ℤ) (N * N : ℕ),
          ‖chen1973PairCoefficient N s m‖ ^ 2) :=
      chen1973Lemma2_source_call_on_pairCoefficient h2 N Q s
    _ ≤ 2 * (((Q : ℝ) ^ 2 + Real.pi * ((N * N : ℕ) : ℝ)) *
        liuHarmonic (N * N) ^ 4) := by
      gcongr
      exact chen1973_pairCoefficient_energy_le_harmonic_four N s
        hs

/-- The PV--Abel errors aggregated over the complete finite starred family.
The modulus-one lane vanishes by the explicit source convention. -/
theorem chen1973_truncation_error_fourth_sum_le
    (N Q : ℕ) (s : ℂ) (hs : Chen1973Lemma3Domain s s.re s.im) :
    (∑ q ∈ Icc 1 Q, ∑ χ : PrimitiveCharacter q,
      ‖chen1973PrimitiveLValue q s χ -
        chen1973PrimitivePolynomialValue q N s χ‖ ^ 4) ≤
      ∑ q ∈ Icc 1 Q, (Fintype.card (PrimitiveCharacter q) : ℝ) *
        (40 * ‖s‖ * Real.sqrt q * Real.log q *
          (((N + 1 : ℕ) : ℝ) ^ (-s.re))) ^ 4 := by
  apply Finset.sum_le_sum
  intro q hq
  by_cases hq1 : 1 < q
  · letI : NeZero q := ⟨Nat.ne_zero_of_lt hq1⟩
    calc
      (∑ χ : PrimitiveCharacter q,
          ‖chen1973PrimitiveLValue q s χ -
            chen1973PrimitivePolynomialValue q N s χ‖ ^ 4) ≤
        ∑ _χ : PrimitiveCharacter q,
          (40 * ‖s‖ * Real.sqrt q * Real.log q *
            (((N + 1 : ℕ) : ℝ) ^ (-s.re))) ^ 4 := by
          apply Finset.sum_le_sum
          intro χ hχ
          have h := chen1973_LFunction_sub_polynomial_le_forty hq1 χ N s hs
          have hpow := pow_le_pow_left₀ (norm_nonneg _) h 4
          simpa [chen1973PrimitiveLValue, chen1973PrimitivePolynomialValue, hq1]
            using hpow
      _ = _ := by simp
  · have hqeq : q = 1 := by
      have hqpos := (Finset.mem_Icc.mp hq).1
      omega
    subst q
    simp

/-- A pointwise fourth-power split used to aggregate the truncation errors. -/
lemma norm_four_le_eight_add_norm_sub_four (z w : ℂ) :
    ‖z‖ ^ 4 ≤ 8 * (‖w‖ ^ 4 + ‖z - w‖ ^ 4) := by
  have hz : z = w + (z - w) := by ring
  have h : ‖z‖ ≤ ‖w‖ + ‖z - w‖ := by
    calc
      ‖z‖ = ‖w + (z - w)‖ := congrArg norm hz
      _ ≤ ‖w‖ + ‖z - w‖ := norm_add_le w (z - w)
  have hpow := pow_le_pow_left₀ (norm_nonneg _) h 4
  nlinarith [sq_nonneg (‖w‖ - ‖z - w‖),
    sq_nonneg (‖w‖ ^ 2 - ‖z - w‖ ^ 2)]

/-- The exact final finite assembly before Chen's last scalar simplification.
It keeps the truncation-error fourth powers explicit, so no endpoint or family
cardinality convention is hidden. -/
theorem chen1973Lemma3_fourthMoment_finite_assembly
    (h2 : Chen1973Lemma2EquationTwo) (N Q : ℕ) (s : ℂ)
    (hs : Chen1973Lemma3Domain s s.re s.im) :
    chen1973Lemma3FourthMoment Q s ≤
      16 * (((Q : ℝ) ^ 2 + Real.pi * ((N * N : ℕ) : ℝ)) *
        liuHarmonic (N * N) ^ 4) +
      8 * ∑ q ∈ Icc 1 Q, ∑ χ : PrimitiveCharacter q,
        ‖chen1973PrimitiveLValue q s χ -
          chen1973PrimitivePolynomialValue q N s χ‖ ^ 4 := by
  unfold chen1973Lemma3FourthMoment
  calc
    (∑ q ∈ Icc 1 Q, ∑ χ : PrimitiveCharacter q,
        ‖chen1973PrimitiveLValue q s χ‖ ^ 4) ≤
      ∑ q ∈ Icc 1 Q, ∑ χ : PrimitiveCharacter q,
        8 * (‖chen1973PrimitivePolynomialValue q N s χ‖ ^ 4 +
          ‖chen1973PrimitiveLValue q s χ -
            chen1973PrimitivePolynomialValue q N s χ‖ ^ 4) := by
      exact Finset.sum_le_sum fun q hq => Finset.sum_le_sum fun χ hχ =>
        norm_four_le_eight_add_norm_sub_four _ _
    _ = 8 * (∑ q ∈ Icc 1 Q, ∑ χ : PrimitiveCharacter q,
          ‖chen1973PrimitivePolynomialValue q N s χ‖ ^ 4) +
        8 * ∑ q ∈ Icc 1 Q, ∑ χ : PrimitiveCharacter q,
          ‖chen1973PrimitiveLValue q s χ -
            chen1973PrimitivePolynomialValue q N s χ‖ ^ 4 := by
      simp_rw [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum]
    _ ≤ 16 * (((Q : ℝ) ^ 2 + Real.pi * ((N * N : ℕ) : ℝ)) *
          liuHarmonic (N * N) ^ 4) +
        8 * ∑ q ∈ Icc 1 Q, ∑ χ : PrimitiveCharacter q,
          ‖chen1973PrimitiveLValue q s χ -
            chen1973PrimitivePolynomialValue q N s χ‖ ^ 4 := by
      have hpoly :
          (∑ q ∈ Icc 1 Q, ∑ χ : PrimitiveCharacter q,
            ‖chen1973PrimitivePolynomialValue q N s χ‖ ^ 4) ≤
          ∑ q ∈ Icc 1 Q, ∑ χ : PrimitiveCharacter q,
            ‖chen1973DirichletPolynomial N s χ‖ ^ 4 := by
        apply Finset.sum_le_sum
        intro q hq
        by_cases hq1 : 1 < q
        · simp [chen1973PrimitivePolynomialValue, hq1]
        · simp only [chen1973PrimitivePolynomialValue, if_neg hq1, norm_zero,
            zero_pow (by norm_num : (4 : ℕ) ≠ 0), Finset.sum_const_zero]
          exact Finset.sum_nonneg fun χ hχ => by positivity
      have hp0 := chen1973DirichletPolynomial_fourthMoment_le h2 N Q s hs
      have hp := hpoly.trans hp0
      linarith

/-! ## Corrected unrestricted-height endpoint and bounded-height specialization

The source calculation naturally yields `log (Q * (1 + ‖s‖)) ^ 4`.  The
`log Q ^ 4` form below is therefore stated only under the explicit additional
hypothesis `‖s‖ ≤ Q ^ A`.  Both endpoints retain the preceding finite assembly.
-/

def chen1973Lemma3LogScale (Q : ℕ) (s : ℂ) : ℝ :=
  Real.log ((Q : ℝ) * (1 + ‖s‖))

lemma chen1973Lemma3_norm_half {s : ℂ}
    (hs : Chen1973Lemma3Domain s s.re s.im) : (1 / 2 : ℝ) ≤ ‖s‖ := by
  exact hs.2.trans (Complex.re_le_norm s)

lemma chen1973Lemma3_logScale_pos {Q : ℕ} {s : ℂ} (hQ : 2 ≤ Q) :
    0 < chen1973Lemma3LogScale Q s := by
  apply Real.log_pos
  have hQr : (2 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hn : 0 ≤ ‖s‖ := norm_nonneg s
  nlinarith

lemma chen1973Lemma3_cutoff_square_add_one_le
    {Q : ℕ} {s : ℂ} (hQ : 2 ≤ Q) :
    ((chen1973Lemma3Cutoff Q s * chen1973Lemma3Cutoff Q s + 1 : ℕ) : ℝ) ≤
      ((Q : ℝ) * (1 + ‖s‖)) ^ 2 := by
  have hc := chen1973Lemma3Cutoff_le Q s
  have hQr : (2 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hn : 0 ≤ ‖s‖ := norm_nonneg s
  norm_num [Nat.cast_add, Nat.cast_mul]
  nlinarith [sq_nonneg ((Q : ℝ) * ‖s‖ - chen1973Lemma3Cutoff Q s)]

lemma chen1973Lemma3_harmonic_le_logScale
    {Q : ℕ} {s : ℂ} (hQ : 2 ≤ Q) :
    liuHarmonic (chen1973Lemma3Cutoff Q s * chen1973Lemma3Cutoff Q s) ≤
      6 * chen1973Lemma3LogScale Q s := by
  let X := chen1973Lemma3Cutoff Q s * chen1973Lemma3Cutoff Q s
  let A : ℝ := (Q : ℝ) * (1 + ‖s‖)
  have hA : 0 < A := by
    dsimp [A]
    positivity
  have hXA : ((X + 1 : ℕ) : ℝ) ≤ A ^ 2 := by
    simpa [X, A] using chen1973Lemma3_cutoff_square_add_one_le (Q := Q) (s := s) hQ
  have hlog : Real.log (X + 1 : ℕ) ≤ Real.log (A ^ 2) :=
    Real.log_le_log (by positivity) hXA
  have hlogA : Real.log (A ^ 2) = 2 * Real.log A := by
    rw [Real.log_pow]
    norm_num
  have hH := liuHarmonic_le_three_log_add_one X
  dsimp [chen1973Lemma3LogScale]
  rw [hlogA] at hlog
  dsimp [A] at hlog ⊢
  linarith

lemma chen1973Lemma3_cutoff_decay_four
    {Q : ℕ} {s : ℂ} (hQ : 2 ≤ Q)
    (hs : Chen1973Lemma3Domain s s.re s.im) :
    ((((chen1973Lemma3Cutoff Q s + 1 : ℕ) : ℝ) ^ (-s.re)) ^ 4) ≤
      (((Q : ℝ) * ‖s‖)⁻¹) ^ 2 := by
  let B : ℝ := ((chen1973Lemma3Cutoff Q s + 1 : ℕ) : ℝ)
  let A : ℝ := (Q : ℝ) * ‖s‖
  have hn := chen1973Lemma3_norm_half hs
  have hQr : (2 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hA : 0 < A := by dsimp [A]; positivity
  have hB : 1 ≤ B := by dsimp [B]; exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by omega)
  have hAB : A ≤ B := by
    dsimp [A, B]
    simpa only [Nat.cast_add, Nat.cast_one] using
      (chen1973Lemma3Cutoff_lt_succ Q s).le
  have hfirst : B ^ (-s.re) ≤ B ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hB (by linarith [hs.2])
  have hsecond : B ^ (-(1 / 2 : ℝ)) ≤ A ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hA hAB (by norm_num)
  have hp : B ^ (-s.re) ≤ A ^ (-(1 / 2 : ℝ)) := hfirst.trans hsecond
  have hp0 : 0 ≤ B ^ (-s.re) := Real.rpow_nonneg (by positivity) _
  have hp4 := pow_le_pow_left₀ hp0 hp 4
  have heq : (A ^ (-(1 / 2 : ℝ))) ^ 4 = A⁻¹ ^ 2 := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul hA.le]
    norm_num
  dsimp [B, A] at hp4 heq ⊢
  rwa [heq] at hp4

lemma chen1973Lemma3_truncation_pointwise_scalar
    {Q q : ℕ} {s : ℂ} (hQ : 2 ≤ Q) (hq0 : 1 ≤ q) (hq : q ≤ Q)
    (hs : Chen1973Lemma3Domain s s.re s.im) :
    (40 * ‖s‖ * Real.sqrt q * Real.log q *
      (((chen1973Lemma3Cutoff Q s + 1 : ℕ) : ℝ) ^ (-s.re))) ^ 4 ≤
      2560000 * ‖s‖ ^ 2 * (q : ℝ) ^ 2 / (Q : ℝ) ^ 2 *
        chen1973Lemma3LogScale Q s ^ 4 := by
  let p : ℝ := (((chen1973Lemma3Cutoff Q s + 1 : ℕ) : ℝ) ^ (-s.re))
  let L : ℝ := chen1973Lemma3LogScale Q s
  have hn := chen1973Lemma3_norm_half hs
  have hn0 : 0 < ‖s‖ := lt_of_lt_of_le (by norm_num) hn
  have hQr : (0 : ℝ) < Q := by positivity
  have hqr : (0 : ℝ) ≤ q := by positivity
  have hlogq0 : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq0)
  have hL0 : 0 ≤ L := (chen1973Lemma3_logScale_pos (Q := Q) (s := s) hQ).le
  have harg : (q : ℝ) ≤ (Q : ℝ) * (1 + ‖s‖) := by
    have hqR : (q : ℝ) ≤ Q := by exact_mod_cast hq
    have hnnon : 0 ≤ ‖s‖ := norm_nonneg s
    nlinarith
  have hlog : Real.log q ≤ L := by
    dsimp [L, chen1973Lemma3LogScale]
    exact Real.log_le_log (by exact_mod_cast hq0) harg
  have hlog4 : Real.log q ^ 4 ≤ L ^ 4 := pow_le_pow_left₀ hlogq0 hlog 4
  have hp4 : p ^ 4 ≤ (((Q : ℝ) * ‖s‖)⁻¹) ^ 2 := by
    simpa [p] using chen1973Lemma3_cutoff_decay_four (Q := Q) (s := s) hQ hs
  have hsqrt : (Real.sqrt q) ^ 4 = (q : ℝ) ^ 2 := by
    rw [show (Real.sqrt q) ^ 4 = ((Real.sqrt q) ^ 2) ^ 2 by ring,
      Real.sq_sqrt hqr]
  calc
    (40 * ‖s‖ * Real.sqrt q * Real.log q * p) ^ 4 =
        2560000 * ‖s‖ ^ 4 * (Real.sqrt q) ^ 4 * Real.log q ^ 4 * p ^ 4 := by
          ring
    _ = 2560000 * ‖s‖ ^ 4 * (q : ℝ) ^ 2 * Real.log q ^ 4 * p ^ 4 := by
          rw [hsqrt]
    _ ≤ 2560000 * ‖s‖ ^ 4 * (q : ℝ) ^ 2 * L ^ 4 *
        (((Q : ℝ) * ‖s‖)⁻¹) ^ 2 := by gcongr
    _ = 2560000 * ‖s‖ ^ 2 * (q : ℝ) ^ 2 / (Q : ℝ) ^ 2 * L ^ 4 := by
      field_simp

private lemma chen1973_card_primitive_le_totient (q : ℕ) (hq : 0 < q) :
    Fintype.card (PrimitiveCharacter q) ≤ q.totient := by
  let _ : NeZero q := ⟨Nat.ne_of_gt hq⟩
  calc
    Fintype.card (PrimitiveCharacter q) ≤
        Fintype.card (DirichletCharacter ℂ q) :=
      @Fintype.card_subtype_le (DirichletCharacter ℂ q) _
        (fun χ => χ.IsPrimitive) _
    _ = q.totient := by
      have h := DirichletCharacter.sum_char_inv_mul_char_eq ℂ
        (a := (1 : ZMod q)) isUnit_one (1 : ZMod q)
      simpa using h

theorem chen1973Lemma3_truncation_error_sum_scalar
    {Q : ℕ} {s : ℂ} (hQ : 2 ≤ Q)
    (hs : Chen1973Lemma3Domain s s.re s.im) :
    (∑ q ∈ Icc 1 Q, ∑ χ : PrimitiveCharacter q,
      ‖chen1973PrimitiveLValue q s χ -
        chen1973PrimitivePolynomialValue q (chen1973Lemma3Cutoff Q s) s χ‖ ^ 4) ≤
      2560000 * (Q : ℝ) ^ 2 * ‖s‖ ^ 2 * chen1973Lemma3LogScale Q s ^ 4 := by
  let N := chen1973Lemma3Cutoff Q s
  let L := chen1973Lemma3LogScale Q s
  have hbase := chen1973_truncation_error_fourth_sum_le N Q s hs
  refine hbase.trans ?_
  calc
    (∑ q ∈ Icc 1 Q, (Fintype.card (PrimitiveCharacter q) : ℝ) *
        (40 * ‖s‖ * Real.sqrt q * Real.log q *
          (((N + 1 : ℕ) : ℝ) ^ (-s.re))) ^ 4) ≤
      ∑ q ∈ Icc 1 Q, 2560000 * ‖s‖ ^ 2 * (Q : ℝ) * L ^ 4 := by
        apply Finset.sum_le_sum
        intro q hq
        have hq0 := (Finset.mem_Icc.mp hq).1
        have hqQ := (Finset.mem_Icc.mp hq).2
        have hcardNat : Fintype.card (PrimitiveCharacter q) ≤ q.totient :=
          chen1973_card_primitive_le_totient q (by omega)
        have hcard : (Fintype.card (PrimitiveCharacter q) : ℝ) ≤ q := by
          exact_mod_cast hcardNat.trans (Nat.totient_le q)
        have hraw := chen1973Lemma3_truncation_pointwise_scalar (Q := Q) (q := q) (s := s) hQ hq0 hqQ hs
        have hterm0 : 0 ≤ (40 * ‖s‖ * Real.sqrt q * Real.log q *
            (((chen1973Lemma3Cutoff Q s + 1 : ℕ) : ℝ) ^ (-s.re))) ^ 4 := by
          positivity
        calc
          (Fintype.card (PrimitiveCharacter q) : ℝ) *
              (40 * ‖s‖ * Real.sqrt q * Real.log q *
                (((N + 1 : ℕ) : ℝ) ^ (-s.re))) ^ 4 ≤
            (q : ℝ) * (40 * ‖s‖ * Real.sqrt q * Real.log q *
                (((N + 1 : ℕ) : ℝ) ^ (-s.re))) ^ 4 := by
                  gcongr
          _ ≤ (q : ℝ) * (2560000 * ‖s‖ ^ 2 * (q : ℝ) ^ 2 /
                (Q : ℝ) ^ 2 * L ^ 4) := by
                  gcongr
          _ ≤ (Q : ℝ) * (2560000 * ‖s‖ ^ 2 * (Q : ℝ) ^ 2 /
                (Q : ℝ) ^ 2 * L ^ 4) := by gcongr
          _ = 2560000 * ‖s‖ ^ 2 * (Q : ℝ) * L ^ 4 := by
                have hQr : (Q : ℝ) ≠ 0 := by positivity
                field_simp
    _ = 2560000 * (Q : ℝ) ^ 2 * ‖s‖ ^ 2 * L ^ 4 := by
      simp only [Finset.sum_const, nsmul_eq_mul, Nat.card_Icc]
      norm_num
      ring
    _ = _ := by rfl



/-- The corrected unrestricted-height form of Chen's Lemma 3.  Unlike the
printed final line, the fourth logarithm retains the conductor-height scale
forced by the cutoff `⌊Q‖s‖⌋₊`. -/
theorem chen1973Lemma3_corrected_endpoint
    (h2 : Chen1973Lemma2EquationTwo) {Q : ℕ} (s : ℂ) (hQ : 2 ≤ Q)
    (hs : Chen1973Lemma3Domain s s.re s.im) :
    chen1973Lemma3FourthMoment Q s ≤
      21000000 * (Q : ℝ) ^ 2 * ‖s‖ ^ 2 *
        Real.log ((Q : ℝ) * (1 + ‖s‖)) ^ 4 := by
  let N := chen1973Lemma3Cutoff Q s
  let L := chen1973Lemma3LogScale Q s
  have hfin := chen1973Lemma3_fourthMoment_finite_assembly h2 N Q s hs
  have hH := chen1973Lemma3_harmonic_le_logScale (Q := Q) (s := s) hQ
  have hH0 : 0 ≤ liuHarmonic (N * N) := by
    unfold liuHarmonic
    positivity
  have hH4 : liuHarmonic (N * N) ^ 4 ≤ (6 * L) ^ 4 := by
    exact pow_le_pow_left₀ hH0 (by simpa [N, L] using hH) 4
  have herr := chen1973Lemma3_truncation_error_sum_scalar (Q := Q) (s := s) hQ hs
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
    chen1973Lemma3FourthMoment Q s ≤
        16 * (((Q : ℝ) ^ 2 + Real.pi * (((N * N : ℕ) : ℝ))) *
          liuHarmonic (N * N) ^ 4) +
        8 * ∑ q ∈ Icc 1 Q, ∑ χ : PrimitiveCharacter q,
          ‖chen1973PrimitiveLValue q s χ -
            chen1973PrimitivePolynomialValue q N s χ‖ ^ 4 := hfin
    _ ≤ 16 * ((8 * (Q : ℝ) ^ 2 * ‖s‖ ^ 2) * (6 * L) ^ 4) +
        8 * (2560000 * (Q : ℝ) ^ 2 * ‖s‖ ^ 2 * L ^ 4) := by gcongr
    _ = 20645888 * (Q : ℝ) ^ 2 * ‖s‖ ^ 2 * L ^ 4 := by ring
    _ ≤ 21000000 * (Q : ℝ) ^ 2 * ‖s‖ ^ 2 * L ^ 4 := by gcongr; norm_num



lemma chen1973Lemma3_logScale_le_bounded_height
    {Q A : ℕ} {s : ℂ} (hQ : 2 ≤ Q)
    (hheight : ‖s‖ ≤ (Q : ℝ) ^ A) :
    chen1973Lemma3LogScale Q s ≤ (A + 2 : ℕ) * Real.log Q := by
  have hQr : (2 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hQ0 : (0 : ℝ) < Q := by positivity
  have hpow0 : 0 ≤ (Q : ℝ) ^ A := by positivity
  have harg : (Q : ℝ) * (1 + ‖s‖) ≤ (Q : ℝ) ^ (A + 2) := by
    calc
      (Q : ℝ) * (1 + ‖s‖) ≤ (Q : ℝ) * (1 + (Q : ℝ) ^ A) := by gcongr
      _ ≤ (Q : ℝ) * (2 * (Q : ℝ) ^ A) := by
        gcongr
        nlinarith [show (1 : ℝ) ≤ (Q : ℝ) ^ A by
          exact one_le_pow₀ (by linarith)]
      _ ≤ (Q : ℝ) * ((Q : ℝ) * (Q : ℝ) ^ A) := by gcongr
      _ = (Q : ℝ) ^ (A + 2) := by
        rw [pow_add]
        ring
  have hlog := Real.log_le_log (by positivity : 0 < (Q : ℝ) * (1 + ‖s‖)) harg
  dsimp [chen1973Lemma3LogScale]
  rw [Real.log_pow] at hlog
  simpa [Nat.cast_add, Nat.cast_ofNat] using hlog

/-- Chen's printed `log Q` fourth power is valid after adding the explicit
bounded-height hypothesis `‖s‖ ≤ Q^A`; it is not an unconditional source claim. -/
theorem chen1973Lemma3_bounded_height_specialization
    (h2 : Chen1973Lemma2EquationTwo) {Q A : ℕ} (s : ℂ) (hQ : 2 ≤ Q)
    (hs : Chen1973Lemma3Domain s s.re s.im)
    (hheight : ‖s‖ ≤ (Q : ℝ) ^ A) :
    chen1973Lemma3FourthMoment Q s ≤
      21000000 * (A + 2 : ℕ) ^ 4 * (Q : ℝ) ^ 2 * ‖s‖ ^ 2 *
        Real.log Q ^ 4 := by
  have hmain := chen1973Lemma3_corrected_endpoint h2 s hQ hs
  have hlog := chen1973Lemma3_logScale_le_bounded_height hQ hheight
  have hlog0 : 0 ≤ chen1973Lemma3LogScale Q s := (chen1973Lemma3_logScale_pos hQ).le
  have hlog4 := pow_le_pow_left₀ hlog0 hlog 4
  calc
    chen1973Lemma3FourthMoment Q s ≤
        21000000 * (Q : ℝ) ^ 2 * ‖s‖ ^ 2 * chen1973Lemma3LogScale Q s ^ 4 := hmain
    _ ≤ 21000000 * (Q : ℝ) ^ 2 * ‖s‖ ^ 2 *
        (((A + 2 : ℕ) : ℝ) * Real.log Q) ^ 4 := by gcongr
    _ = 21000000 * (A + 2 : ℕ) ^ 4 * (Q : ℝ) ^ 2 * ‖s‖ ^ 2 *
        Real.log Q ^ 4 := by push_cast; ring

/-- The corrected unrestricted-height endpoint with Chen's Lemma 2 discharged
by the now-proved exact Farey formula (4). -/
theorem chen1973Lemma3_corrected_endpoint_unconditional
    {Q : ℕ} (s : ℂ) (hQ : 2 ≤ Q)
    (hs : Chen1973Lemma3Domain s s.re s.im) :
    chen1973Lemma3FourthMoment Q s ≤
      21000000 * (Q : ℝ) ^ 2 * ‖s‖ ^ 2 *
        Real.log ((Q : ℝ) * (1 + ‖s‖)) ^ 4 :=
  chen1973Lemma3_corrected_endpoint
    (chen1973Lemma2_equationTwo_of_fareyEquationFour chen1973FareyEquationFour)
    s hQ hs

/-- The bounded-height specialization with the exact source Lemma 2 input
discharged unconditionally. -/
theorem chen1973Lemma3_bounded_height_specialization_unconditional
    {Q A : ℕ} (s : ℂ) (hQ : 2 ≤ Q)
    (hs : Chen1973Lemma3Domain s s.re s.im)
    (hheight : ‖s‖ ≤ (Q : ℝ) ^ A) :
    chen1973Lemma3FourthMoment Q s ≤
      21000000 * (A + 2 : ℕ) ^ 4 * (Q : ℝ) ^ 2 * ‖s‖ ^ 2 *
        Real.log Q ^ 4 :=
  chen1973Lemma3_bounded_height_specialization
    (chen1973Lemma2_equationTwo_of_fareyEquationFour chen1973FareyEquationFour)
    s hQ hs hheight

/-!
## Source-strength audit of the last displayed line

The scan defines `∑*` only as a primitive-character sum; it does not explicitly
say that modulus `1` is omitted.  Nevertheless the proof uses the nonprincipal
Dirichlet series and the factor `log q`, so its displayed argument necessarily
uses the classical convention that this starred family starts at `q = 2`.
Mathlib's `PrimitiveCharacter 1` is nonempty and its `LFunction` is zeta, which
has a pole at `s = 1`; including it would make the stated uniform half-plane
lemma false.  The explicit zero above therefore records a mathematically forced
source convention rather than changing Mathlib's primitive-character type.

There is a second, independent issue in the last scalar step.  The proved energy
is `liuHarmonic (⌊Q‖s‖⌋²)^4`, naturally of size
`log(Q‖s‖)^4`.  The printed lemma has no restriction on `t` or `‖s‖`, but replaces
this by `log Q^4`.  That replacement is not uniform for unrestricted height and
does not follow from the displayed argument.  Accordingly the theorem above is
the complete source-faithful finite assembly; no false `Q²‖s‖²(log Q)^4`
wrapper is introduced.
-/

end AnalyticNumberTheory.LargeSieve
