/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nous Research
-/
import MathlibNt.AnalyticNumberTheory.Chen1973.Chen1973Lemma6Equations16And17
import MathlibNt.AnalyticNumberTheory.Chen1973.Chen1973Lemma6Equations14And15
import MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLConditionalValueSeries
import AnalyticNumberTheory.LargeSieve.BombieriDavenport
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

/-!
# Conjugation symmetry for Chen's equation (17)

This file proves the conjugation identities for the actual primitive-character
family and the actual finite polynomials occurring in equation (17).  It then
uses those identities to replace the full vertical-line norm integrals by twice
the half-line integrals already used in `Chen1973Lemma6Equations16And17`.
-/

noncomputable section

open Classical Complex Finset Filter MeasureTheory Set
open scoped BigOperators ArithmeticFunction Topology

namespace AnalyticNumberTheory.LargeSieve

local notation "conj" => starRingEnd ℂ
open DirichletLAbelWeightVariation DirichletLConditionalValueSeries

/-- Conjugation is an involutive equivalence of primitive characters of a
fixed nonzero modulus. -/
def primitiveCharacterConjEquiv (q : ℕ) [NeZero q] :
    PrimitiveCharacter q ≃ PrimitiveCharacter q where
  toFun χ := ⟨star χ.1, AnalyticNumberTheory.LargeSieve.star_isPrimitive χ.1 χ.2⟩
  invFun χ := ⟨star χ.1, AnalyticNumberTheory.LargeSieve.star_isPrimitive χ.1 χ.2⟩
  left_inv χ := by ext; simp
  right_inv χ := by ext; simp

@[simp] theorem primitiveCharacterConjEquiv_val (q : ℕ) [NeZero q]
    (χ : PrimitiveCharacter q) :
    (primitiveCharacterConjEquiv q χ).1 = star χ.1 := rfl

@[simp] theorem primitiveCharacterConjEquiv_apply_apply (q : ℕ) [NeZero q]
    (χ : PrimitiveCharacter q) :
    primitiveCharacterConjEquiv q (primitiveCharacterConjEquiv q χ) = χ := by
  exact (primitiveCharacterConjEquiv q).apply_symm_apply χ

private lemma conj_cpow_nat (s : ℂ) (n : ℕ) :
    conj ((n : ℂ) ^ s) = (n : ℂ) ^ (conj s) := by
  have harg : ((n : ℂ)).arg ≠ Real.pi := by
    change (((n : ℝ) : ℂ)).arg ≠ Real.pi
    rw [Complex.arg_ofReal_of_nonneg (by positivity)]
    exact ne_of_lt Real.pi_pos
  simpa using (Complex.cpow_conj (n : ℂ) s harg).symm

/-- General (not merely quadratic) conjugation of a natural-order partial
Dirichlet sum. -/
theorem conj_sum_range_cpowWeight_character
    {q : ℕ} [NeZero q] (χ : PrimitiveCharacter q) (s : ℂ) (N : ℕ) :
    conj (∑ n ∈ range N,
      cpowWeight s n * χ.1 n) =
      ∑ n ∈ range N,
        cpowWeight (conj s) n *
          (primitiveCharacterConjEquiv q χ).1 n := by
  rw [map_sum]
  apply sum_congr rfl
  intro n hn
  rw [map_mul]
  change conj (cpowWeight s n) * conj (χ.1 n) = _
  have harg : ((n : ℂ)).arg ≠ Real.pi := by
    change (((n : ℝ) : ℂ)).arg ≠ Real.pi
    rw [Complex.arg_ofReal_of_nonneg (by positivity)]
    exact ne_of_lt Real.pi_pos
  unfold cpowWeight
  rw [primitiveCharacterConjEquiv_val]
  change conj ((n : ℂ) ^ (-s)) * conj (χ.1 n) =
    (n : ℂ) ^ (-(conj s)) * conj (χ.1 n)
  congr 1
  simpa using (Complex.cpow_conj (n : ℂ) (-s) harg).symm

/-- Conjugation identity for a primitive Dirichlet L-function on the whole
conditional-convergence half-plane. -/
theorem primitiveLFunction_conj
    {q : ℕ} [NeZero q] (χ : PrimitiveCharacter q)
    (hχ : χ.1 ≠ 1) (s : ℂ) (hs : 0 < s.re) :
    (primitiveCharacterConjEquiv q χ).1.LFunction (conj s) =
      conj (χ.1.LFunction s) := by
  have hstar : (primitiveCharacterConjEquiv q χ).1 ≠ 1 := by
    intro h
    apply hχ
    have := congrArg star h
    simpa using this
  have hsc : 0 < (conj s).re := by simpa using hs
  have hleft := tendsto_sum_range_orderedValueSeries
    (primitiveCharacterConjEquiv q χ).1 hstar (conj s) hsc
  have hright0 := tendsto_sum_range_orderedValueSeries
    χ.1 hχ s hs
  have hright :
      Tendsto (fun N : ℕ => conj (∑ n ∈ range N,
        cpowWeight s n * χ.1 n)) atTop
        (𝓝 (conj (orderedValueSeries χ.1 hχ s hs))) :=
    (Complex.continuous_conj.tendsto
      (orderedValueSeries χ.1 hχ s hs)).comp hright0
  have hright' :
      Tendsto (fun N : ℕ => ∑ n ∈ range N,
        cpowWeight (conj s) n *
          (primitiveCharacterConjEquiv q χ).1 n) atTop
        (𝓝 (conj (orderedValueSeries χ.1 hχ s hs))) := by
    refine (tendsto_congr' (Eventually.of_forall fun N => ?_)).mp hright
    exact conj_sum_range_cpowWeight_character χ s N
  have hord := tendsto_nhds_unique hleft hright'
  rw [orderedValueSeries_eq_LFunction_of_re_pos
      (primitiveCharacterConjEquiv q χ).1 hstar (conj s) hsc,
    orderedValueSeries_eq_LFunction_of_re_pos χ.1 hχ s hs] at hord
  exact hord

/-- The derivative of a primitive L-function obeys the same conjugation law.
The proof differentiates the locally equal holomorphic functions
`L(s,star χ)` and `conj (L(conj s,χ))`. -/
theorem primitiveLDeriv_conj
    {q : ℕ} [NeZero q] (χ : PrimitiveCharacter q)
    (hχ : χ.1 ≠ 1) (s : ℂ) (hs : 0 < s.re) :
    deriv (primitiveCharacterConjEquiv q χ).1.LFunction (conj s) =
      conj (deriv χ.1.LFunction s) := by
  have hstar : (primitiveCharacterConjEquiv q χ).1 ≠ 1 := by
    intro h
    apply hχ
    have := congrArg star h
    simpa using this
  let F : ℂ → ℂ := fun z => conj (χ.1.LFunction (conj z))
  have hF : HasDerivAt F (conj (deriv χ.1.LFunction s)) (conj s) := by
    simpa [F, Function.comp_def] using
      (DirichletCharacter.lFunction_entire_of_ne_one hχ).differentiableAt.hasDerivAt.conj_conj
  have hopen : IsOpen {z : ℂ | 0 < z.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hmem : conj s ∈ {z : ℂ | 0 < z.re} := by simpa using hs
  have heq : (fun z => (primitiveCharacterConjEquiv q χ).1.LFunction z) =ᶠ[𝓝 (conj s)] F := by
    filter_upwards [hopen.mem_nhds hmem] with z hz
    have hz' : 0 < (conj z).re := by
      simpa only [Set.mem_setOf_eq, Complex.conj_re] using hz
    simpa [F] using primitiveLFunction_conj χ hχ (conj z) hz'
  exact (hF.congr_of_eventuallyEq heq).deriv

/-- Conjugation identity for Chen's natural-order `S(H,s,χ)`. -/
theorem chen1973Lemma6MobiusPartialSum_conj
    {q : ℕ} [NeZero q] (H : ℕ) (s : ℂ) (χ : PrimitiveCharacter q) :
    chen1973Lemma6MobiusPartialSum H (conj s)
        (primitiveCharacterConjEquiv q χ) =
      conj (chen1973Lemma6MobiusPartialSum H s χ) := by
  unfold chen1973Lemma6MobiusPartialSum
  rw [map_sum]
  apply sum_congr rfl
  intro n hn
  change (((ArithmeticFunction.moebius n : ℤ) : ℂ) *
      conj (χ.1 (n : ZMod q)) / (n : ℂ) ^ conj s) = _
  have hnum :
      conj (((ArithmeticFunction.moebius n : ℤ) : ℂ) * χ.1 (n : ZMod q)) =
        ((ArithmeticFunction.moebius n : ℤ) : ℂ) * conj (χ.1 (n : ZMod q)) := by
    rw [map_mul]
    simp
  have hden : conj ((n : ℂ) ^ s) = (n : ℂ) ^ conj s := conj_cpow_nat s n
  rw [← hnum, ← hden]
  exact (map_div₀ conj
    (((ArithmeticFunction.moebius n : ℤ) : ℂ) * χ.1 (n : ZMod q))
    ((n : ℂ) ^ s)).symm

/-- The exact pair polynomial in equation (17), made public for the symmetry
and subsequent moment arguments. -/
def chen1973Lemma6Eq17PairPolynomial
    (x B k m : ℕ) {q : ℕ} (s : ℂ) (χ : PrimitiveCharacter q) : ℂ :=
  ∑ pp ∈ chen1973Lemma6PrimePairShell x B k m,
    χ.1 ((pp.1 * pp.2 : ℕ) : ZMod q) /
      ((pp.1 * pp.2 : ℂ) ^ s *
        Real.log ((x : ℝ) / ((pp.1 : ℝ) * pp.2)))

/-- Exact conjugation identity for the pair polynomial. -/
theorem chen1973Lemma6Eq17PairPolynomial_conj
    {q : ℕ} [NeZero q] (x B k m : ℕ) (s : ℂ)
    (χ : PrimitiveCharacter q) :
    chen1973Lemma6Eq17PairPolynomial x B k m (conj s)
        (primitiveCharacterConjEquiv q χ) =
      conj (chen1973Lemma6Eq17PairPolynomial x B k m s χ) := by
  unfold chen1973Lemma6Eq17PairPolynomial
  rw [map_sum]
  apply sum_congr rfl
  intro pp hpp
  change conj (χ.1 ((pp.1 * pp.2 : ℕ) : ZMod q)) /
      ((pp.1 * pp.2 : ℂ) ^ conj s *
        Real.log ((x : ℝ) / ((pp.1 : ℝ) * pp.2))) = _
  have hden :
      conj (((pp.1 * pp.2 : ℂ) ^ s) *
        Real.log ((x : ℝ) / ((pp.1 : ℝ) * pp.2))) =
        (pp.1 * pp.2 : ℂ) ^ conj s *
          Real.log ((x : ℝ) / ((pp.1 : ℝ) * pp.2)) := by
    rw [map_mul, Complex.conj_ofReal]
    congr 1
    simpa only [Nat.cast_mul] using conj_cpow_nat s (pp.1 * pp.2)
  rw [← hden]
  exact (map_div₀ conj (χ.1 ((pp.1 * pp.2 : ℕ) : ZMod q))
    (((pp.1 * pp.2 : ℂ) ^ s) *
      Real.log ((x : ℝ) / ((pp.1 : ℝ) * pp.2)))).symm

/-- The totalized primitive `L` value commutes with character and parameter
conjugation. -/
theorem chen1973Lemma6PrimitiveLValue_conj
    {q : ℕ} (s : ℂ) (χ : PrimitiveCharacter q) (hs : 0 < s.re) :
    chen1973Lemma6PrimitiveLValue q (conj s)
        (if hq : 1 < q then
          letI : NeZero q := ⟨Nat.ne_zero_of_lt hq⟩
          primitiveCharacterConjEquiv q χ
        else χ) =
      conj (chen1973Lemma6PrimitiveLValue q s χ) := by
  unfold chen1973Lemma6PrimitiveLValue
  split_ifs with hq
  · letI : NeZero q := ⟨Nat.ne_zero_of_lt hq⟩
    have hχ : χ.1 ≠ 1 := by
      intro h
      have hc := χ.2
      rw [DirichletCharacter.IsPrimitive, h, DirichletCharacter.conductor_one] at hc
      omega
    exact primitiveLFunction_conj χ hχ s hs
  · simp

/-- Exact conjugation identity for `1-LS` on the positive half-plane. -/
theorem chen1973Lemma6OneSubLS_conj
    {q : ℕ} [NeZero q] (H : ℕ) (s : ℂ) (χ : PrimitiveCharacter q)
    (hχ : χ.1 ≠ 1) (hs : 0 < s.re) :
    chen1973Lemma6OneSubLS H (conj s) (primitiveCharacterConjEquiv q χ) =
      conj (chen1973Lemma6OneSubLS H s χ) := by
  unfold chen1973Lemma6OneSubLS chen1973PrimitiveLValue
  change 1 - (if hq : 1 < q then
      (primitiveCharacterConjEquiv q χ).1.LFunction (conj s) else 0) *
        chen1973Lemma6MobiusPartialSum H (conj s) (primitiveCharacterConjEquiv q χ) =
    conj (1 - (if hq : 1 < q then χ.1.LFunction s else 0) *
      chen1973Lemma6MobiusPartialSum H s χ)
  split_ifs with hq
  · rw [primitiveLFunction_conj χ hχ s hs,
      chen1973Lemma6MobiusPartialSum_conj]
    simp
  · rw [chen1973Lemma6MobiusPartialSum_conj]
    simp

/-- Exact conjugation identity for `L' S`. -/
theorem chen1973Lemma6LDerivMulS_conj
    {q : ℕ} [NeZero q] (H : ℕ) (s : ℂ) (χ : PrimitiveCharacter q)
    (hχ : χ.1 ≠ 1) (hs : 0 < s.re) :
    deriv (primitiveCharacterConjEquiv q χ).1.LFunction (conj s) *
        chen1973Lemma6MobiusPartialSum H (conj s)
          (primitiveCharacterConjEquiv q χ) =
      conj (deriv χ.1.LFunction s *
        chen1973Lemma6MobiusPartialSum H s χ) := by
  rw [primitiveLDeriv_conj χ hχ s hs,
    chen1973Lemma6MobiusPartialSum_conj, map_mul]

/-- The exact totalized `L` object used in equation (17) has the expected
conjugation identity on the actual conductor range. -/
theorem chen1973Lemma6PrimitiveLValue_conj_of_one_lt
    {q : ℕ} [NeZero q] (hq : 1 < q) (s : ℂ) (χ : PrimitiveCharacter q)
    (hχ : χ.1 ≠ 1) (hs : 0 < s.re) :
    chen1973Lemma6PrimitiveLValue q (conj s) (primitiveCharacterConjEquiv q χ) =
      conj (chen1973Lemma6PrimitiveLValue q s χ) := by
  simp only [chen1973Lemma6PrimitiveLValue, dif_pos hq]
  exact primitiveLFunction_conj χ hχ s hs

/-- The exact totalized `L'` object used in equation (17) has the expected
conjugation identity on the actual conductor range. -/
theorem chen1973PrimitiveLDeriv_conj_of_one_lt
    {q : ℕ} [NeZero q] (hq : 1 < q) (s : ℂ) (χ : PrimitiveCharacter q)
    (hχ : χ.1 ≠ 1) (hs : 0 < s.re) :
    chen1973PrimitiveLDeriv q (conj s) (primitiveCharacterConjEquiv q χ) =
      conj (chen1973PrimitiveLDeriv q s χ) := by
  simp only [chen1973PrimitiveLDeriv, dif_pos hq]
  exact primitiveLDeriv_conj χ hχ s hs

private theorem norm_one_sub_conj_mul_conj (z w : ℂ) :
    ‖1 - conj z * conj w‖ = ‖1 - z * w‖ := by
  calc
    ‖1 - conj z * conj w‖ = ‖conj (1 - z * w)‖ := by simp
    _ = ‖1 - z * w‖ := Complex.norm_conj _

private theorem norm_conj_mul_conj (z w : ℂ) :
    ‖conj z * conj w‖ = ‖z * w‖ := by
  calc
    ‖conj z * conj w‖ = ‖conj (z * w)‖ := by rw [map_mul]
    _ = ‖z * w‖ := Complex.norm_conj _

/-- Conjugating the point `a+iv` on a real vertical line reflects `v`. -/
theorem conj_verticalLine (a v : ℝ) :
    conj ((a : ℂ) + (v : ℂ) * I) = (a : ℂ) + ((-v : ℝ) : ℂ) * I := by
  apply Complex.ext <;> simp

/-- Chen's real denominator kernel is invariant under reflection of a vertical
line. -/
theorem chen1973Lemma6Eq17Kernel_reflection
    (x : ℕ) (a v : ℝ) :
    chen1973Lemma6Eq17Kernel x (a + (-v) * I) =
      chen1973Lemma6Eq17Kernel x (a + v * I) := by
  have hn : ‖(a : ℂ) + -(v : ℂ) * I‖ =
      ‖(a : ℂ) + (v : ℂ) * I‖ := by
    simp [Complex.norm_def, Complex.normSq_apply]
  unfold chen1973Lemma6Eq17Kernel
  rw [hn]

/-- The first equation-(17) numerator is even on every positive real vertical
line.  Positive-level conductor blocks contain only nonprincipal primitive
characters, so the general conjugation equivalence applies to every summand. -/
theorem chen1973Lemma6A_reflection
    {x L level B k m H : ℕ} (hlevel : 1 ≤ level)
    (a v : ℝ) (ha : 0 < a) :
    chen1973Lemma6A x L level B k m H (a + (-v) * I) =
      chen1973Lemma6A x L level B k m H (a + v * I) := by
  classical
  unfold chen1973Lemma6A
  apply sum_congr rfl
  intro q hq
  have hq1 : 1 < q := by
    by_cases hl : level = 0
    · simp [chen1973Lemma6ConductorBlock, hl] at hq
      omega
    · simp [chen1973Lemma6ConductorBlock, hl, chen1973Lemma6DyadicShell] at hq
      omega
  letI : NeZero q := ⟨Nat.ne_zero_of_lt hq1⟩
  congr 1
  rw [← (primitiveCharacterConjEquiv q).sum_comp]
  apply sum_congr rfl
  intro χ hχmem
  have hχ : χ.1 ≠ 1 := by
    intro heq
    have hp := χ.2
    rw [DirichletCharacter.IsPrimitive, heq, DirichletCharacter.conductor_one] at hp
    omega
  have hsre : 0 < ((a : ℂ) + (v : ℂ) * I).re := by simpa using ha
  rw [show ((a : ℂ) + -(v : ℂ) * I) =
      conj ((a : ℂ) + (v : ℂ) * I) by apply Complex.ext <;> simp]
  change ‖chen1973Lemma6Eq17PairPolynomial x B k m
      (conj ((a : ℂ) + (v : ℂ) * I)) (primitiveCharacterConjEquiv q χ)‖ *
    ‖1 - chen1973Lemma6PrimitiveLValue q (conj ((a : ℂ) + (v : ℂ) * I))
        (primitiveCharacterConjEquiv q χ) *
      chen1973Lemma6MobiusPartialSum H (conj ((a : ℂ) + (v : ℂ) * I))
        (primitiveCharacterConjEquiv q χ)‖ = _
  rw [chen1973Lemma6Eq17PairPolynomial_conj,
    chen1973Lemma6PrimitiveLValue_conj_of_one_lt hq1 _ χ hχ hsre,
    chen1973Lemma6MobiusPartialSum_conj]
  simp only [← map_mul, Complex.norm_conj]
  rw [map_mul, norm_one_sub_conj_mul_conj]
  rfl

/-- The second equation-(17) numerator is even on every positive real vertical
line. -/
theorem chen1973Lemma6B_reflection
    {x L level B k m H : ℕ} (hlevel : 1 ≤ level)
    (a v : ℝ) (ha : 0 < a) :
    chen1973Lemma6B x L level B k m H (a + (-v) * I) =
      chen1973Lemma6B x L level B k m H (a + v * I) := by
  classical
  unfold chen1973Lemma6B chen1973PrimitiveLDeriv
  apply sum_congr rfl
  intro q hq
  have hq1 : 1 < q := by
    by_cases hl : level = 0
    · simp [chen1973Lemma6ConductorBlock, hl] at hq
      omega
    · simp [chen1973Lemma6ConductorBlock, hl, chen1973Lemma6DyadicShell] at hq
      omega
  letI : NeZero q := ⟨Nat.ne_zero_of_lt hq1⟩
  congr 1
  rw [← (primitiveCharacterConjEquiv q).sum_comp]
  apply sum_congr rfl
  intro χ hχmem
  have hχ : χ.1 ≠ 1 := by
    intro heq
    have hp := χ.2
    rw [DirichletCharacter.IsPrimitive, heq, DirichletCharacter.conductor_one] at hp
    omega
  have hsre : 0 < ((a : ℂ) + (v : ℂ) * I).re := by simpa using ha
  rw [show ((a : ℂ) + -(v : ℂ) * I) =
      conj ((a : ℂ) + (v : ℂ) * I) by apply Complex.ext <;> simp]
  split_ifs with hq'
  · change ‖chen1973Lemma6Eq17PairPolynomial x B k m
        (conj ((a : ℂ) + (v : ℂ) * I)) (primitiveCharacterConjEquiv q χ)‖ *
      ‖deriv (primitiveCharacterConjEquiv q χ).1.LFunction
          (conj ((a : ℂ) + (v : ℂ) * I)) *
        chen1973Lemma6MobiusPartialSum H (conj ((a : ℂ) + (v : ℂ) * I))
          (primitiveCharacterConjEquiv q χ)‖ = _
    rw [chen1973Lemma6Eq17PairPolynomial_conj,
      primitiveLDeriv_conj χ hχ _ hsre,
      chen1973Lemma6MobiusPartialSum_conj]
    simp only [chen1973Lemma6Eq17PairPolynomial, map_mul, Complex.norm_conj]
    congr 1
    exact norm_conj_mul_conj _ _

/-- The actual first norm integrand in (17) is even. -/
theorem chen1973Lemma6Eq17FirstIntegrand_even
    {x L level B k m H : ℕ} (hlevel : 1 ≤ level)
    (hx : 1 < x) (v : ℝ) :
    chen1973Lemma6A x L level B k m H
        (chen1973Lemma6Alpha x + (-v) * I) /
        chen1973Lemma6Eq17Kernel x
          (chen1973Lemma6Alpha x + (-v) * I) =
      chen1973Lemma6A x L level B k m H
        (chen1973Lemma6Alpha x + v * I) /
        chen1973Lemma6Eq17Kernel x
          (chen1973Lemma6Alpha x + v * I) := by
  rw [chen1973Lemma6A_reflection hlevel]
  · rw [chen1973Lemma6Eq17Kernel_reflection]
  · unfold chen1973Lemma6Alpha
    have : 0 < Real.log x := Real.log_pos (by exact_mod_cast hx)
    positivity

/-- The actual second norm integrand in (17) is even. -/
theorem chen1973Lemma6Eq17SecondIntegrand_even
    {x L level B k m H : ℕ} (hlevel : 1 ≤ level)
    (hx : 1 < x) (v : ℝ) :
    chen1973Lemma6B x L level B k m H
        (chen1973Lemma6Beta x + (-v) * I) /
        chen1973Lemma6Eq17Kernel x
          (chen1973Lemma6Beta x + (-v) * I) =
      chen1973Lemma6B x L level B k m H
        (chen1973Lemma6Beta x + v * I) /
        chen1973Lemma6Eq17Kernel x
          (chen1973Lemma6Beta x + v * I) := by
  rw [chen1973Lemma6B_reflection hlevel]
  · rw [chen1973Lemma6Eq17Kernel_reflection]
  · unfold chen1973Lemma6Beta
    have : 0 < Real.log x := Real.log_pos (by exact_mod_cast hx)
    positivity

/-- Full-line version of the first actual equation-(17) integral. -/
def chen1973Lemma6Eq17FirstFullIntegral
    (x L level B k m H : ℕ) : ℝ :=
  ∫ v : ℝ,
    chen1973Lemma6A x L level B k m H (chen1973Lemma6Alpha x + v * I) /
      chen1973Lemma6Eq17Kernel x (chen1973Lemma6Alpha x + v * I)

/-- Full-line version of the second actual equation-(17) integral. -/
def chen1973Lemma6Eq17SecondFullIntegral
    (x L level B k m H : ℕ) : ℝ :=
  ∫ v : ℝ,
    chen1973Lemma6B x L level B k m H (chen1973Lemma6Beta x + v * I) /
      chen1973Lemma6Eq17Kernel x (chen1973Lemma6Beta x + v * I)

private theorem integral_eq_two_mul_Ioi_of_even (f : ℝ → ℝ)
    (heven : ∀ v, f (-v) = f v) :
    (∫ v : ℝ, f v) = 2 * ∫ v in Ioi (0 : ℝ), f v := by
  have habs : (fun v : ℝ => f v) = fun v => f |v| := by
    funext v
    rcases le_total 0 v with hv | hv
    · rw [abs_of_nonneg hv]
    · rw [abs_of_nonpos hv, heven]
  calc
    (∫ v : ℝ, f v) = ∫ v : ℝ, f |v| := by rw [habs]
    _ = 2 * ∫ v in Ioi (0 : ℝ), f v := integral_comp_abs

set_option maxHeartbeats 800000 in
/-- The full alpha-line norm integral is exactly twice Chen's half-line
integral. -/
theorem chen1973Lemma6Eq17FirstFullIntegral_eq_two_mul_half
    {x L level B k m H : ℕ} (hlevel : 1 ≤ level) (hx : 1 < x) :
    chen1973Lemma6Eq17FirstFullIntegral x L level B k m H =
      2 * chen1973Lemma6Eq17FirstIntegral x L level B k m H := by
  unfold chen1973Lemma6Eq17FirstFullIntegral chen1973Lemma6Eq17FirstIntegral
  apply integral_eq_two_mul_Ioi_of_even
  intro v
  rw [ofReal_neg]
  exact chen1973Lemma6Eq17FirstIntegrand_even
    (x := x) (L := L) (level := level) (B := B) (k := k) (m := m) (H := H)
    hlevel hx v

set_option maxHeartbeats 800000 in
/-- The full beta-line norm integral is exactly twice Chen's half-line
integral. -/
theorem chen1973Lemma6Eq17SecondFullIntegral_eq_two_mul_half
    {x L level B k m H : ℕ} (hlevel : 1 ≤ level) (hx : 1 < x) :
    chen1973Lemma6Eq17SecondFullIntegral x L level B k m H =
      2 * chen1973Lemma6Eq17SecondIntegral x L level B k m H := by
  unfold chen1973Lemma6Eq17SecondFullIntegral chen1973Lemma6Eq17SecondIntegral
  apply integral_eq_two_mul_Ioi_of_even
  intro v
  rw [ofReal_neg]
  exact chen1973Lemma6Eq17SecondIntegrand_even
    (x := x) (L := L) (level := level) (B := B) (k := k) (m := m) (H := H)
    hlevel hx v

end AnalyticNumberTheory.LargeSieve