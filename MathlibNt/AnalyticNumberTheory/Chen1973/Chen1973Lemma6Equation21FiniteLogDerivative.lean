import MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLZeroFreeFiniteRectangleLogDerivative
import MathlibNt.AnalyticNumberTheory.Chen1973.Chen1973Lemma6Equation21

open Complex Metric Set
open AnalyticNumberTheory.LargeSieve

namespace Eq21FiniteLogDerivative
noncomputable section

/-- The finite bound for the literal totalized primitive value/derivative pair. -/
theorem norm_primitive_logDeriv_le_of_zeroFree_rectangle
    {q : ℕ} (hq : 1 < q) (χ : PrimitiveCharacter q)
    {δ T : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 4) (hT : 0 ≤ T)
    (hzero : ∀ z : ℂ, 1 - δ ≤ z.re → z.re ≤ 2 → |z.im| ≤ T + 1 →
      chen1973Lemma6PrimitiveLValue q z χ ≠ 0)
    (s : ℂ) (ht : |s.im| ≤ T) (hslo : 1 - δ / 2 ≤ s.re)
    (hshi : s.re ≤ 1 + δ) :
    ‖chen1973PrimitiveLDeriv q s χ / chen1973Lemma6PrimitiveLValue q s χ‖ ≤
      40 / δ * Real.log (32 * q * (1 + |s.im|) / δ) := by
  let : NeZero q := ⟨Nat.ne_zero_of_lt hq⟩
  have hχ : χ.1 ≠ 1 := by
    intro h
    have hp := χ.2
    rw [DirichletCharacter.IsPrimitive, h, DirichletCharacter.conductor_one] at hp
    omega
  have hz : ∀ z : ℂ, 1 - δ ≤ z.re → z.re ≤ 2 → |z.im| ≤ T + 1 →
      χ.1.LFunction z ≠ 0 := by
    intro z hlo hhi him
    simpa only [chen1973Lemma6PrimitiveLValue, dif_pos hq] using hzero z hlo hhi him
  have h := norm_logDeriv_LFunction_le_of_zeroFree_rectangle χ.1 hχ
    hδ hδ1 hT hz s.im s.re ht hslo hshi
  have heq : (s.re : ℂ) + I * s.im = s := by
    simpa only [mul_comm I] using Complex.re_add_im s
  simpa only [heq, logDeriv_apply, chen1973PrimitiveLDeriv,
    chen1973Lemma6PrimitiveLValue, dif_pos hq] using h

/-- W4 with a real parameter `u`, width `2/sqrt u` and finite height `u²`. -/
theorem norm_primitive_logDeriv_le_sqrt_budget
    {q : ℕ} (hq : 1 < q) (χ : PrimitiveCharacter q)
    {u : ℝ} (hu64 : 64 ≤ u)
    (hzero : ∀ z : ℂ, 1 - 2 / Real.sqrt u ≤ z.re → z.re ≤ 2 →
      |z.im| ≤ u ^ 2 + 1 → chen1973Lemma6PrimitiveLValue q z χ ≠ 0)
    (s : ℂ) (hslo : 1 - 1 / Real.sqrt u ≤ s.re) (hshi : s.re ≤ 1 + 1 / u)
    (ht : |s.im| ≤ u ^ 2) :
    ‖chen1973PrimitiveLDeriv q s χ / chen1973Lemma6PrimitiveLValue q s χ‖ ≤
      20 * Real.sqrt u * Real.log (16 * q * (1 + u ^ 2) * Real.sqrt u) := by
  have hu : 0 < u := by linarith
  have hr : 0 < Real.sqrt u := Real.sqrt_pos.2 hu
  have hrsq := Real.sq_sqrt hu.le
  have hr8 : 8 ≤ Real.sqrt u := by nlinarith [Real.sqrt_nonneg u]
  have hδ : 0 < 2 / Real.sqrt u := by positivity
  have hδ1 : 2 / Real.sqrt u ≤ 1 / 4 := by
    apply (div_le_iff₀ hr).2
    linarith
  have hα : 1 / u ≤ 2 / Real.sqrt u := by
    apply (div_le_div_iff₀ hu hr).2
    nlinarith
  have hlo : 1 - (2 / Real.sqrt u) / 2 ≤ s.re := by
    convert hslo using 1; ring
  have h := norm_primitive_logDeriv_le_of_zeroFree_rectangle hq χ hδ hδ1
    (sq_nonneg u) hzero s ht hlo (by linarith)
  have hfactor : 40 / (2 / Real.sqrt u) = 20 * Real.sqrt u := by field_simp; ring
  have harg : 32 * (q : ℝ) * (1 + |s.im|) / (2 / Real.sqrt u) =
      16 * q * (1 + |s.im|) * Real.sqrt u := by field_simp; ring
  rw [hfactor, harg] at h
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.log_le_log (by positivity)
  gcongr

/-- W4 at the actual Chen source parameters and the actual primitive quotient.
The nonvanishing hypothesis is explicitly finite and has no shared input record. -/
theorem chen1973Lemma6_eq21_logDeriv_on_finiteRectangle_of_zeroFree
    {x q : ℕ} (hq : 1 < q) (χ : PrimitiveCharacter q)
    (hu64 : 64 ≤ Real.log (x : ℝ))
    (hzero : ∀ z : ℂ, 1 - 2 / Real.sqrt (Real.log (x : ℝ)) ≤ z.re → z.re ≤ 2 →
      |z.im| ≤ (Real.log (x : ℝ)) ^ 2 + 1 →
      chen1973Lemma6PrimitiveLValue q z χ ≠ 0)
    (s : ℂ) (hslo : chen1973Lemma6Eq21Sigma x ≤ s.re)
    (hshi : s.re ≤ chen1973Lemma6Alpha x)
    (ht : |s.im| ≤ (Real.log (x : ℝ)) ^ 2) :
    ‖chen1973PrimitiveLDeriv q s χ / chen1973Lemma6PrimitiveLValue q s χ‖ ≤
      20 * Real.sqrt (Real.log (x : ℝ)) *
        Real.log (16 * q * (1 + (Real.log (x : ℝ)) ^ 2) * Real.sqrt (Real.log (x : ℝ))) :=
  norm_primitive_logDeriv_le_sqrt_budget hq χ hu64 hzero s hslo hshi ht

/-- Uniform conductor payment; this is a scalar consequence, not a new
analytic hypothesis. -/
theorem sqrt_budget_le_uniform {q : ℕ} (hq : 1 < q)
    {u : ℝ} (hu : 1 ≤ u) (hqu : (q : ℝ) ≤ u ^ (100 : ℕ)) :
    20 * Real.sqrt u * Real.log (16 * q * (1 + u ^ 2) * Real.sqrt u) ≤
      20 * Real.sqrt u * (Real.log 32 + (205 / 2 : ℝ) * Real.log u) := by
  have hu0 : 0 < u := by linarith
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (Nat.zero_lt_of_lt hq)
  have hr : 0 < Real.sqrt u := Real.sqrt_pos.2 hu0
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc
    Real.log (16 * q * (1 + u ^ 2) * Real.sqrt u) ≤
        Real.log (32 * u ^ (102 : ℕ) * Real.sqrt u) := by
      apply Real.log_le_log (by positivity)
      calc
        _ ≤ 16 * u ^ (100 : ℕ) * (2 * u ^ 2) * Real.sqrt u := by
          gcongr
          nlinarith [sq_nonneg (u - 1)]
        _ = _ := by ring
    _ = Real.log 32 + (205 / 2 : ℝ) * Real.log u := by
      rw [Real.log_mul (by positivity) hr.ne',
        Real.log_mul (by norm_num) (by positivity), Real.log_pow, Real.log_sqrt hu0.le]
      norm_num
      ring

/-- The finite-rectangle actual primitive bound, uniform for `q ≤ u^100`. -/
theorem norm_primitive_logDeriv_le_uniform
    {q : ℕ} (hq : 1 < q) (χ : PrimitiveCharacter q)
    {u : ℝ} (hu64 : 64 ≤ u) (hqu : (q : ℝ) ≤ u ^ (100 : ℕ))
    (hzero : ∀ z : ℂ, 1 - 2 / Real.sqrt u ≤ z.re → z.re ≤ 2 →
      |z.im| ≤ u ^ 2 + 1 → chen1973Lemma6PrimitiveLValue q z χ ≠ 0)
    (s : ℂ) (hslo : 1 - 1 / Real.sqrt u ≤ s.re) (hshi : s.re ≤ 1 + 1 / u)
    (ht : |s.im| ≤ u ^ 2) :
    ‖chen1973PrimitiveLDeriv q s χ / chen1973Lemma6PrimitiveLValue q s χ‖ ≤
      20 * Real.sqrt u * (Real.log 32 + (205 / 2 : ℝ) * Real.log u) :=
  (norm_primitive_logDeriv_le_sqrt_budget hq χ hu64 hzero s hslo hshi ht).trans
    (sqrt_budget_le_uniform hq (by linarith) hqu)

end
end Eq21FiniteLogDerivative
