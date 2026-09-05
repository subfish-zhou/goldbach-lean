/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nous Research
-/
import MathlibNt.AnalyticNumberTheory.Chen1973.Chen1973Lemma6Equation12
import MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLFoundation

/-!
# Chen 1973, Lemma 6, equations (16) and (17)

This module records the two displayed formulae on pp. 120--121 with the actual
finite `S(H,s,χ)` and the actual switched `Φ` from equation (12).  In
particular, there is no free function named `Phi`.

The second prefactor in (17) is the printed `x^(1/2)` (p.121).
-/

noncomputable section

open Classical Complex Finset MeasureTheory Set
open scoped BigOperators ArithmeticFunction

namespace AnalyticNumberTheory.LargeSieve

/-- Chen's two vertical lines in (17). -/
def chen1973Lemma6Alpha (x : ℕ) : ℝ := 1 + 1 / Real.log x
def chen1973Lemma6Beta (x : ℕ) : ℝ := 1 / 2 + 1 / Real.log x

/-- Totalized `L(s,χ)` on the primitive range. -/
def chen1973Lemma6PrimitiveLValue (q : ℕ) (s : ℂ)
    (χ : PrimitiveCharacter q) : ℂ :=
  if hq : 1 < q then
    letI : NeZero q := ⟨Nat.ne_zero_of_lt hq⟩
    χ.1.LFunction s
  else 0

/-- The totalized derivative used in the finite starred-character sums. -/
def chen1973PrimitiveLDeriv (q : ℕ) (s : ℂ)
    (χ : PrimitiveCharacter q) : ℂ :=
  if hq : 1 < q then
    letI : NeZero q := ⟨Nat.ne_zero_of_lt hq⟩
    deriv χ.1.LFunction s
  else 0

/-- Termwise actual-`Φ` interface to the already closed Mellin--Bromwich
identity.  The finite sum is left finite here; hence no conditional `tsum`
reordering is involved.  This is the exact analytic kernel consumed before
(16). -/
theorem chen1973Lemma6ActualPhi_termwise_bromwich
    {x d n : ℕ} {pp : ℕ × ℕ} (χ : PrimitiveCharacter d)
    (hx : 1 < x) (hn : 0 < n) (hp₁ : 0 < pp.1) (hp₂ : 0 < pp.2) :
    (((ArithmeticFunction.vonMangoldt n : ℝ) *
        chen1973PerronKernelFinite (x : ℝ)
          ((x : ℝ) / ((pp.1 : ℝ) * pp.2 * n)) : ℂ) * χ.1 (n : ZMod d)) =
      ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
        (((1 / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ t : ℝ, chen1973BromwichIntegrand (x : ℝ)
            ((x : ℝ) / ((pp.1 : ℝ) * pp.2 * n)) t) *
        χ.1 (n : ZMod d) := by
  have hy : 0 < (x : ℝ) / ((pp.1 : ℝ) * pp.2 * n) := by
    positivity
  have hB := Chen1973BromwichIdentity (x : ℝ) (by exact_mod_cast hx)
    ((x : ℝ) / ((pp.1 : ℝ) * pp.2 * n)) hy
  rw [hB]

/-- The exact algebraic decomposition (16).  The only analytic fact needed is
the pointwise nonvanishing required to divide by `L`. -/
theorem chen1973Lemma6_equation16
    {d H : ℕ} [NeZero d] (χ : PrimitiveCharacter d) (s : ℂ)
    (hL : χ.1.LFunction s ≠ 0) :
    deriv χ.1.LFunction s / χ.1.LFunction s =
      (deriv χ.1.LFunction s / χ.1.LFunction s) *
          (1 - χ.1.LFunction s * chen1973Lemma6MobiusPartialSum H s χ) +
        deriv χ.1.LFunction s * chen1973Lemma6MobiusPartialSum H s χ := by
  field_simp [hL]
  ring

/-- On the printed right line, (16) needs no additional zero-free hypothesis:
nonprincipal Dirichlet `L`-functions do not vanish for `Re s ≥ 1`. -/
theorem chen1973Lemma6_equation16_on_alpha
    {d H : ℕ} [NeZero d] (χ : PrimitiveCharacter d) (hχ : χ.1 ≠ 1)
    (x : ℕ) (hx : 1 < x) (v : ℝ) :
    deriv χ.1.LFunction (chen1973Lemma6Alpha x + v * I) /
        χ.1.LFunction (chen1973Lemma6Alpha x + v * I) =
      (deriv χ.1.LFunction (chen1973Lemma6Alpha x + v * I) /
          χ.1.LFunction (chen1973Lemma6Alpha x + v * I)) *
        (1 - χ.1.LFunction (chen1973Lemma6Alpha x + v * I) *
          chen1973Lemma6MobiusPartialSum H
            (chen1973Lemma6Alpha x + v * I) χ) +
      deriv χ.1.LFunction (chen1973Lemma6Alpha x + v * I) *
        chen1973Lemma6MobiusPartialSum H
          (chen1973Lemma6Alpha x + v * I) χ := by
  apply chen1973Lemma6_equation16
  apply χ.1.LFunction_ne_zero_of_one_le_re (Or.inl hχ)
  simp only [chen1973Lemma6Alpha, add_re, ofReal_re, mul_re, ofReal_im,
    I_re, I_im, mul_zero, zero_mul, sub_zero]
  have hlog : 0 < Real.log x := Real.log_pos (by exact_mod_cast hx)
  simpa using (le_add_of_nonneg_right (le_of_lt (one_div_pos.mpr hlog)) :
    (1 : ℝ) ≤ 1 + 1 / Real.log x)

/-- The literal high-power radial denominator printed in (17).  Its scale is
`(log x)^(11/10)` and its exponent is `[log x] + 1`; in particular it has no
conductor-level dependence. -/
def chen1973Lemma6Eq17Kernel (x : ℕ) (s : ℂ) : ℝ :=
  ‖s‖ * (1 + ‖s‖ / chen1973PerronScale (x : ℝ)) ^
    (chen1973PerronOrder (x : ℝ) + 1)

/-- The actual `A(l,k,s,m,H)` of p. 121. The source has already paid the
alpha-line logarithmic derivative pointwise into the exterior `(log x)^2`
prefactor, so `A` contains only the pair polynomial and `1-LS`. -/
def chen1973Lemma6A (x L level B k m H : ℕ) (s : ℂ) : ℝ :=
  ∑ d ∈ chen1973Lemma6ConductorBlock x L level,
    |((ArithmeticFunction.moebius d : ℤ) : ℝ)| *
      (3 : ℝ) ^ d.primeFactors.card / d *
      ∑ χ : PrimitiveCharacter d,
        ‖∑ pp ∈ chen1973Lemma6PrimePairShell x B k m,
          χ.1 ((pp.1 * pp.2 : ℕ) : ZMod d) /
            ((pp.1 * pp.2 : ℂ) ^ s *
              Real.log ((x : ℝ) / ((pp.1 : ℝ) * pp.2)))‖ *
        ‖1 - chen1973Lemma6PrimitiveLValue d s χ *
          chen1973Lemma6MobiusPartialSum H s χ‖

/-- The actual `B(l,k,s,m,H)` of p. 121. -/
def chen1973Lemma6B (x L level B k m H : ℕ) (s : ℂ) : ℝ :=
  ∑ d ∈ chen1973Lemma6ConductorBlock x L level,
    |((ArithmeticFunction.moebius d : ℤ) : ℝ)| *
      (3 : ℝ) ^ d.primeFactors.card / d *
      ∑ χ : PrimitiveCharacter d,
        ‖∑ pp ∈ chen1973Lemma6PrimePairShell x B k m,
          χ.1 ((pp.1 * pp.2 : ℕ) : ZMod d) /
            ((pp.1 * pp.2 : ℂ) ^ s *
              Real.log ((x : ℝ) / ((pp.1 : ℝ) * pp.2)))‖ *
        ‖chen1973PrimitiveLDeriv d s χ * chen1973Lemma6MobiusPartialSum H s χ‖

/-- First actual vertical-line integral in (17), on `Re s = α`. -/
def chen1973Lemma6Eq17FirstIntegral
    (x L level B k m H : ℕ) : ℝ :=
  ∫ v in Ioi (0 : ℝ),
    chen1973Lemma6A x L level B k m H (chen1973Lemma6Alpha x + v * I) /
      chen1973Lemma6Eq17Kernel x (chen1973Lemma6Alpha x + v * I)

/-- Second actual vertical-line integral in (17), on `Re s = β`. -/
def chen1973Lemma6Eq17SecondIntegral
    (x L level B k m H : ℕ) : ℝ :=
  ∫ v in Ioi (0 : ℝ),
    chen1973Lemma6B x L level B k m H (chen1973Lemma6Beta x + v * I) /
      chen1973Lemma6Eq17Kernel x (chen1973Lemma6Beta x + v * I)

/-- The literal right side of (17), with the original beta prefactor `x^(1/2)`. -/
def chen1973Lemma6Equation17RHS
    (x L level B k m H : ℕ) : ℝ :=
  2 * x * (Real.log x) ^ 2 *
      chen1973Lemma6Eq17FirstIntegral x L level B k m H +
    2 * (x : ℝ) ^ ((1 : ℝ) / 2) *
      chen1973Lemma6Eq17SecondIntegral x L level B k m H

/-- The actual equation-(17) left side, with the pair-dependent `Φ` from
equation (12) inserted directly (rather than passed as a free parameter). -/
def chen1973Lemma6NmBlockActual (x L level B k m : ℕ) : ℝ :=
  ∑ d ∈ chen1973Lemma6ConductorBlock x L level,
    |((ArithmeticFunction.moebius d : ℤ) : ℝ)| * (3 : ℝ) ^ d.primeFactors.card / d *
      ‖∑ χ : PrimitiveCharacter d,
        star (χ.1 (x : ZMod d)) *
          ∑ pp ∈ chen1973Lemma6PrimePairShell x B k m,
            (Real.log ((x : ℝ) / ((pp.1 : ℝ) * pp.2)))⁻¹ *
              chen1973Lemma6ActualPhi x d χ pp *
                χ.1 ((pp.1 * pp.2 : ℕ) : ZMod d)‖

/-- Compatibility boundary for the still-unformalized contour deformation in
(17).  This is not a beta-line zero-free hypothesis: on the source range
`level ≥ 1`, every conductor is greater than one, hence the primitive
character is nonprincipal and `L'·S` continues entire to the beta line.  The
remaining work is the quantitative deformation from the unconditional
Bromwich line, including the whole-line to half-line symmetry and Bochner
integrability/Fubini argument. -/
def Chen1973Equation17ContourMajorization
    (x L level B k m H : ℕ) : Prop :=
  chen1973Lemma6NmBlockActual x L level B k m ≤
    chen1973Lemma6Equation17RHS x L level B k m H

/-- Compatibility consumer for a supplied contour majorization.  The
premise-free publication theorem is proved in the equation-(17) assembly
module. -/
theorem chen1973Lemma6_equation17_of_contourMajorization
    {x L level B k m H : ℕ}
    (h17 : Chen1973Equation17ContourMajorization x L level B k m H) :
    chen1973Lemma6NmBlockActual x L level B k m ≤
      2 * x * (Real.log x) ^ 2 *
          chen1973Lemma6Eq17FirstIntegral x L level B k m H +
        2 * (x : ℝ) ^ ((1 : ℝ) / 2) *
          chen1973Lemma6Eq17SecondIntegral x L level B k m H := h17

end AnalyticNumberTheory.LargeSieve