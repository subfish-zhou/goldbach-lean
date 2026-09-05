/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nous Research
-/
import MathlibNt.AnalyticNumberTheory.Chen1973.Chen1973Lemma6Equations16And17
import Mathlib.Tactic

/-!
# Chen 1973, Lemma 6, equation (21): the level-zero source node

Source ledger: `references/chen-1973/chen-1973-original-scan.pdf`, printed
p. 123 (PDF page 13), SHA-256
`965413185962830608bcdfe8172584b9d593f87a3dedd53d1efca91c949301fd`.
Equation (21) treats `N_m^(0,k)`, uniformly for `0 ≤ k ≤ l₂`.  Immediately before it Chen invokes,
for primitive `χ_d`, the zero-free assertion
`Re s ≥ 1 - c / d^(1/300) → L(s,χ_d) ≠ 0` (with one constant `c`).  No
exceptional-character qualifier is printed there.  The displayed contour is
`Re ω = 1 - 1 / (log x)^(1/2)`, its smoothing scale is `(log x)^(11/10)`, and
its order is `[log x] + 1`.  The displayed conductor range is
`1 < d ≪ (log x)^100`; the next line pays `(log x)^200` and sums over
`x^(1/10) < p₁ ≤ x^(1/3) < p₂ ≤ (x/p₁)^(1/2)`, finally obtaining
`x / (log x)^20` up to an absolute constant.

The exponent `1/300` and prime range were rechecked visually on 2026-09-05;
the earlier readings `3/100` and `1/6` were transcription errors, not source
defects. For `d ≤ (log x)^100`, the width comparison is eventually payable.
The full-height zero-free assertion itself remains an analytic input.
It defines the literal finite source objects, proves the level-zero carrier and
the algebraic assembly, and leaves only the three named analytic inequalities
actually used in the displayed `≪` chain.  In particular, none of those inputs
has the terminal equation-(21) conclusion as its statement.
-/

noncomputable section

open Classical Complex Finset MeasureTheory Set
open scoped BigOperators ArithmeticFunction

namespace AnalyticNumberTheory.LargeSieve

/-- The real part of the vertical line printed in equation (21). -/
def chen1973Lemma6Eq21Sigma (x : ℕ) : ℝ :=
  1 - 1 / Real.sqrt (Real.log x)

/-- A point on the equation-(21) vertical line. -/
def chen1973Lemma6Eq21Line (x : ℕ) (t : ℝ) : ℂ :=
  chen1973Lemma6Eq21Sigma x + t * I

/-- The global prime-pair region printed on the second line of (21). -/
def chen1973Lemma6Eq21PrimeRegion (x : ℕ) : Finset (ℕ × ℕ) :=
  (chen1973Lemma5PrimePairs x).filter fun pp =>
    (x : ℝ) ^ ((1 : ℝ) / 10) < pp.1 ∧
    (pp.1 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 3) ∧
    (x : ℝ) ^ ((1 : ℝ) / 3) < pp.2 ∧
    (pp.2 : ℝ) ≤ Real.sqrt ((x : ℝ) / pp.1)

/-- The positive finite sum on the second line of equation (21). -/
def chen1973Lemma6Eq21PrimeSum (x : ℕ) : ℝ :=
  ∑ pp ∈ chen1973Lemma6Eq21PrimeRegion x,
    ((x : ℝ) / ((pp.1 : ℝ) * pp.2)) ^ chen1973Lemma6Eq21Sigma x

/-- The literal vertical integral occurring termwise in the first two lines of
(21).  `chen1973MellinKernel` is exactly
`(1 + ω/(log x)^(11/10))^(-[log x]-1) / ω`.  Totalized `L` objects make the
definition meaningful before the proof establishes `1 < d`. -/
def chen1973Lemma6Eq21VerticalIntegral
    (x d : ℕ) (χ : PrimitiveCharacter d) (pp : ℕ × ℕ) : ℂ :=
  ((1 / (2 * Real.pi) : ℝ) : ℂ) *
    ∫ t : ℝ,
      χ.1 ((pp.1 * pp.2 : ℕ) : ZMod d) *
        (((x : ℝ) / ((pp.1 : ℝ) * pp.2) : ℂ) ^ chen1973Lemma6Eq21Line x t) *
        chen1973MellinKernel (x : ℝ) (chen1973Lemma6Eq21Line x t) *
        (chen1973PrimitiveLDeriv d (chen1973Lemma6Eq21Line x t) χ /
          chen1973Lemma6PrimitiveLValue d (chen1973Lemma6Eq21Line x t) χ)

/-- The finite weighted contour majorant displayed on the first two lines of
(21), using the actual level-zero conductor carrier and actual `(k,m)` shell. -/
def chen1973Lemma6Eq21ContourMajorant
    (x L B k m : ℕ) : ℝ :=
  ∑ d ∈ chen1973Lemma6ConductorBlock x L 0,
    |((ArithmeticFunction.moebius d : ℤ) : ℝ)| *
      (3 : ℝ) ^ d.primeFactors.card / d *
      ∑ χ : PrimitiveCharacter d,
        ‖∑ pp ∈ chen1973Lemma6PrimePairShell x B k m,
          (Real.log ((x : ℝ) / ((pp.1 : ℝ) * pp.2)))⁻¹ *
            chen1973Lemma6Eq21VerticalIntegral x d χ pp‖

/-- Literal parameter packet for the equation-(21) lane.  Constants hidden by
source `≪` are intentionally not fields: in the assembly theorem they are
quantified once, before every cell parameter. -/
structure Chen1973Lemma6Eq21SourceParameters
    (x L B k m l₂ : ℕ) : Prop where
  hx : 3 ≤ x
  hL : 0 < L
  hB : 0 < B
  hk : k ≤ l₂
  hlog_one : 1 ≤ Real.log x
  hL_lower : (L : ℝ) ≤ Real.log x ^ (100 : ℕ)
  hL_upper : Real.log x ^ (100 : ℕ) < L + 1
  hB_lower : (B : ℝ) ≤ (x : ℝ) ^ ((13 : ℝ) / 30)
  hB_upper : (x : ℝ) ^ ((13 : ℝ) / 30) < B + 1

/-- The zero-free assertion printed immediately before equation (21).  There is
no exceptional-character deletion in the source sentence. -/
def Chen1973Lemma6Eq21ZeroFreeInput (x L : ℕ) (c : ℝ) : Prop :=
  0 < c ∧
    ∀ d ∈ chen1973Lemma6ConductorBlock x L 0,
      ∀ χ : PrimitiveCharacter d, ∀ s : ℂ,
        1 - c / (d : ℝ) ^ ((1 : ℝ) / 300) ≤ s.re →
          chen1973Lemma6PrimitiveLValue d s χ ≠ 0

lemma chen1973Lemma6_eq21_conductorBlock_eq
    (x L : ℕ) :
    chen1973Lemma6ConductorBlock x L 0 =
      (Finset.Ioc 1 L).filter (fun d => Nat.Coprime d x ∧ Squarefree d) := by
  simp [chen1973Lemma6ConductorBlock]

lemma chen1973Lemma6_eq21_one_lt_conductor
    {x L d : ℕ} (hd : d ∈ chen1973Lemma6ConductorBlock x L 0) :
    1 < d := by
  rw [chen1973Lemma6_eq21_conductorBlock_eq] at hd
  exact (Finset.mem_Ioc.mp (Finset.mem_filter.mp hd).1).1

lemma chen1973Lemma6_eq21_conductor_le
    {x L d : ℕ} (hd : d ∈ chen1973Lemma6ConductorBlock x L 0) :
    d ≤ L := by
  rw [chen1973Lemma6_eq21_conductorBlock_eq] at hd
  exact (Finset.mem_Ioc.mp (Finset.mem_filter.mp hd).1).2

@[simp] lemma chen1973Lemma6_eq21_line_re (x : ℕ) (t : ℝ) :
    (chen1973Lemma6Eq21Line x t).re = chen1973Lemma6Eq21Sigma x := by
  simp [chen1973Lemma6Eq21Line]

lemma chen1973Lemma6_eq21_primeSum_nonneg (x : ℕ) :
    0 ≤ chen1973Lemma6Eq21PrimeSum x := by
  unfold chen1973Lemma6Eq21PrimeSum
  positivity

lemma chen1973Lemma6_eq21_contourMajorant_nonneg
    (x L B k m : ℕ) :
    0 ≤ chen1973Lemma6Eq21ContourMajorant x L B k m := by
  unfold chen1973Lemma6Eq21ContourMajorant
  positivity

/-- Strongest honest assembly of the three analytic arrows printed in (21).

* `hshift` is the zero-free contour deformation from the actual `N` block;
* `hcontour` is the displayed `(log x)^200` contour estimate;
* `hprime` is the final decay estimate for the explicit prime-pair sum.

They are deliberately separate, source-shaped inequalities, rather than a
premise restating the desired terminal bound. -/
theorem chen1973Lemma6_equation21_of_source_estimates
    (Cshift Ccontour : ℝ) (hCshift : 0 ≤ Cshift)
    {x L B k m l₂ : ℕ}
    (_P : Chen1973Lemma6Eq21SourceParameters x L B k m l₂)
    {c : ℝ} (hzeroFree : Chen1973Lemma6Eq21ZeroFreeInput x L c)
    (hshift :
      Chen1973Lemma6Eq21ZeroFreeInput x L c →
        chen1973Lemma6NmBlockActual x L 0 B k m ≤
          Cshift * chen1973Lemma6Eq21ContourMajorant x L B k m)
    (hcontour :
      chen1973Lemma6Eq21ContourMajorant x L B k m ≤
        Ccontour * Real.log x ^ (200 : ℕ) * chen1973Lemma6Eq21PrimeSum x)
    (hprime :
      Cshift * (Ccontour * Real.log x ^ (200 : ℕ) *
        chen1973Lemma6Eq21PrimeSum x) ≤
          (x : ℝ) / Real.log x ^ (20 : ℕ)) :
    chen1973Lemma6NmBlockActual x L 0 B k m ≤
      (x : ℝ) / Real.log x ^ (20 : ℕ) := by
  exact (hshift hzeroFree).trans
    ((mul_le_mul_of_nonneg_left hcontour hCshift).trans hprime)

/-- The exact `(19),(20),(21)` cell join for actual source objects.  Positive
levels are dispatched by the already-proved source partition; level zero is
precisely the new equation-(21) lane. -/
theorem chen1973Lemma6_equations19_20_21_actual_join
    {x L B D I₁ I₂ m level k : ℕ}
    (hlevel : level ∈ Finset.range (I₁ + 1))
    (hk : k ∈ Finset.range (I₂ + 1))
    (hLast : ∀ j ∈ Finset.Icc 1 I₁, L * 2 ^ j ≤ 2 * D)
    (h19 : ∀ j ∈ Finset.Icc 1 I₁, ∀ i ∈ Finset.range (I₂ + 1),
      chen1973Lemma6Eq19Cell x L B D j i →
        chen1973Lemma6NmBlockActual x L j B i m ≤
          (x : ℝ) / Real.log x ^ (20 : ℕ))
    (h20 : ∀ j ∈ Finset.Icc 1 I₁, ∀ i ∈ Finset.range (I₂ + 1),
      chen1973Lemma6Eq20Cell x L B D j i →
        chen1973Lemma6NmBlockActual x L j B i m ≤
          (x : ℝ) / Real.log x ^ (20 : ℕ))
    (h21 : ∀ i ∈ Finset.range (I₂ + 1),
      chen1973Lemma6NmBlockActual x L 0 B i m ≤
        (x : ℝ) / Real.log x ^ (20 : ℕ)) :
    chen1973Lemma6NmBlockActual x L level B k m ≤
      (x : ℝ) / Real.log x ^ (20 : ℕ) := by
  by_cases hzero : level = 0
  · subst level
    exact h21 k hk
  · have hlevelPos : 1 ≤ level := Nat.one_le_iff_ne_zero.mpr hzero
    have hlevelIcc : level ∈ Finset.Icc 1 I₁ := by
      exact Finset.mem_Icc.mpr ⟨hlevelPos, by
        simp only [Finset.mem_range] at hlevel
        omega⟩
    rcases chen1973Lemma6_eq19_or_eq20 hlevelPos (hLast level hlevelIcc) with h | h
    · exact h19 level hlevelIcc k hk h
    · exact h20 level hlevelIcc k hk h

end AnalyticNumberTheory.LargeSieve
