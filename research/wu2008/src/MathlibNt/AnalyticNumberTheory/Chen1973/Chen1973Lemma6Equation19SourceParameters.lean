/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nous Research
-/
import MathlibNt.AnalyticNumberTheory.Chen1973.Chen1973Lemma6Equation19
import Mathlib.Tactic

/-!
# Chen 1973, Lemma 6, equation (19): source parameters

This module freezes the literal positive-level parameter domain on p. 122.
The conductor cell is
`L*2^(level-1) < d ≤ L*2^level`, the pair cell is
`B*2^k < p₁p₂ ≤ B*2^(k+1)`. The legacy height helpers in this module
use the actual maximum W, not the printed exponential I. The genuine source
height `⌈2^level (log x)^200 I_{level,x}⌉₊` is defined in SourceWeightHeight.

No final-payment hypothesis is stored in the source packet.  The final
logarithmic payments below are proved from explicit large-`x` inequalities.
Any constant coming from a source `≪` is therefore quantified once, before all
cell parameters.
-/

noncomputable section

open Classical Complex Finset Set
open scoped BigOperators ArithmeticFunction

namespace AnalyticNumberTheory.LargeSieve

/-- Lower endpoint of the positive-level conductor cell. -/
def chen1973Lemma6Eq19SourceD (L level : ℕ) : ℕ :=
  L * 2 ^ (level - 1)

/-- Upper endpoint of the positive-level conductor cell. -/
def chen1973Lemma6Eq19SourceQ (L level : ℕ) : ℕ :=
  L * 2 ^ level

/-- Lower endpoint of the equation-(19) prime-pair shell. -/
def chen1973Lemma6Eq19PairD (B k : ℕ) : ℕ :=
  B * 2 ^ k

/-- Upper endpoint of the equation-(19) prime-pair shell. -/
def chen1973Lemma6Eq19PairQ (B k : ℕ) : ℕ :=
  B * 2 ^ (k + 1)

/-- The real legacy W-based cutoff; not the printed exponential-I height. -/
def chen1973Lemma6Eq19HeightReal (x L level : ℕ) : ℝ :=
  (2 : ℝ) ^ level * Real.log x ^ (200 : ℕ) *
    chen1973Lemma6Eq19I x L level

/-- Literal p. 122 positive-level equation-(19) domain.

`lastD` is Chen's final conductor cutoff occurring in the branch split.  It is
not confused with the lower endpoint `chen1973Lemma6Eq19SourceD L level`.
The real-to-natural identifications `L ≈ (log x)^100` and
`B ≈ x^(13/30)` are kept as exact two-sided rounding inequalities. -/
structure Chen1973Lemma6Eq19SourceParameters
    (x L B lastD level k : ℕ) : Prop where
  hx : 3 ≤ x
  hL : 0 < L
  hB : 0 < B
  hlevel : 1 ≤ level
  hlog_one : 1 ≤ Real.log x
  hL_lower : (L : ℝ) ≤ Real.log x ^ (100 : ℕ)
  hL_upper : Real.log x ^ (100 : ℕ) < L + 1
  hB_lower : (B : ℝ) ≤ (x : ℝ) ^ ((13 : ℝ) / 30)
  hB_upper : (x : ℝ) ^ ((13 : ℝ) / 30) < B + 1
  hbranch : chen1973Lemma6Eq19Cell x L B lastD level k

lemma chen1973Lemma6Eq19SourceParameters.log_pos
    {x L B lastD level k : ℕ}
    (P : Chen1973Lemma6Eq19SourceParameters x L B lastD level k) :
    0 < Real.log x := by
  exact lt_of_lt_of_le zero_lt_one P.hlog_one


lemma chen1973Lemma6Eq19SourceParameters.branch
    {x L B lastD level k : ℕ}
    (P : Chen1973Lemma6Eq19SourceParameters x L B lastD level k) :
    lastD < chen1973Lemma6Eq19PairD B k ∨
      (chen1973Lemma6Eq19PairD B k ≤ lastD ∧
        chen1973Lemma6Eq19SourceQ L level < chen1973Lemma6Eq19PairD B k) := by
  simpa [chen1973Lemma6Eq19Cell, chen1973Lemma6Eq19PairD,
    chen1973Lemma6Eq19SourceQ] using P.hbranch.2

lemma chen1973Lemma6Eq19SourceD_pos
    {x L B lastD level k : ℕ}
    (P : Chen1973Lemma6Eq19SourceParameters x L B lastD level k) :
    0 < chen1973Lemma6Eq19SourceD L level := by
  unfold chen1973Lemma6Eq19SourceD
  exact Nat.mul_pos P.hL (pow_pos (by omega) _)

lemma chen1973Lemma6Eq19SourceQ_pos
    {x L B lastD level k : ℕ}
    (P : Chen1973Lemma6Eq19SourceParameters x L B lastD level k) :
    0 < chen1973Lemma6Eq19SourceQ L level := by
  unfold chen1973Lemma6Eq19SourceQ
  exact Nat.mul_pos P.hL (pow_pos (by omega) _)

lemma chen1973Lemma6Eq19SourceQ_ge_two
    {x L B lastD level k : ℕ}
    (P : Chen1973Lemma6Eq19SourceParameters x L B lastD level k) :
    2 ≤ chen1973Lemma6Eq19SourceQ L level := by
  unfold chen1973Lemma6Eq19SourceQ
  have hp : 2 ≤ 2 ^ level := by
    simpa using (Nat.pow_le_pow_right (by omega : 0 < 2) P.hlevel)
  exact le_trans hp (Nat.le_mul_of_pos_left _ P.hL)

lemma chen1973Lemma6Eq19SourceD_lt_Q
    {x L B lastD level k : ℕ}
    (P : Chen1973Lemma6Eq19SourceParameters x L B lastD level k) :
    chen1973Lemma6Eq19SourceD L level < chen1973Lemma6Eq19SourceQ L level := by
  unfold chen1973Lemma6Eq19SourceD chen1973Lemma6Eq19SourceQ
  apply Nat.mul_lt_mul_of_pos_left
  · exact Nat.pow_lt_pow_right (by omega) (Nat.sub_lt P.hlevel (by omega))
  · exact P.hL

/-- The actual conductor carrier lies in the literal positive-level interval. -/
theorem chen1973Lemma6_eq19_conductorBlock_subset_source_Ioc
    {x L B lastD level k : ℕ}
    (P : Chen1973Lemma6Eq19SourceParameters x L B lastD level k) :
    ∀ ⦃d⦄, d ∈ chen1973Lemma6ConductorBlock x L level →
      d ∈ Finset.Ioc (chen1973Lemma6Eq19SourceD L level)
        (chen1973Lemma6Eq19SourceQ L level) := by
  intro d hd
  unfold chen1973Lemma6ConductorBlock at hd
  rw [if_neg (Nat.ne_of_gt P.hlevel)] at hd
  simp only [chen1973Lemma6DyadicShell, Finset.mem_filter] at hd
  apply Finset.mem_Ioc.mpr
  have hlev : level - 1 + 1 = level := Nat.sub_add_cancel P.hlevel
  exact ⟨by simpa [chen1973Lemma6Eq19SourceD] using hd.1.2.1,
    by simpa [chen1973Lemma6Eq19SourceQ, hlev] using hd.1.2.2⟩



lemma chen1973Lemma6Eq19Height_eq_ceil
    (x L level : ℕ) :
    chen1973Lemma6Eq19Height x L level =
      ⌈chen1973Lemma6Eq19HeightReal x L level⌉₊ := by
  rfl

lemma chen1973Lemma6Eq19HeightReal_pos
    {x L B lastD level k : ℕ}
    (P : Chen1973Lemma6Eq19SourceParameters x L B lastD level k) :
    0 < chen1973Lemma6Eq19HeightReal x L level := by
  unfold chen1973Lemma6Eq19HeightReal
  have hlog := chen1973Lemma6Eq19SourceParameters.log_pos P
  have hI := chen1973Lemma6Eq19I_pos x L level
  positivity






/-- Uniform polylogarithmic absorption.  The absolute constant is selected
before `x` and before every cell parameter; `hlarge` is the explicit large-`x`
threshold. -/
theorem chen1973Lemma6_eq19_absorb_global_constant
    (Cabs : ℝ) {x : ℝ} (_hC : 0 ≤ Cabs) (hlog : 1 ≤ Real.log x)
    {a b : ℕ} (hab : a ≤ b)
    (hlarge : Cabs ≤ Real.log x ^ (b - a)) :
    Cabs * Real.log x ^ a ≤ Real.log x ^ b := by
  calc
    Cabs * Real.log x ^ a ≤ Real.log x ^ (b - a) * Real.log x ^ a := by
      gcongr
    _ = Real.log x ^ b := by
      rw [← pow_add]
      congr
      omega


end AnalyticNumberTheory.LargeSieve
