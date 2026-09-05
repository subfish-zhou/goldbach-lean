/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nous Research
-/
import MathlibNt.AnalyticNumberTheory.Chen1973.Chen1973Lemma5SwitchedTripleSource

/-!
# Chen 1973, Lemma 6: source spine for the `M₂` bound

This file follows printed pp. 119--123, equations (12)--(21).  It freezes the
actual `M₂` from `Chen1973Lemma5SwitchedTripleSource`, the literal prime-pair
and conductor dyadic carriers, and the finite reindexing behind (13).

The analytic estimates are deliberately not hidden in a conclusion-shaped
record.  The terminal theorem takes separately named hypotheses with the exact
roles of displayed equations (12), (19), (20), and (21), plus the final
logarithmic absorption.  All finite carrier identities are proved here.

The source's finite Dirichlet polynomial is represented by `Finset.range H`
(in natural order).  This matters on the `β = 1/2 + 1/log x` line: no
conditionally convergent infinite reordering is introduced.

Source ledger (verified directly on printed pp. 119--123):

* (12) is `M₂ ≪ (log x)^6 max_{1<m≤x^(1/2)} N_m`.
* (13) uses `0≤l≤I₁`, `0≤k≤I₂`, low conductors
  `1<d≤(log x)^100`, high cells
  `2^(l-1)(log x)^100<d≤2^l(log x)^100`, and pair cells
  `x^(13/30)2^k<p₁p₂≤x^(13/30)2^(k+1)`.
* (14) is the second moment for `1-LS`; (15) is the fourth moment of the
  natural-order polynomial `S(H,β+iv,χ)`; (16) is the algebraic `L'/L`
  split; (17) has the printed second prefactor `x^(1/2)`.
* (18) bounds `3^ν(d)` on squarefree conductors.  Equations (19) and (20)
  give `N_m^(l,k) ≪ x/(log x)^20`; in the second case the printed choice is
  `H=max(2^(2l-k)x^(-13/30)(log x)^400 I_{l,x}, x^(1/2-ε))`.
* (21) treats the low-conductor `l=0` cells using the primitive-character
  zero-free line.  Finally (12), (13), and (19)--(21) yield the printed
  `M₂ ≪ x/(log x)^2.01`.
-/

noncomputable section

open Classical Complex Finset
open scoped BigOperators ArithmeticFunction

namespace AnalyticNumberTheory.LargeSieve

/-- The p. 120 polynomial `S(H,s,χ)=∑_{n=1}^H μ(n)χ(n)n⁻ˢ`, with the
natural-number order made literal. -/
def chen1973Lemma6MobiusPartialSum {d : ℕ} (H : ℕ) (s : ℂ)
    (χ : PrimitiveCharacter d) : ℂ :=
  ∑ n ∈ Finset.Icc 1 H,
    ((ArithmeticFunction.moebius n : ℤ) : ℂ) * χ.1 (n : ZMod d) / (n : ℂ) ^ s

/-- The exact finite square before collecting equal products into the source's
coefficient `j(n)`.  Both indices are natural-order finite partial sums, so this
identity is valid equally on the `Re(s)≤1` line used in (15). -/
theorem chen1973Lemma6_mobiusPartialSum_sq
    {d H : ℕ} (s : ℂ) (χ : PrimitiveCharacter d) :
    chen1973Lemma6MobiusPartialSum H s χ ^ 2 =
      ∑ a ∈ Finset.Icc 1 H, ∑ b ∈ Finset.Icc 1 H,
        (((ArithmeticFunction.moebius a : ℤ) : ℂ) * χ.1 (a : ZMod d) / (a : ℂ) ^ s) *
          (((ArithmeticFunction.moebius b : ℤ) : ℂ) * χ.1 (b : ZMod d) / (b : ℂ) ^ s) := by
  unfold chen1973Lemma6MobiusPartialSum
  simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]

/-- A dyadic shell with the source convention `B·2^k < size ≤ B·2^(k+1)`. -/
def chen1973Lemma6DyadicShell {α : Type*} [DecidableEq α]
    (S : Finset α) (size : α → ℕ) (B k : ℕ) : Finset α :=
  S.filter fun a => B * 2 ^ k < size a ∧ size a ≤ B * 2 ^ (k + 1)

/-- The complete dyadic hull covered by levels `0,…,K`. -/
def chen1973Lemma6DyadicHull {α : Type*} [DecidableEq α]
    (S : Finset α) (size : α → ℕ) (B K : ℕ) : Finset α :=
  S.filter fun a => B < size a ∧ size a ≤ B * 2 ^ (K + 1)

private theorem chen1973Lemma6_mem_some_dyadicShell
    {n B K : ℕ} (hB : 0 < B) (hlo : B < n) (hhi : n ≤ B * 2 ^ (K + 1)) :
    ∃ k ≤ K, B * 2 ^ k < n ∧ n ≤ B * 2 ^ (k + 1) := by
  let q := (n - 1) / B
  have hBn : B ≤ n - 1 := by omega
  have hq : q ≠ 0 := by
    have : 1 ≤ q := (Nat.le_div_iff_mul_le hB).2 (by simpa using hBn)
    omega
  refine ⟨Nat.log2 q, ?_, ?_, ?_⟩
  · have hqK : q < 2 ^ (K + 1) := by
      apply (Nat.div_lt_iff_lt_mul hB).2
      rw [Nat.mul_comm]
      omega
    exact Nat.le_of_lt_succ ((Nat.log2_lt hq).2 hqK)
  · have hpow : 2 ^ Nat.log2 q ≤ q := Nat.log2_self_le hq
    have hmul : B * 2 ^ Nat.log2 q ≤ B * q := Nat.mul_le_mul_left B hpow
    have hdiv : B * q ≤ n - 1 := by
      simpa [q, Nat.mul_comm] using Nat.mul_div_le (n - 1) B
    omega
  · have hqpow : q < 2 ^ (Nat.log2 q + 1) := Nat.lt_log2_self
    have := (Nat.div_lt_iff_lt_mul hB).1 hqpow
    rw [Nat.mul_comm] at this
    omega

private theorem chen1973Lemma6_dyadicShell_disjoint
    {α : Type*} [DecidableEq α] (S : Finset α) (size : α → ℕ)
    {B i j : ℕ} (hB : 0 < B) (hij : i ≠ j) :
    Disjoint (chen1973Lemma6DyadicShell S size B i)
      (chen1973Lemma6DyadicShell S size B j) := by
  rw [Finset.disjoint_left]
  intro a hai haj
  simp only [chen1973Lemma6DyadicShell, Finset.mem_filter] at hai haj
  rcases hai with ⟨_, hi0, hi1⟩
  rcases haj with ⟨_, hj0, hj1⟩
  rcases lt_or_gt_of_ne hij with hij' | hji'
  · have hp : 2 ^ (i + 1) ≤ 2 ^ j := Nat.pow_le_pow_right (by omega) (by omega)
    have hm := Nat.mul_le_mul_left B hp
    omega
  · have hp : 2 ^ (j + 1) ≤ 2 ^ i := Nat.pow_le_pow_right (by omega) (by omega)
    have hm := Nat.mul_le_mul_left B hp
    omega

/-- Exact finite union of the printed dyadic shells. -/
theorem chen1973Lemma6_biUnion_dyadicShell_eq_hull
    {α : Type*} [DecidableEq α] (S : Finset α) (size : α → ℕ)
    {B K : ℕ} (hB : 0 < B) :
    (Finset.range (K + 1)).biUnion (chen1973Lemma6DyadicShell S size B) =
      chen1973Lemma6DyadicHull S size B K := by
  ext a
  simp only [Finset.mem_biUnion, Finset.mem_range, chen1973Lemma6DyadicShell,
    chen1973Lemma6DyadicHull, Finset.mem_filter]
  constructor
  · rintro ⟨k, hk, haS, hlo, hhi⟩
    refine ⟨haS, ?_, ?_⟩
    · have hpow : (1 : ℕ) ≤ 2 ^ k := Nat.one_le_two_pow
      have hmul := Nat.mul_le_mul_left B hpow
      exact lt_of_le_of_lt (by simpa using hmul) hlo
    · exact le_trans hhi (Nat.mul_le_mul_left B
        (Nat.pow_le_pow_right (by omega) (by omega)))
  · rintro ⟨haS, hlo, hhi⟩
    obtain ⟨k, hk, hklo, hkhi⟩ :=
      chen1973Lemma6_mem_some_dyadicShell hB hlo hhi
    exact ⟨k, by omega, haS, hklo, hkhi⟩

/-- The printed shells are pairwise disjoint; hence finite sums may be
reindexed without multiplicity. -/
theorem chen1973Lemma6_dyadicShell_pairwiseDisjoint
    {α : Type*} [DecidableEq α] (S : Finset α) (size : α → ℕ)
    {B K : ℕ} (hB : 0 < B) :
    ((Finset.range (K + 1) : Finset ℕ) : Set ℕ).PairwiseDisjoint
      (chen1973Lemma6DyadicShell S size B) := by
  intro i hi j hj hij
  exact chen1973Lemma6_dyadicShell_disjoint S size hB hij

/-- Exact sum reindexing over the source dyadic hull. -/
theorem chen1973Lemma6_sum_dyadicShell
    {α : Type*} [DecidableEq α] (S : Finset α) (size : α → ℕ)
    {B K : ℕ} (hB : 0 < B) (f : α → ℝ) :
    ∑ a ∈ chen1973Lemma6DyadicHull S size B K, f a =
      ∑ k ∈ Finset.range (K + 1),
        ∑ a ∈ chen1973Lemma6DyadicShell S size B k, f a := by
  rw [← chen1973Lemma6_biUnion_dyadicShell_eq_hull S size hB]
  exact Finset.sum_biUnion (chen1973Lemma6_dyadicShell_pairwiseDisjoint S size hB)

/-- The literal p. 119 prime-pair shell
`x^(13/30)2^k < p₁p₂ ≤ x^(13/30)2^(k+1)`, represented by an honest natural
base cutoff `B`; the real-power correspondence is stated separately below. -/
def chen1973Lemma6PrimePairShell (x B k m : ℕ) : Finset (ℕ × ℕ) :=
  chen1973Lemma6DyadicShell
    ((chen1973Lemma5PrimePairs x).filter fun pp => Nat.Coprime (pp.1 * pp.2) m)
    (fun pp => pp.1 * pp.2) B k

/-- Honest cutoff bridge for the printed `x^(13/30)` boundary. -/
def Chen1973ThirteenThirtiethCutoff (x B : ℕ) : Prop :=
  ∀ n : ℕ, B < n ↔ (x : ℝ) ^ ((13 : ℝ) / 30) < n

/-- The conductor blocks in (13): level zero is `1<d≤L`; level `l+1` is
`2^l L<d≤2^(l+1)L`. -/
def chen1973Lemma6ConductorBlock (x L level : ℕ) : Finset ℕ :=
  if level = 0 then
    (Finset.Ioc 1 L).filter (fun d => Nat.Coprime d x ∧ Squarefree d)
  else
    (chen1973Lemma6DyadicShell (Finset.Ioc 1 (L * 2 ^ level)) id L (level - 1)).filter
      (fun d => Nat.Coprime d x ∧ Squarefree d)

/-- The exact p. 119 summand of `N_m`, with Chen's Möbius/`3^ν` weight,
primitive-character sum, reciprocal logarithm, and actual semiprime carrier.
`Phi d χ y` is the displayed contour kernel `Φ(y,χ)` defined at the start of
Lemma 6; it is not an arbitrary coefficient sequence on integers. -/
def chen1973Lemma6NmBlock (x L level B k m : ℕ)
    (Phi : (d : ℕ) → PrimitiveCharacter d → ℝ → ℂ) : ℝ :=
  ∑ d ∈ chen1973Lemma6ConductorBlock x L level,
    |((ArithmeticFunction.moebius d : ℤ) : ℝ)| * (3 : ℝ) ^ d.primeFactors.card / d *
      ‖∑ χ : PrimitiveCharacter d,
        star (χ.1 (x : ZMod d)) *
          ∑ pp ∈ chen1973Lemma6PrimePairShell x B k m,
            (Real.log ((x : ℝ) / ((pp.1 : ℝ) * pp.2)))⁻¹ *
              Phi d χ ((x : ℝ) / ((pp.1 : ℝ) * pp.2)) *
                χ.1 ((pp.1 * pp.2 : ℕ) : ZMod d)‖

/-- The complete right side of source equation (13). -/
def chen1973Lemma6DyadicMajorant (x L I1 B I2 m : ℕ)
    (Phi : (d : ℕ) → PrimitiveCharacter d → ℝ → ℂ) : ℝ :=
  ∑ level ∈ Finset.range (I1 + 1),
    ∑ k ∈ Finset.range (I2 + 1),
      chen1973Lemma6NmBlock x L level B k m Phi

/-- `1≤l≤I₁` cells in the first two ranges treated by source equation (19). -/
def chen1973Lemma6Eq19Cell (x L B D level k : ℕ) : Prop :=
  1 ≤ level ∧
    (D < B * 2 ^ k ∨
      (B * 2 ^ k ≤ D ∧ L * 2 ^ level < B * 2 ^ k))

/-- `1≤l≤I₁` cells in the complementary range treated by source equation (20). -/
def chen1973Lemma6Eq20Cell (x L B D level k : ℕ) : Prop :=
  1 ≤ level ∧ B * 2 ^ k ≤ L * 2 ^ level ∧ L * 2 ^ level ≤ 2 * D

/-- Every positive-level cell is assigned to (19) or (20), under the printed
last-shell relation `D < 2^I₁L ≤ 2D`. -/
theorem chen1973Lemma6_eq19_or_eq20
    {x L B D level k : ℕ} (hlevel : 1 ≤ level) (hLast : L * 2 ^ level ≤ 2 * D) :
    chen1973Lemma6Eq19Cell x L B D level k ∨
      chen1973Lemma6Eq20Cell x L B D level k := by
  unfold chen1973Lemma6Eq19Cell chen1973Lemma6Eq20Cell
  by_cases hBD : D < B * 2 ^ k
  · exact Or.inl ⟨hlevel, Or.inl hBD⟩
  · by_cases hLB : L * 2 ^ level < B * 2 ^ k
    · exact Or.inl ⟨hlevel, Or.inr ⟨by omega, hLB⟩⟩
    · exact Or.inr ⟨hlevel, by omega, hLast⟩

/-- Transparent source chain (12), (13), (19)--(21) to Lemma 6's terminal
`2.01` bound.  Each analytic input is a concrete inequality about the displayed
quantity; there is no `Prop` wrapper carrying the conclusion. -/
theorem chen1973Lemma6M2_le_twoPointZeroOne
    (x D L I1 B I2 m : ℕ)
    (Phi : (d : ℕ) → PrimitiveCharacter d → ℝ → ℂ)
    (h12 : chen1973Lemma5M2 x D ≤
      Real.log x ^ 6 * chen1973Lemma6DyadicMajorant x L I1 B I2 m Phi)
    (h19 : ∀ level ∈ Finset.Icc 1 I1, ∀ k ∈ Finset.range (I2 + 1),
      chen1973Lemma6Eq19Cell x L B D level k →
        chen1973Lemma6NmBlock x L level B k m Phi ≤ x / Real.log x ^ 20)
    (h20 : ∀ level ∈ Finset.Icc 1 I1, ∀ k ∈ Finset.range (I2 + 1),
      chen1973Lemma6Eq20Cell x L B D level k →
        chen1973Lemma6NmBlock x L level B k m Phi ≤ x / Real.log x ^ 20)
    (h21 : ∀ k ∈ Finset.range (I2 + 1),
      chen1973Lemma6NmBlock x L 0 B k m Phi ≤ x / Real.log x ^ 20)
    (hLast : ∀ level ∈ Finset.Icc 1 I1, L * 2 ^ level ≤ 2 * D)
    (hAbsorb : Real.log x ^ 6 *
      (((I1 + 1 : ℕ) : ℝ) * ((I2 + 1 : ℕ) : ℝ) *
        (x / Real.log x ^ 20)) ≤ x / Real.log x ^ (2.01 : ℝ)) :
    chen1973Lemma5M2 x D ≤ x / Real.log x ^ (2.01 : ℝ) := by
  apply h12.trans
  apply le_trans (mul_le_mul_of_nonneg_left ?_ (by positivity)) hAbsorb
  unfold chen1973Lemma6DyadicMajorant
  calc
    (∑ level ∈ Finset.range (I1 + 1),
      ∑ k ∈ Finset.range (I2 + 1), chen1973Lemma6NmBlock x L level B k m Phi) ≤
        ∑ level ∈ Finset.range (I1 + 1),
          ∑ _k ∈ Finset.range (I2 + 1), x / Real.log x ^ 20 := by
      apply Finset.sum_le_sum
      intro level hlevel
      apply Finset.sum_le_sum
      intro k hk
      by_cases hl0 : level = 0
      · simpa [hl0] using h21 k hk
      · have hlI : level ∈ Finset.Icc 1 I1 := by
          simp only [Finset.mem_range] at hlevel
          simp only [Finset.mem_Icc]
          omega
        have hlevel1 : 1 ≤ level := by
          simp only [Finset.mem_Icc] at hlI
          exact hlI.1
        rcases chen1973Lemma6_eq19_or_eq20 (x := x) (B := B)
            (D := D) (L := L) (k := k) (level := level)
            hlevel1 (hLast level hlI) with hcell | hcell
        · exact h19 level hlI k hk hcell
        · exact h20 level hlI k hk hcell
    _ = (((I1 + 1 : ℕ) : ℝ) * ((I2 + 1 : ℕ) : ℝ) *
        (x / Real.log x ^ 20)) := by
      simp [mul_assoc]

end AnalyticNumberTheory.LargeSieve
