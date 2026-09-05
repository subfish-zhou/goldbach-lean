/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nous Research
-/
import MathlibNt.SieveTheory.LinearSieve.Richert.Richert1969Theorem1FiniteChain

/-!
# Richert 1969: Lemma 3 and the payment from ordinary Bombieri

Frozen source:

* `references/richert-1969/richert-1969.pdf`, PDF page 14, equations
  (3.24)--(3.25);
* the same PDF, pages 17--20, especially ordinary Bombieri (4.18) and the
  following Cauchy--Schwarz argument;
* `references/richert-1969/VISION_TRANSCRIPTION.md`, sections 7 and 9.

The source does not invoke a weighted Bombieri theorem as a black box.  It
applies Cauchy--Schwarz, uses Lemma 3 with `h = 9` to pay the square of
`3 ^ omega(d)`, and uses a pointwise `d E*(N,d)` envelope on the second factor.
The theorem below records exactly that finite implication.
-/

noncomputable section

open Finset
open scoped BigOperators

namespace MathlibNt.SieveTheory.Richert1969

/-- The divisor weight in the square of Richert's `3 ^ omega(d)` error sum. -/
def lemma3NineOmegaMass (S : Finset ℕ) : ℝ :=
  ∑ d ∈ S, (9 : ℝ) ^ d.primeFactors.card / (d : ℝ)

/-- The weighted error sum that appears after the two sieve remainders are
reindexed by their combined modulus. -/
def threeOmegaErrorMass (S : Finset ℕ) (E : ℕ → ℝ) : ℝ :=
  ∑ d ∈ S, (3 : ℝ) ^ d.primeFactors.card * E d

/-- Richert's Lemma 3 at `h = 9`, specialized to a finite squarefree carrier:
the required mass is dominated by the finite `J₉` Euler-product mass. -/
theorem lemma3NineOmegaMass_le_J9Mass
    (S : Finset ℕ) (Q : ℕ)
    (hS : S ⊆ Finset.range (Q + 1))
    (hSquarefree : ∀ d ∈ S, Squarefree d) :
    lemma3NineOmegaMass S ≤ LiuWeight.liuPanPrimePowerJ9Mass Q := by
  have hrewrite :
      lemma3NineOmegaMass S =
        ∑ d ∈ S,
          (((ArithmeticFunction.moebius d : ℤ) : ℝ) ^ 2) *
            (9 : ℝ) ^ d.primeFactors.card / d := by
    unfold lemma3NineOmegaMass
    apply Finset.sum_congr rfl
    intro d hd
    rw [SwitchingPrinciple.moebius_sq_eq_one_of_squarefree
      (hSquarefree d hd)]
    ring
  rw [hrewrite]
  unfold LiuWeight.liuPanPrimePowerJ9Mass
  apply Finset.sum_le_sum_of_subset_of_nonneg hS
  intro d hdRange hdS
  positivity

/-- The `h = 9` case of Richert's Lemma 3 in the polylogarithmic form used
after Cauchy--Schwarz.  Its constant is independent of the carrier and cutoff. -/
theorem lemma3NineOmegaMass_le_polylog :
    ∃ C : ℝ, 0 < C ∧ ∀ (Q : ℕ) (S : Finset ℕ),
      S ⊆ Finset.range (Q + 1) →
      (∀ d ∈ S, Squarefree d) →
      lemma3NineOmegaMass S ≤
        C * (Real.log (Q + 2)) ^ (9 : ℝ) := by
  obtain ⟨C, hC, hJ9⟩ := LiuWeight.liuPanPrimePowerJ9Mass_le_polylog
  refine ⟨C, hC, ?_⟩
  intro Q S hS hSquarefree
  exact (lemma3NineOmegaMass_le_J9Mass S Q hS hSquarefree).trans (hJ9 Q)

/-- Finite Cauchy--Schwarz in the exact form used after (4.18).

`sum E` is the ordinary Bombieri mass.  The pointwise estimate
`d * E d ≤ X` turns the second Cauchy factor into `X * sum E`; the first factor
is the `h = 9` instance of Lemma 3. -/
theorem weightedError_sq_le_lemma3Mass_mul_ordinary
    (S : Finset ℕ) (w E : ℕ → ℝ) (X : ℝ)
    (hd : ∀ d ∈ S, 0 < d)
    (hE : ∀ d ∈ S, 0 ≤ E d)
    (henvelope : ∀ d ∈ S, (d : ℝ) * E d ≤ X) :
    (∑ d ∈ S, w d * E d) ^ 2 ≤
      (∑ d ∈ S, w d ^ 2 / (d : ℝ)) *
        (X * ∑ d ∈ S, E d) := by
  let a : ℕ → ℝ := fun d => w d / Real.sqrt d
  let b : ℕ → ℝ := fun d => Real.sqrt d * E d
  have hab :
      (∑ d ∈ S, w d * E d) = ∑ d ∈ S, a d * b d := by
    apply Finset.sum_congr rfl
    intro d hdS
    have hdR : (0 : ℝ) < d := by exact_mod_cast hd d hdS
    have hsqrt : Real.sqrt (d : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr hdR
    dsimp [a, b]
    field_simp
  rw [hab]
  refine (Finset.sum_mul_sq_le_sq_mul_sq S a b).trans ?_
  have ha :
      (∑ d ∈ S, a d ^ 2) =
        ∑ d ∈ S, w d ^ 2 / (d : ℝ) := by
    apply Finset.sum_congr rfl
    intro d hdS
    have hdR : (0 : ℝ) < d := by exact_mod_cast hd d hdS
    dsimp [a]
    rw [div_pow, Real.sq_sqrt hdR.le]
  have hb :
      (∑ d ∈ S, b d ^ 2) ≤ X * ∑ d ∈ S, E d := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro d hdS
    have hdR : (0 : ℝ) ≤ d := by positivity
    have hEd := hE d hdS
    calc
      b d ^ 2 = (d : ℝ) * E d ^ 2 := by
        dsimp [b]
        rw [mul_pow, Real.sq_sqrt hdR]
      _ = ((d : ℝ) * E d) * E d := by ring
      _ ≤ X * E d := mul_le_mul_of_nonneg_right (henvelope d hdS) hEd
  rw [ha]
  exact mul_le_mul_of_nonneg_left hb
    (Finset.sum_nonneg fun d hdS => div_nonneg (sq_nonneg _) (by positivity))

/-- Richert's explicit payment: Lemma 3 at `h = 9`, ordinary Bombieri (4.18),
and the elementary pointwise envelope imply the `3 ^ omega` weighted error
bound.  No weighted Bombieri conclusion is assumed. -/
theorem threeOmegaError_sq_le_of_ordinaryBombieri
    (S : Finset ℕ) (E : ℕ → ℝ) (X L B : ℝ)
    (hd : ∀ d ∈ S, 0 < d)
    (hE : ∀ d ∈ S, 0 ≤ E d)
    (hX : 0 ≤ X) (hL : 0 ≤ L)
    (henvelope : ∀ d ∈ S, (d : ℝ) * E d ≤ X)
    (hLemma3 : lemma3NineOmegaMass S ≤ L ^ (9 : ℕ))
    (hOrdinaryBombieri : (∑ d ∈ S, E d) ≤ B) :
    threeOmegaErrorMass S E ^ 2 ≤ L ^ (9 : ℕ) * (X * B) := by
  have hcauchy :=
    weightedError_sq_le_lemma3Mass_mul_ordinary S
      (fun d => (3 : ℝ) ^ d.primeFactors.card) E X
      hd hE henvelope
  have hmass :
      (∑ d ∈ S,
          ((3 : ℝ) ^ d.primeFactors.card) ^ 2 / (d : ℝ)) =
        lemma3NineOmegaMass S := by
    unfold lemma3NineOmegaMass
    apply Finset.sum_congr rfl
    intro d hdS
    rw [pow_two, ← mul_pow]
    norm_num
  rw [hmass] at hcauchy
  calc
    threeOmegaErrorMass S E ^ 2 ≤
        lemma3NineOmegaMass S * (X * ∑ d ∈ S, E d) := by
      simpa [threeOmegaErrorMass] using hcauchy
    _ ≤ L ^ (9 : ℕ) * (X * ∑ d ∈ S, E d) := by
      gcongr
      exact mul_nonneg hX (Finset.sum_nonneg fun d hdS => hE d hdS)
    _ ≤ L ^ (9 : ℕ) * (X * B) := by
      gcongr

/-- Richert's complete finite payment from Lemma 3 and an ordinary Bombieri
mass, with no weighted Bombieri conclusion assumed.  Squarefreeness and the
cutoff discharge Lemma 3 through `J₉`; Cauchy--Schwarz pays the `3^ω` weight. -/
theorem threeOmegaError_sq_le_of_ordinaryBombieri_squarefree
    (S : Finset ℕ) (Q : ℕ) (E : ℕ → ℝ) (X B : ℝ)
    (hS : S ⊆ Finset.range (Q + 1))
    (hSquarefree : ∀ d ∈ S, Squarefree d)
    (hE : ∀ d ∈ S, 0 ≤ E d)
    (hX : 0 ≤ X)
    (henvelope : ∀ d ∈ S, (d : ℝ) * E d ≤ X)
    (hOrdinaryBombieri : (∑ d ∈ S, E d) ≤ B) :
    ∃ C : ℝ, 0 < C ∧
      threeOmegaErrorMass S E ^ 2 ≤
        (C * (Real.log (Q + 2)) ^ (9 : ℝ)) * (X * B) := by
  obtain ⟨C, hC, hLemma3⟩ := lemma3NineOmegaMass_le_polylog
  have hd : ∀ d ∈ S, 0 < d := by
    intro d hdS
    exact Nat.pos_of_ne_zero fun hd0 => by
      subst d
      simpa using hSquarefree 0 hdS
  have hcauchy :=
    weightedError_sq_le_lemma3Mass_mul_ordinary S
      (fun d => (3 : ℝ) ^ d.primeFactors.card) E X
      hd hE henvelope
  have hmass :
      (∑ d ∈ S,
          ((3 : ℝ) ^ d.primeFactors.card) ^ 2 / (d : ℝ)) =
        lemma3NineOmegaMass S := by
    unfold lemma3NineOmegaMass
    apply Finset.sum_congr rfl
    intro d hdS
    rw [pow_two, ← mul_pow]
    norm_num
  rw [hmass] at hcauchy
  refine ⟨C, hC, ?_⟩
  calc
    threeOmegaErrorMass S E ^ 2 ≤
        lemma3NineOmegaMass S * (X * ∑ d ∈ S, E d) := by
      simpa [threeOmegaErrorMass] using hcauchy
    _ ≤ (C * (Real.log (Q + 2)) ^ (9 : ℝ)) *
        (X * ∑ d ∈ S, E d) := by
      exact mul_le_mul_of_nonneg_right
        (hLemma3 Q S hS hSquarefree)
        (mul_nonneg hX (Finset.sum_nonneg fun d hdS => hE d hdS))
    _ ≤ (C * (Real.log (Q + 2)) ^ (9 : ℝ)) * (X * B) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hOrdinaryBombieri hX)
        (mul_nonneg hC.le (Real.rpow_nonneg
          (Real.log_nonneg (by exact_mod_cast
            (show 1 ≤ Q + 2 by omega))) 9))

end MathlibNt.SieveTheory.Richert1969
