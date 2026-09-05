

import MathlibNt.AnalyticNumberTheory.Vaughan.VaughanTypeIEnergy

/-!
 # Structured Type-II coefficient energy for Vaughan's identity

This module opens the large--large divisor pair in `vaughanThird`.  Its
coefficient budget retains the outer large divisor multiplicity, the inner
large divisor multiplicity for each outer divisor, and every Möbius and von
Mangoldt weight.  In particular the Type-II lane is not bounded by treating
`vaughanTypeIICoeff` as an opaque sequence.
-/

namespace AnalyticNumberTheory.LargeSieve

open Classical Finset
open scoped BigOperators ArithmeticFunction

noncomputable section

/-- Cardinality-form Cauchy--Schwarz, used separately on the two large divisor
layers of `vaughanThird`. -/
private theorem typeII_sum_sq_le_card_mul_sum_sq {α : Type*} (s : Finset α)
    (f : α → ℝ) :
    (∑ a ∈ s, f a) ^ 2 ≤ (s.card : ℝ) * ∑ a ∈ s, (f a) ^ 2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq s (fun _ => (1 : ℝ)) f
  simpa using h

/-- The genuine large--large divisor-pair energy of `vaughanThird`.

The first cardinality counts eligible `d > u`; the cardinality inside the
`d`-sum counts eligible `e > v` dividing `n / d`.  The summand keeps the
factorized Möbius/von-Mangoldt weight instead of hiding it in a packaged
Type-II coefficient. -/
def vaughanTypeIIDivisorEnergy (n u v : ℕ) : ℝ :=
  ((n.divisors.filter fun d => u < d).card : ℝ) *
    ∑ d ∈ n.divisors.filter (fun d => u < d),
      (((n / d).divisors.filter fun e => v < e).card : ℝ) *
        ∑ e ∈ (n / d).divisors.filter (fun e => v < e),
          (((ArithmeticFunction.moebius d : ℤ) : ℝ) *
            ArithmeticFunction.vonMangoldt e) ^ 2

/-- Nested Cauchy--Schwarz on the actual large--large divisor structure. -/
theorem vaughanThird_sq_le_divisorEnergy (n u v : ℕ) :
    Sieve.vaughanThird n u v ^ 2 ≤ vaughanTypeIIDivisorEnergy n u v := by
  unfold Sieve.vaughanThird vaughanTypeIIDivisorEnergy
  let D := n.divisors.filter (fun d => u < d)
  let E : ℕ → Finset ℕ := fun d => (n / d).divisors.filter (fun e => v < e)
  let c : ℕ → ℕ → ℝ := fun d e =>
    ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
      ArithmeticFunction.vonMangoldt e
  calc
    (∑ d ∈ D, ∑ e ∈ E d, c d e) ^ 2
        ≤ (D.card : ℝ) * ∑ d ∈ D, (∑ e ∈ E d, c d e) ^ 2 :=
      typeII_sum_sq_le_card_mul_sum_sq D (fun d => ∑ e ∈ E d, c d e)
    _ ≤ (D.card : ℝ) *
        ∑ d ∈ D, ((E d).card : ℝ) * ∑ e ∈ E d, (c d e) ^ 2 := by
      gcongr with d hd
      exact typeII_sum_sq_le_card_mul_sum_sq (E d) (c d)

/-- The same structural estimate at the public Type-II alias. -/
theorem vaughanTypeII_sq_le_divisorEnergy (n u v : ℕ) :
    vaughanTypeII n u v ^ 2 ≤ vaughanTypeIIDivisorEnergy n u v := by
  simpa [vaughanTypeII] using vaughanThird_sq_le_divisorEnergy n u v

lemma vaughanTypeIIDivisorEnergy_nonneg (n u v : ℕ) :
    0 ≤ vaughanTypeIIDivisorEnergy n u v := by
  unfold vaughanTypeIIDivisorEnergy
  positivity

/-- Pointwise coefficient estimate with the scalar coefficient `b n` separate
from the expanded large--large divisor energy. -/
theorem vaughanTypeIICoeff_norm_sq_le_divisorEnergy
    (b : ℤ → ℂ) (u v : ℕ) (n : ℤ) :
    ‖vaughanTypeIICoeff b u v n‖ ^ 2 ≤
      ‖b n‖ ^ 2 * vaughanTypeIIDivisorEnergy n.toNat u v := by
  rw [vaughanTypeIICoeff, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    mul_pow]
  have h := vaughanTypeII_sq_le_divisorEnergy n.toNat u v
  have hb : 0 ≤ ‖b n‖ ^ 2 := sq_nonneg _
  have hr : |vaughanTypeII n.toNat u v| ^ 2 =
      vaughanTypeII n.toNat u v ^ 2 := sq_abs _
  rw [hr]
  exact mul_le_mul_of_nonneg_left h hb

/-- Structured finite `ℓ²` coefficient energy on `[1,N]`.  The interval keeps
`N` literal, while each summand keeps `u`, `v`, both divisor multiplicities,
and all Möbius/Λ weights. -/
theorem vaughanTypeIICoeff_energy_le_divisorEnergy
    (b : ℤ → ℂ) (N u v : ℕ) :
    (∑ n ∈ Finset.Icc (1 : ℤ) N,
      ‖vaughanTypeIICoeff b u v n‖ ^ 2) ≤
      ∑ n ∈ Finset.Icc (1 : ℤ) N,
        ‖b n‖ ^ 2 * vaughanTypeIIDivisorEnergy n.toNat u v := by
  exact Finset.sum_le_sum fun n _ =>
    vaughanTypeIICoeff_norm_sq_le_divisorEnergy b u v n

/-- Weighted Vaughan prefix ledger with both non-small lanes expanded.  Type I
uses its cutoff-factor divisor budget and Type II uses the genuine large--large
nested divisor-pair energy above; only the explicitly retained small range is
left as a packaged norm lane. -/
theorem weighted_vaughan_prefix_large_sieve_structured_ledger
    (b : ℤ → ℂ) (N Q u v : ℕ) (hQ : 0 < Q) :
    (∑ q ∈ Finset.Icc 1 Q,
      ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ : PrimitiveCharacter q,
          primitiveCharacterPrefixMaxSquare (vaughanLambdaCoeff b) 0 N q χ) ≤
      3 * (((Nat.log2 N + 1 : ℕ) : ℝ) ^ 2) *
        primitiveLargeSieveConstant N Q *
        ((∑ n ∈ Finset.Icc (1 : ℤ) N,
            ‖b n‖ ^ 2 * vaughanTypeICutoffEnergy n.toNat u v) +
          (∑ n ∈ Finset.Icc (1 : ℤ) N,
            ‖b n‖ ^ 2 * vaughanTypeIIDivisorEnergy n.toNat u v) +
          (∑ n ∈ Finset.Icc (1 : ℤ) N,
            ‖vaughanSmallCoeff b v n‖ ^ 2)) := by
  refine (weighted_vaughan_prefix_large_sieve_typeI_ledger b N Q u v hQ).trans ?_
  apply mul_le_mul_of_nonneg_left
  · gcongr with n hn
    exact vaughanTypeIICoeff_norm_sq_le_divisorEnergy b u v n
  · unfold primitiveLargeSieveConstant
    positivity

end

end AnalyticNumberTheory.LargeSieve
