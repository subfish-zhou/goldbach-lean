/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nous Research
-/
import MathlibNt.SieveTheory.SwitchingPrinciple

/-!
# Richert 1969, Theorem 1: finite weighted-sieve chain

Frozen source:

* `references/richert-1969/richert-1969.pdf`, PDF pages 8--11,
  equations (3.1)--(3.11);
* `references/richert-1969/VISION_TRANSCRIPTION.md`, sections 5 and 9.

The paper's Theorem A is quoted rather than proved.  This file therefore proves
only the finite implication that consumes a lower `S(A,z)`, every conditioned
upper `S(A,p,z)`, and the squareful exclusion.  It does not introduce an axiom,
and it does not assume the weighted conclusion.
-/

noncomputable section

open Finset
open scoped BigOperators

namespace MathlibNt.SieveTheory.Richert1969

/-- The finite carrier counted by the lower object `S(A,z)`. -/
def lowerCarrier (A : Finset ℕ) (P : ℕ) : Finset ℕ :=
  A.filter fun a => Nat.Coprime P a

/-- The primed carrier in (3.1): square divisibility by a weighted prime is
excluded before the Richert weight is summed. -/
def squarefreeWeightedCarrier (A Q : Finset ℕ) (P : ℕ) : Finset ℕ :=
  (lowerCarrier A P).filter fun a => ∀ p ∈ Q, ¬p ^ 2 ∣ a

/-- The exact finite squareful correction removed from the lower carrier. -/
def squarefulCorrection (A Q : Finset ℕ) (P : ℕ) : ℝ :=
  ((lowerCarrier A P).card : ℝ) -
    ((squarefreeWeightedCarrier A Q P).card : ℝ)

/-- The prime-conditioned upper object `S(A,p,z)`. -/
def primeConditionedCarrier (A : Finset ℕ) (P p : ℕ) : Finset ℕ :=
  (lowerCarrier A P).filter fun a => p ∣ a

/-- The finite weighted lower object in (3.1), with the source prime interval
encoded by `Q` and the source factor `1 - u log p / log X` encoded by `w`. -/
def weightedLowerObject
    (A Q : Finset ℕ) (P : ℕ) (lambda : ℝ) (w : ℕ → ℝ) : ℝ :=
  ∑ a ∈ squarefreeWeightedCarrier A Q P,
    (1 - lambda * ∑ p ∈ Q, if p ∣ a then w p else 0)

/-- The weighted sum of all prime-conditioned upper objects. -/
def primeConditionedUpperAggregate
    (A Q : Finset ℕ) (P : ℕ) (w : ℕ → ℝ) : ℝ :=
  ∑ p ∈ Q, w p * ((primeConditionedCarrier A P p).card : ℝ)

/-- The exact prime interval in (3.1), including the restriction `p ∤ K`. -/
noncomputable def theoremOneWeightedPrimes
    (X : ℝ) (K : ℕ) (u v : ℝ) : Finset ℕ :=
  (Finset.range ⌈X ^ (1 / u)⌉₊).filter fun p : ℕ =>
    p.Prime ∧ X ^ (1 / v) ≤ p ∧ (p : ℝ) < X ^ (1 / u) ∧ ¬p ∣ K

/-- The finite product `P_K(X^(1/v))` defining the lower sifted carrier. -/
noncomputable def theoremOneSiftingProduct
    (X : ℝ) (K : ℕ) (v : ℝ) : ℕ :=
  ((Finset.range ⌈X ^ (1 / v)⌉₊).filter fun p : ℕ =>
    p.Prime ∧ (p : ℝ) < X ^ (1 / v) ∧ ¬p ∣ K).prod id

/-- Richert's logarithmic prime weight `1 - u log p / log X` in (3.1). -/
noncomputable def theoremOnePrimeWeight (X u : ℝ) (p : ℕ) : ℝ :=
  1 - u * Real.log p / Real.log X

/-- The literal finite object `W_K(A,v,u,lambda)` from (3.1)--(3.2). -/
noncomputable def theoremOneWeightedLowerObject
    (A : Finset ℕ) (X : ℝ) (K : ℕ) (v u lambda : ℝ) : ℝ :=
  weightedLowerObject A (theoremOneWeightedPrimes X K u v)
    (theoremOneSiftingProduct X K v) lambda (theoremOnePrimeWeight X u)

private theorem weighted_divisor_sum_eq
    (A Q : Finset ℕ) (P : ℕ) (w : ℕ → ℝ) :
    (∑ a ∈ squarefreeWeightedCarrier A Q P,
        ∑ p ∈ Q, if p ∣ a then w p else 0) =
      ∑ p ∈ Q, w p *
        (((squarefreeWeightedCarrier A Q P).filter fun a => p ∣ a).card : ℝ) := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  rw [← Finset.sum_filter]
  simp [mul_comm]

private theorem squarefree_conditioned_card_le
    (A Q : Finset ℕ) (P p : ℕ) :
    ((squarefreeWeightedCarrier A Q P).filter fun a => p ∣ a).card ≤
      (primeConditionedCarrier A P p).card := by
  apply Finset.card_le_card
  intro a ha
  rcases Finset.mem_filter.mp ha with ⟨haGood, hpa⟩
  exact Finset.mem_filter.mpr
    ⟨(Finset.mem_filter.mp haGood).1, hpa⟩

/-- Equations (3.5)--(3.8), before any analytic estimate: the weighted lower
object is bounded below by the lower sieve, minus the exact squareful
correction, minus the weighted sum of the prime-conditioned upper sieves. -/
theorem lower_sub_squareful_sub_conditioned_le_weightedLowerObject
    (A Q : Finset ℕ) (P : ℕ) (lambda : ℝ) (w : ℕ → ℝ)
    (hlambda : 0 ≤ lambda) (hw : ∀ p ∈ Q, 0 ≤ w p) :
    ((lowerCarrier A P).card : ℝ) - squarefulCorrection A Q P -
        lambda * primeConditionedUpperAggregate A Q P w ≤
      weightedLowerObject A Q P lambda w := by
  have hweighted :
      (∑ p ∈ Q, w p *
          (((squarefreeWeightedCarrier A Q P).filter fun a => p ∣ a).card : ℝ)) ≤
        primeConditionedUpperAggregate A Q P w := by
    unfold primeConditionedUpperAggregate
    apply Finset.sum_le_sum
    intro p hp
    exact mul_le_mul_of_nonneg_left
      (by exact_mod_cast squarefree_conditioned_card_le A Q P p) (hw p hp)
  unfold weightedLowerObject squarefulCorrection
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
    ← Finset.mul_sum, weighted_divisor_sum_eq]
  have hscale := mul_le_mul_of_nonneg_left hweighted hlambda
  nlinarith

/-- Equation (3.5) for the literal interval and logarithmic weight of
Theorem 1.  The later analytic estimates (3.6)--(3.11) are separate inputs. -/
theorem theoremOneFiniteLowerBound
    (A : Finset ℕ) (X : ℝ) (K : ℕ) (v u lambda : ℝ)
    (hlambda : 0 ≤ lambda)
    (hweight :
      ∀ p ∈ theoremOneWeightedPrimes X K u v,
        0 ≤ theoremOnePrimeWeight X u p) :
    ((lowerCarrier A (theoremOneSiftingProduct X K v)).card : ℝ) -
        squarefulCorrection A (theoremOneWeightedPrimes X K u v)
          (theoremOneSiftingProduct X K v) -
        lambda * primeConditionedUpperAggregate A
          (theoremOneWeightedPrimes X K u v)
          (theoremOneSiftingProduct X K v) (theoremOnePrimeWeight X u) ≤
      theoremOneWeightedLowerObject A X K v u lambda := by
  exact lower_sub_squareful_sub_conditioned_le_weightedLowerObject
    A (theoremOneWeightedPrimes X K u v)
    (theoremOneSiftingProduct X K v) lambda (theoremOnePrimeWeight X u)
    hlambda hweight

namespace Chen

open SwitchingPrinciple

/-- The lower `S(A,z)` in the Chen specialization is exactly the source
Goldbach candidate count. -/
theorem lowerS_eq_candidateCard (N : ℕ) :
    (jurkatRichertSourceBoundingSieve N).siftedSum =
      (jurkatRichertSourceCandidates N).card :=
  jurkatRichertSourceBoundingSieve_siftedSum_eq_card N

/-- Every `S(A,p,z)` in the Chen specialization is the literal conditioned
candidate count, including the nonreduced `p ∣ N` lanes. -/
theorem primeConditionedUpperS_eq_candidateCard (N p : ℕ) :
    (jurkatRichertSourceConditionedBoundingSieve N p).siftedSum =
      ((jurkatRichertSourceCandidates N).filter fun q => p ∣ N - q).card :=
  jurkatRichertSourceConditionedBoundingSieve_siftedSum_eq_card N p

/-- Chen's displayed weighted object is the lower sieve minus one half of the
sum of its prime-conditioned upper sieves. -/
theorem weightedLowerObject_eq_lower_sub_half_conditioned (N : ℕ) :
    jurkatRichertSourceWeightedCount N =
      ((jurkatRichertSourceCandidates N).card : ℝ) -
        jurkatRichertSourceMediumPrimeAggregate N / 2 :=
  jurkatRichertSourceWeightedCount_eq N

/-- The prime sum is paid by the Stieltjes/partial-summation integral, with the
exact coefficient `8 * (log 8 + K / 2)`. -/
theorem stieltjesPrimeIntegral :
    ChenJurkatRichertVaryingQPrimeSumAsymptotic :=
  chenJurkatRichertVaryingQPrimeSumAsymptotic

/-- The downstream Chen proper-prime-power correction.  This is distinct from
Richert's direct `(A4)` payment for the removed `p^2 ∣ a` carrier in (3.7). -/
theorem squarefulCorrection_le
    (N : ℕ) (hN : 2 ^ 110 < N) (hEven : Even N) :
    jurkatRichertDistinctWeightedCount N -
        30 * (N : ℝ) ^ (9 / 10 : ℝ) ≤
      jurkatRichertWeightedCount N :=
  jurkatRichertDistinctWeightedCount_sub_proper_le N hN hEven

/-- The Chen-facing conclusion from the two quoted lower/upper Theorem A
coefficient dependencies and the two distribution inputs.  Theorem A remains
an explicit imported dependency; Richert 1969 does not prove it. -/
theorem weightedLowerBound_of_importedTheoremA
    (hLowerTheoremA : DimensionOneLowerRosserDensityFundamentalLemma)
    (hOrdinaryBombieri : BombieriVinogradov.StandardBombieriVinogradov)
    (hUpperTheoremA : DimensionOneUpperRosserDensityFundamentalLemma)
    (hWeightedBombieri : ChenJurkatRichertVaryingQWeightedBombieriVinogradov) :
    ChenJurkatRichertWeightedLowerBound :=
  chenJurkatRichertWeightedLowerBound_of_literature_inputs
    hLowerTheoremA hOrdinaryBombieri hUpperTheoremA hWeightedBombieri

end Chen

end MathlibNt.SieveTheory.Richert1969
