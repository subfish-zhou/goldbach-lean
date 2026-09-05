

import MathlibNt.AnalyticNumberTheory.Vaughan.VaughanTypeIIBilinearFourthMomentScale
import MathlibNt.AnalyticNumberTheory.LargeSieve.BombieriDavenport

/-!
 # Explicit Q-dependent bilinear tensor moment bound

Expanding the outer `d`-sum and applying Cauchy only in `d` reduces the
bilinear tensor second moment (the mixed fourth moment for rank-one tensors) to
one nonmaximal weighted primitive large sieve for every row.  Thus the exact
rowwise charge is

`D * (M + c(Q) * Q^2) * coefficientEnergy`,

where `c(Q) = 2 * ceil (log(Q^2) / log 2) + 12`.  This module also compares
that expression with the genuine bilinear scale and gives an unconditional
producer for the canonical Vaughan block.  No prefix maximum is present; a
prefix version should be obtained separately by the dyadic/Rademacher--Menshov
reduction, paying its displayed logarithm squared.
-/

namespace AnalyticNumberTheory.LargeSieve

open Classical Finset
open scoped BigOperators ArithmeticFunction

noncomputable section

/-- The explicit logarithmic coefficient in the current primitive large sieve. -/
def primitiveBilinearQFactor (Q : ℕ) : ℝ :=
  2 * (Nat.ceil (Real.log ((Q : ℝ) ^ 2) / Real.log 2) : ℝ) + 12

lemma primitiveBilinearQFactor_nonneg (Q : ℕ) :
    0 ≤ primitiveBilinearQFactor Q := by
  unfold primitiveBilinearQFactor
  positivity

lemma one_le_primitiveBilinearQFactor (Q : ℕ) :
    1 ≤ primitiveBilinearQFactor Q := by
  unfold primitiveBilinearQFactor
  have h : 0 ≤ (Nat.ceil (Real.log ((Q : ℝ) ^ 2) / Real.log 2) : ℝ) := by
    positivity
  linarith

private lemma bilinearTensorCharacterForm_norm_sq_le_card
    (A : ℕ → ℤ → ℂ) (DS : Finset ℕ) (M q : ℕ)
    (χ : PrimitiveCharacter q) :
    ‖bilinearTensorCharacterForm A DS M q χ‖ ^ 2 ≤
      (DS.card : ℝ) * ∑ d ∈ DS,
        ‖∑ t ∈ Finset.Icc (1 : ℤ) M,
          A d t * χ.1 (t : ZMod q)‖ ^ 2 := by
  let R : ℕ → ℂ := fun d =>
    ∑ t ∈ Finset.Icc (1 : ℤ) M, A d t * χ.1 (t : ZMod q)
  have hform : bilinearTensorCharacterForm A DS M q χ =
      ∑ d ∈ DS, χ.1 (d : ZMod q) * R d := by
    unfold bilinearTensorCharacterForm
    apply Finset.sum_congr rfl
    intro d hd
    dsimp [R]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t ht
    ring
  rw [hform]
  have hnorm := norm_sum_le DS (fun d => χ.1 (d : ZMod q) * R d)
  have hsq : ‖∑ d ∈ DS, χ.1 (d : ZMod q) * R d‖ ^ 2 ≤
      (∑ d ∈ DS, ‖χ.1 (d : ZMod q) * R d‖) ^ 2 := by
    exact pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  have hcs : (∑ d ∈ DS, ‖χ.1 (d : ZMod q) * R d‖) ^ 2 ≤
      (DS.card : ℝ) * ∑ d ∈ DS, ‖χ.1 (d : ZMod q) * R d‖ ^ 2 := by
    simpa only [one_mul, one_pow, sum_const, nsmul_eq_mul, mul_one] using
      (Finset.sum_mul_sq_le_sq_mul_sq DS
        (fun _d => (1 : ℝ)) (fun d => ‖χ.1 (d : ZMod q) * R d‖))
  refine hsq.trans (hcs.trans ?_)
  apply mul_le_mul_of_nonneg_left
  · apply Finset.sum_le_sum
    intro d hd
    rw [norm_mul, mul_pow]
    have hχ := DirichletCharacter.norm_le_one χ.1 (d : ZMod q)
    have hχ0 := norm_nonneg (χ.1 (d : ZMod q))
    have hχsq : ‖χ.1 (d : ZMod q)‖ ^ 2 ≤ 1 := by nlinarith
    simpa [R] using mul_le_mul_of_nonneg_right hχsq (sq_nonneg ‖R d‖)
  · positivity

/-- Explicit generic nonmaximal bilinear tensor inequality.  Cauchy in `d`
and the existing weighted primitive large sieve give exactly the rowwise scale
`D * (M + c(Q) Q^2)` times the full Frobenius energy. -/
theorem weighted_primitive_bilinearTensor_explicit
    (A : ℕ → ℤ → ℂ) (DS : Finset ℕ) (D M Q : ℕ)
    (hQ : 0 < Q) (hcard : DS.card ≤ D) :
    (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
      ∑ χ : PrimitiveCharacter q,
        ‖bilinearTensorCharacterForm A DS M q χ‖ ^ 2) ≤
      (D : ℝ) * ((M : ℝ) + primitiveBilinearQFactor Q * (Q : ℝ) ^ 2) *
        bilinearTensorCoeffEnergy A DS M := by
  let S : ℕ → (q : ℕ) → PrimitiveCharacter q → ℝ := fun d q χ =>
    ‖∑ t ∈ Finset.Icc (1 : ℤ) M, A d t * χ.1 (t : ZMod q)‖ ^ 2
  have hq : ∀ q ∈ Finset.Icc 1 Q,
      (∑ χ : PrimitiveCharacter q,
        ‖bilinearTensorCharacterForm A DS M q χ‖ ^ 2) ≤
        (DS.card : ℝ) * ∑ d ∈ DS, ∑ χ : PrimitiveCharacter q, S d q χ := by
    intro q hq
    calc
      _ ≤ ∑ χ : PrimitiveCharacter q,
          (DS.card : ℝ) * ∑ d ∈ DS, S d q χ := by
        apply Finset.sum_le_sum
        intro χ hχ
        simpa [S] using bilinearTensorCharacterForm_norm_sq_le_card A DS M q χ
      _ = (DS.card : ℝ) * ∑ d ∈ DS,
          ∑ χ : PrimitiveCharacter q, S d q χ := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
  have hcauchy :
      (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ : PrimitiveCharacter q,
          ‖bilinearTensorCharacterForm A DS M q χ‖ ^ 2) ≤
        (DS.card : ℝ) * ∑ d ∈ DS, ∑ q ∈ Finset.Icc 1 Q,
          ((q : ℝ) / (q.totient : ℝ)) * ∑ χ : PrimitiveCharacter q, S d q χ := by
    calc
      _ ≤ ∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
          ((DS.card : ℝ) * ∑ d ∈ DS,
            ∑ χ : PrimitiveCharacter q, S d q χ) := by
        apply Finset.sum_le_sum
        intro q hqm
        exact mul_le_mul_of_nonneg_left (hq q hqm) (by positivity)
      _ = (DS.card : ℝ) * ∑ d ∈ DS, ∑ q ∈ Finset.Icc 1 Q,
          ((q : ℝ) / (q.totient : ℝ)) * ∑ χ : PrimitiveCharacter q, S d q χ := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro d hd
        apply Finset.sum_congr rfl
        intro q hq
        apply Finset.sum_congr rfl
        intro χ hχ
        ring
  refine hcauchy.trans ?_
  have hrow : ∀ d ∈ DS,
      (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ : PrimitiveCharacter q, S d q χ) ≤
        ((M : ℝ) + primitiveBilinearQFactor Q * (Q : ℝ) ^ 2) *
          ∑ t ∈ Finset.Icc (1 : ℤ) M, ‖A d t‖ ^ 2 := by
    intro d hd
    simpa [S, primitiveBilinearQFactor] using
      weighted_primitive_bombieri_davenport_explicit (A d) 0 M Q hQ
  have hcardR : (DS.card : ℝ) ≤ (D : ℝ) := by exact_mod_cast hcard
  have hscale : 0 ≤ (M : ℝ) + primitiveBilinearQFactor Q * (Q : ℝ) ^ 2 := by
    exact add_nonneg (by positivity)
      (mul_nonneg (primitiveBilinearQFactor_nonneg Q) (sq_nonneg _))
  calc
    (DS.card : ℝ) * ∑ d ∈ DS, ∑ q ∈ Finset.Icc 1 Q,
        ((q : ℝ) / (q.totient : ℝ)) * ∑ χ : PrimitiveCharacter q, S d q χ
      ≤ (DS.card : ℝ) * ∑ d ∈ DS,
          (((M : ℝ) + primitiveBilinearQFactor Q * (Q : ℝ) ^ 2) *
            ∑ t ∈ Finset.Icc (1 : ℤ) M, ‖A d t‖ ^ 2) := by
        apply mul_le_mul_of_nonneg_left
        · exact Finset.sum_le_sum fun d hd => hrow d hd
        · positivity
    _ = (DS.card : ℝ) *
        (((M : ℝ) + primitiveBilinearQFactor Q * (Q : ℝ) ^ 2) *
          bilinearTensorCoeffEnergy A DS M) := by
        unfold bilinearTensorCoeffEnergy
        simp_rw [Finset.mul_sum]
    _ ≤ (D : ℝ) *
        (((M : ℝ) + primitiveBilinearQFactor Q * (Q : ℝ) ^ 2) *
          bilinearTensorCoeffEnergy A DS M) := by
        apply mul_le_mul_of_nonneg_right hcardR
        exact mul_nonneg hscale (by unfold bilinearTensorCoeffEnergy; positivity)
    _ = _ := by ring

/-- The rowwise explicit scale is bounded by the genuine bilinear product scale,
with only the displayed logarithmic factor `c(Q)`. -/
theorem rowwise_bilinear_scale_le_polylog_product (D M Q : ℕ) :
    (D : ℝ) * ((M : ℝ) + primitiveBilinearQFactor Q * (Q : ℝ) ^ 2) ≤
      primitiveBilinearQFactor Q * bilinearMultiplicativeScale D M Q := by
  rw [bilinearMultiplicativeScale_eq]
  have hc := one_le_primitiveBilinearQFactor Q
  have hD : 0 ≤ (D : ℝ) := by positivity
  have hM : 0 ≤ (M : ℝ) := by positivity
  have hQ2 : 0 ≤ (Q : ℝ) ^ 2 := sq_nonneg _
  nlinarith [mul_nonneg hD hM, mul_nonneg hD hQ2,
    mul_nonneg hM hQ2, sq_nonneg ((Q : ℝ) ^ 2)]

/-- Q-dependent version of the generic frontier.  Unlike
`BilinearTensorFourthMomentBound K`, its coefficient is allowed to display the
unavoidable current `Q`-logarithm. -/
def QDependentBilinearTensorFourthMomentBound (K : ℕ → ℝ) : Prop :=
  ∀ (A : ℕ → ℤ → ℂ) (DS : Finset ℕ) (D M Q : ℕ), 0 < Q → DS.card ≤ D →
    (∀ d ∈ DS, d < 2 * D) →
    (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
      ∑ χ : PrimitiveCharacter q,
        ‖bilinearTensorCharacterForm A DS M q χ‖ ^ 2) ≤
      K Q * bilinearMultiplicativeScale D M Q *
        bilinearTensorCoeffEnergy A DS M

/-- Unconditional producer for the generic Q-dependent bilinear tensor bound. -/
theorem qDependentBilinearTensorFourthMomentBound_producer :
    QDependentBilinearTensorFourthMomentBound primitiveBilinearQFactor := by
  intro A DS D M Q hQ hcard hsupport
  refine (weighted_primitive_bilinearTensor_explicit A DS D M Q hQ hcard).trans ?_
  apply mul_le_mul_of_nonneg_right (rowwise_bilinear_scale_le_polylog_product D M Q)
  unfold bilinearTensorCoeffEnergy
  positivity

lemma vaughanCanonicalBilinearBlock_eq_bilinearTensorCharacterForm
    (b : ℕ → ℂ) (y N u v k l q : ℕ) (χ : PrimitiveCharacter q) :
    vaughanTypeIICanonicalBilinearBlock b y N u v k l q χ =
      bilinearTensorCharacterForm
        (vaughanCanonicalBilinearTensor b y N v l)
        (vaughanCanonicalDyadicBlock N u k)
        (vaughanCanonicalTensorLength y k) q χ := by
  change vaughanBilinearBlockOn vaughanMoebiusCoeff vaughanMangoldtCoeff b y
      (vaughanCanonicalDyadicBlock N u k)
      (vaughanCanonicalDyadicBlock N v l) q χ = _
  rw [vaughanBilinearBlockOn_eq_tensor]
  · unfold bilinearTensorCharacterForm vaughanCanonicalBilinearTensor
    apply Finset.sum_congr rfl
    intro d hd
    have hL : vaughanCanonicalTensorLength y k ≤ y :=
      Nat.div_le_self y (2 ^ k)
    have hsub : Finset.Icc (1 : ℤ) (vaughanCanonicalTensorLength y k) ⊆
        Finset.Icc (1 : ℤ) y :=
      Finset.Icc_subset_Icc_right (by exact_mod_cast hL)
    rw [← Finset.sum_subset hsub]
    · simp_rw [Finset.mul_sum]
      ring
    · intro t hty htshort
      have htpos : 0 < t :=
        lt_of_lt_of_le Int.zero_lt_one (Finset.mem_Icc.mp hty).1
      have htcast : (t.toNat : ℤ) = t := Int.toNat_of_nonneg htpos.le
      have hlt : vaughanCanonicalTensorLength y k < t.toNat := by
        by_contra h
        apply htshort
        exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hty).1, by
          rw [← htcast]
          exact_mod_cast le_of_not_gt h⟩
      rw [vaughanBilinearTensorCoeff_canonical_eq_zero
        b y N u v k l d t hd hty hlt]
      simp
  · intro d hd
    exact (mem_vaughanCanonicalDyadicBlock.mp hd).1
  · intro e he
    exact (mem_vaughanCanonicalDyadicBlock.mp he).1

lemma vaughanCanonicalBilinearTensor_coeffEnergy_le
    (b : ℕ → ℂ) (y N u v k l : ℕ) :
    bilinearTensorCoeffEnergy
        (vaughanCanonicalBilinearTensor b y N v l)
        (vaughanCanonicalDyadicBlock N u k)
        (vaughanCanonicalTensorLength y k) ≤
      vaughanCanonicalShortTensorEnergy vaughanMangoldtCoeff b
        y N u v k l := by
  unfold bilinearTensorCoeffEnergy vaughanCanonicalBilinearTensor
    vaughanCanonicalShortTensorEnergy
  apply Finset.sum_le_sum
  intro d hd
  apply Finset.sum_le_sum
  intro t ht
  rw [norm_mul, mul_pow]
  have hμ : ‖vaughanMoebiusCoeff d‖ ^ 2 ≤ (1 : ℝ) := by
    rcases ArithmeticFunction.moebius_eq_or d with h | h | h <;>
      simp [vaughanMoebiusCoeff, h]
  simpa using mul_le_mul_of_nonneg_right hμ
    (sq_nonneg ‖vaughanBilinearTensorCoeff vaughanMangoldtCoeff b y d
      (vaughanCanonicalDyadicBlock N v l) t‖)

/-- Canonical Vaughan-block producer with no frozen fourth-moment hypothesis.
This is the nonmaximal rectangle bound at the product scale, with the explicit
current `Q`-logarithm. -/
theorem weighted_primitive_vaughanCanonicalBilinear_unconditional
    (b : ℕ → ℂ) (y N u v k l Q : ℕ) (hQ : 0 < Q) :
    (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
      ∑ χ : PrimitiveCharacter q,
        ‖vaughanTypeIICanonicalBilinearBlock b y N u v k l q χ‖ ^ 2) ≤
      primitiveBilinearQFactor Q *
        bilinearMultiplicativeScale (2 ^ k) (vaughanCanonicalTensorLength y k) Q *
        vaughanCanonicalShortTensorEnergy vaughanMangoldtCoeff b
          y N u v k l := by
  simp_rw [vaughanCanonicalBilinearBlock_eq_bilinearTensorCharacterForm]
  refine (qDependentBilinearTensorFourthMomentBound_producer
    (vaughanCanonicalBilinearTensor b y N v l)
    (vaughanCanonicalDyadicBlock N u k) (2 ^ k)
    (vaughanCanonicalTensorLength y k) Q hQ
    (card_vaughanCanonicalDyadicBlock_le_pow N u k) ?_).trans ?_
  · intro d hd
    simpa [Nat.pow_succ, Nat.mul_comm] using
      (vaughanCanonicalDyadicBlock_pow_bounds hd).2
  · apply mul_le_mul_of_nonneg_left
    exact vaughanCanonicalBilinearTensor_coeffEnergy_le b y N u v k l
    exact mul_nonneg (primitiveBilinearQFactor_nonneg Q)
      (bilinearMultiplicativeScale_nonneg _ _ _)

end

end AnalyticNumberTheory.LargeSieve
