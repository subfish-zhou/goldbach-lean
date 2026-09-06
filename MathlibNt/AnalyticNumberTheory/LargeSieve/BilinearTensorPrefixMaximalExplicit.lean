

import MathlibNt.AnalyticNumberTheory.LargeSieve.BilinearTensorFourthMomentExplicit
import MathlibNt.AnalyticNumberTheory.LargeSieve.DyadicPrefixMaximal
import MathlibNt.AnalyticNumberTheory.LargeSieve.ImprimitiveConductorWeightLinear
import MathlibNt.AnalyticNumberTheory.Vaughan.VaughanTypeIIActualTensorMomentExplicit

/-!
 # Prefix-maximal explicit bilinear tensor estimate

This independent leaf upgrades the explicit nonmaximal bilinear tensor estimate
to the complete maximum over the collected `t`-prefix.  The aligned dyadic
Rademacher--Menshov decomposition in `DyadicPrefixMaximal` pays exactly
`(Nat.log2 M + 1)^2`; Cauchy in the outer row variable does not move the
maximum outside the primitive-character sum.
-/

namespace AnalyticNumberTheory.LargeSieve

open Classical Finset
open scoped BigOperators ArithmeticFunction

noncomputable section

/-- Square of the bilinear tensor form truncated at the collected-variable
prefix `1 ≤ t ≤ y`. -/
def bilinearTensorCharacterPrefixSquare
    (A : ℕ → ℤ → ℂ) (DS : Finset ℕ) (y q : ℕ)
    (χ : PrimitiveCharacter q) : ℝ :=
  ‖∑ d ∈ DS, ∑ t ∈ Finset.Icc (1 : ℤ) y,
      A d t * χ.1 ((d : ℤ) * t : ZMod q)‖ ^ 2

/-- Complete `t`-prefix maximum for a bilinear tensor form. -/
def bilinearTensorCharacterPrefixMaxSquare
    (A : ℕ → ℤ → ℂ) (DS : Finset ℕ) (M q : ℕ)
    (χ : PrimitiveCharacter q) : ℝ :=
  ((Finset.range (M + 1)).image
      (fun y => bilinearTensorCharacterPrefixSquare A DS y q χ)).max'
    (Finset.image_nonempty.mpr ⟨0, by simp⟩)

lemma bilinearTensorCharacterPrefixMaxSquare_nonneg
    (A : ℕ → ℤ → ℂ) (DS : Finset ℕ) (M q : ℕ)
    (χ : PrimitiveCharacter q) :
    0 ≤ bilinearTensorCharacterPrefixMaxSquare A DS M q χ := by
  unfold bilinearTensorCharacterPrefixMaxSquare
  refine (sq_nonneg ‖(0 : ℂ)‖).trans ?_
  apply Finset.le_max'
  refine Finset.mem_image.mpr ⟨0, by simp, ?_⟩
  simp [bilinearTensorCharacterPrefixSquare]

private lemma prefix_square_le_card_mul_row_prefix_max
    (A : ℕ → ℤ → ℂ) (DS : Finset ℕ) (M y q : ℕ)
    (hy : y ≤ M) (χ : PrimitiveCharacter q) :
    bilinearTensorCharacterPrefixSquare A DS y q χ ≤
      (DS.card : ℝ) * ∑ d ∈ DS,
        primitiveCharacterPrefixMaxSquare (A d) 0 M q χ := by
  let R : ℕ → ℂ := fun d =>
    ∑ t ∈ Finset.Icc (1 : ℤ) y, A d t * χ.1 (t : ZMod q)
  have hform :
      (∑ d ∈ DS, ∑ t ∈ Finset.Icc (1 : ℤ) y,
        A d t * χ.1 ((d : ℤ) * t : ZMod q)) =
        ∑ d ∈ DS, χ.1 (d : ZMod q) * R d := by
    apply Finset.sum_congr rfl
    intro d hd
    dsimp [R]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t ht
    rw [map_mul]
    norm_cast
    ring
  unfold bilinearTensorCharacterPrefixSquare
  rw [hform]
  calc
    ‖∑ d ∈ DS, χ.1 (d : ZMod q) * R d‖ ^ 2
        ≤ (∑ d ∈ DS, ‖R d‖) ^ 2 := by
      apply pow_le_pow_left₀ (norm_nonneg _)
      exact norm_sum_le_of_le _ fun d _ => by
        rw [norm_mul]
        exact mul_le_of_le_one_left (norm_nonneg _)
          (DirichletCharacter.norm_le_one χ.1 (d : ZMod q))
    _ ≤ (DS.card : ℝ) * ∑ d ∈ DS, ‖R d‖ ^ 2 := by
      simpa using Finset.sum_mul_sq_le_sq_mul_sq DS
        (fun _d => (1 : ℝ)) (fun d => ‖R d‖)
    _ ≤ (DS.card : ℝ) * ∑ d ∈ DS,
        primitiveCharacterPrefixMaxSquare (A d) 0 M q χ := by
      gcongr with d hd
      simpa [R, primitiveCharacterPrefixSquare] using
        primitiveCharacterPrefixSquare_le_max (A d) 0 hy χ

/-- Every complete bilinear prefix maximum is bounded by outer-row Cauchy and
the sum of the complete row-prefix maxima. -/
theorem bilinearTensorCharacterPrefixMaxSquare_le_rows
    (A : ℕ → ℤ → ℂ) (DS : Finset ℕ) (M q : ℕ)
    (χ : PrimitiveCharacter q) :
    bilinearTensorCharacterPrefixMaxSquare A DS M q χ ≤
      (DS.card : ℝ) * ∑ d ∈ DS,
        primitiveCharacterPrefixMaxSquare (A d) 0 M q χ := by
  unfold bilinearTensorCharacterPrefixMaxSquare
  apply Finset.max'_le
  intro x hx
  rcases Finset.mem_image.mp hx with ⟨y, hy, rfl⟩
  exact prefix_square_le_card_mul_row_prefix_max A DS M y q
    (by simpa [Finset.mem_range] using hy) χ

-- The same nonnegative rowwise scale occurs in each energy comparison below.
private lemma prefix_rowwise_scale_nonneg (M Q : ℕ) :
    0 ≤ (M : ℝ) + primitiveBilinearQFactor Q * (Q : ℝ) ^ 2 :=
  add_nonneg (Nat.cast_nonneg M)
    (mul_nonneg (primitiveBilinearQFactor_nonneg Q) (sq_nonneg _))

/-- Generic explicit `t`-prefix-maximal bilinear tensor theorem.  The aligned
dyadic decomposition is applied to each row and costs exactly
`(log₂ M + 1)^2`; the remaining factor is the already proved Q-dependent
nonmaximal constant `D * (M + c(Q)Q^2)`. -/
theorem weighted_primitive_bilinearTensor_prefixMax_explicit
    (A : ℕ → ℤ → ℂ) (DS : Finset ℕ) (D M Q : ℕ)
    (hQ : 0 < Q) (hcard : DS.card ≤ D) :
    (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
      ∑ χ : PrimitiveCharacter q,
        bilinearTensorCharacterPrefixMaxSquare A DS M q χ) ≤
      (((Nat.log2 M + 1 : ℕ) : ℝ) ^ 2) *
      (D : ℝ) * ((M : ℝ) + primitiveBilinearQFactor Q * (Q : ℝ) ^ 2) *
        bilinearTensorCoeffEnergy A DS M := by
  let P : ℕ → (q : ℕ) → PrimitiveCharacter q → ℝ := fun d q χ =>
    primitiveCharacterPrefixMaxSquare (A d) 0 M q χ
  have hpoint : ∀ q, ∀ χ : PrimitiveCharacter q,
      bilinearTensorCharacterPrefixMaxSquare A DS M q χ ≤
        (DS.card : ℝ) * ∑ d ∈ DS, P d q χ := by
    intro q χ
    simpa [P] using bilinearTensorCharacterPrefixMaxSquare_le_rows A DS M q χ
  have htranspose :
      (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ : PrimitiveCharacter q,
          bilinearTensorCharacterPrefixMaxSquare A DS M q χ) ≤
        (DS.card : ℝ) * ∑ d ∈ DS,
          (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
            ∑ χ : PrimitiveCharacter q, P d q χ) := by
    calc
      _ ≤ ∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
          (∑ χ : PrimitiveCharacter q,
            (DS.card : ℝ) * ∑ d ∈ DS, P d q χ) := by
        apply Finset.sum_le_sum
        intro q hq
        apply mul_le_mul_of_nonneg_left
        · exact Finset.sum_le_sum fun χ _ => hpoint q χ
        · positivity
      _ = _ := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro q hq
        rw [Finset.sum_comm]
        simp only [mul_left_comm]
  refine htranspose.trans ?_
  have hrow : ∀ d ∈ DS,
      (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ : PrimitiveCharacter q, P d q χ) ≤
        (((Nat.log2 M + 1 : ℕ) : ℝ) ^ 2) *
        ((M : ℝ) + primitiveBilinearQFactor Q * (Q : ℝ) ^ 2) *
          ∑ t ∈ Finset.Icc (1 : ℤ) M, ‖A d t‖ ^ 2 := by
    intro d hd
    simpa [P, primitiveLargeSieveConstant, primitiveBilinearQFactor] using
      weighted_primitive_prefix_maximal (A d) 0 M Q hQ
  have hcardR : (DS.card : ℝ) ≤ (D : ℝ) := by exact_mod_cast hcard
  calc
    (DS.card : ℝ) * ∑ d ∈ DS,
        (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
          ∑ χ : PrimitiveCharacter q, P d q χ)
      ≤ (DS.card : ℝ) * ∑ d ∈ DS,
          ((((Nat.log2 M + 1 : ℕ) : ℝ) ^ 2) *
          ((M : ℝ) + primitiveBilinearQFactor Q * (Q : ℝ) ^ 2) *
            ∑ t ∈ Finset.Icc (1 : ℤ) M, ‖A d t‖ ^ 2) := by
        gcongr with d hd
        exact hrow d hd
    _ ≤ (D : ℝ) * ∑ d ∈ DS,
          ((((Nat.log2 M + 1 : ℕ) : ℝ) ^ 2) *
          ((M : ℝ) + primitiveBilinearQFactor Q * (Q : ℝ) ^ 2) *
            ∑ t ∈ Finset.Icc (1 : ℤ) M, ‖A d t‖ ^ 2) := by
        gcongr
        exact Finset.sum_nonneg fun d _ => mul_nonneg
          (mul_nonneg (sq_nonneg _) (prefix_rowwise_scale_nonneg M Q))
          (Finset.sum_nonneg fun t _ => sq_nonneg _)
    _ = _ := by
      unfold bilinearTensorCoeffEnergy
      simp_rw [Finset.mul_sum]
      ring

/-- The canonical Vaughan Type-II block with the complete collected-variable
prefix maximum, at the physical short length `y / 2^k`. -/
def vaughanCanonicalBilinearPrefixMaxSquare
    (b : ℕ → ℂ) (y N u v k l q : ℕ) (χ : PrimitiveCharacter q) : ℝ :=
  bilinearTensorCharacterPrefixMaxSquare
    (vaughanCanonicalBilinearTensor b y N v l)
    (vaughanCanonicalDyadicBlock N u k)
    (vaughanCanonicalTensorLength y k) q χ

/-- Canonical complete-prefix theorem, with no fourth-moment premise. -/
theorem weighted_primitive_vaughanCanonicalBilinear_prefixMax_unconditional
    (b : ℕ → ℂ) (y N u v k l Q : ℕ) (hQ : 0 < Q) :
    (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
      ∑ χ : PrimitiveCharacter q,
        vaughanCanonicalBilinearPrefixMaxSquare b y N u v k l q χ) ≤
      (((Nat.log2 (vaughanCanonicalTensorLength y k) + 1 : ℕ) : ℝ) ^ 2) *
      ((2 ^ k : ℕ) : ℝ) *
      ((vaughanCanonicalTensorLength y k : ℕ) +
        primitiveBilinearQFactor Q * (Q : ℝ) ^ 2) *
      vaughanCanonicalShortTensorEnergy vaughanMangoldtCoeff b
        y N u v k l := by
  unfold vaughanCanonicalBilinearPrefixMaxSquare
  refine (weighted_primitive_bilinearTensor_prefixMax_explicit
    (vaughanCanonicalBilinearTensor b y N v l)
    (vaughanCanonicalDyadicBlock N u k) (2 ^ k)
    (vaughanCanonicalTensorLength y k) Q hQ
    (card_vaughanCanonicalDyadicBlock_le_pow N u k)).trans ?_
  apply mul_le_mul_of_nonneg_left
  · exact vaughanCanonicalBilinearTensor_coeffEnergy_le b y N u v k l
  · exact mul_nonneg
      (mul_nonneg (sq_nonneg _) (by positivity))
      (prefix_rowwise_scale_nonneg (vaughanCanonicalTensorLength y k) Q)

/-- Linear-harmonic imprimitive conductor-window transport for the complete
canonical bilinear prefix maximum. -/
theorem imprimitive_conductor_window_vaughanCanonicalBilinear_prefixMax
    (b : ℕ → ℂ) (y N Q C u v k l : ℕ) (hC : 0 < C) :
    (∑ d ∈ Finset.Icc C (2 * C), imprimitiveConductorWeight Q d *
      ∑ ψ : PrimitiveCharacter d,
        vaughanCanonicalBilinearPrefixMaxSquare b y N u v k l d ψ) ≤
      ((Q / C : ℕ) : ℝ) * conductorHarmonicFactor (Q / C) *
      ((((Nat.log2 (vaughanCanonicalTensorLength y k) + 1 : ℕ) : ℝ) ^ 2) *
      ((2 ^ k : ℕ) : ℝ) *
      ((vaughanCanonicalTensorLength y k : ℕ) +
        primitiveBilinearQFactor (2 * C) * ((2 * C : ℕ) : ℝ) ^ 2) *
      vaughanCanonicalShortTensorEnergy vaughanMangoldtCoeff b
        y N u v k l) := by
  let F : (d : ℕ) → PrimitiveCharacter d → ℝ := fun d ψ =>
    vaughanCanonicalBilinearPrefixMaxSquare b y N u v k l d ψ
  have hF : ∀ d ψ, 0 ≤ F d ψ := by
    intro d ψ
    exact bilinearTensorCharacterPrefixMaxSquare_nonneg _ _ _ _ _
  refine (imprimitive_conductor_window_family_le_linear_typeII F hF Q C hC).trans ?_
  apply mul_le_mul_of_nonneg_left
  · simpa [F] using weighted_primitive_vaughanCanonicalBilinear_prefixMax_unconditional
      b y N u v k l (2 * C) (Nat.mul_pos (by decide) hC)
  · exact mul_nonneg (by positivity) (conductorHarmonicFactor_nonneg _)

/-- Substitution of the explicit divisor-square constant `27`.  This theorem
makes the remaining full row-mass factor visible. -/
theorem weighted_primitive_vaughanCanonicalBilinear_prefixMax_energy27
    (b : ℕ → ℂ) (y N u v k l Q : ℕ) (B : ℝ)
    (hQ : 0 < Q) (hB : ∀ n ≤ y, ‖b n‖ ≤ B) :
    (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
      ∑ χ : PrimitiveCharacter q,
        vaughanCanonicalBilinearPrefixMaxSquare b y N u v k l q χ) ≤
      (((Nat.log2 (vaughanCanonicalTensorLength y k) + 1 : ℕ) : ℝ) ^ 2) *
      ((2 ^ k : ℕ) : ℝ) *
      ((vaughanCanonicalTensorLength y k : ℕ) +
        primitiveBilinearQFactor Q * (Q : ℝ) ^ 2) *
      (27 * B ^ 2 * (((2 ^ k : ℕ) : ℝ) *
        vaughanCanonicalTensorLength y k) * Real.log (y + 1 : ℕ) ^ 5) := by
  refine (weighted_primitive_vaughanCanonicalBilinear_prefixMax_unconditional
    b y N u v k l Q hQ).trans ?_
  apply mul_le_mul_of_nonneg_left
  · exact vaughanCanonicalShortTensorEnergy_le_shellScale
      b y N u v k l B 27 hB divisorSquareMomentBound_27 (by norm_num)
  · exact mul_nonneg
      (mul_nonneg (sq_nonneg _) (by positivity))
      (prefix_rowwise_scale_nonneg (vaughanCanonicalTensorLength y k) Q)

/-- Algebraic audit: after writing `X=D*M`, the prefix maximal route with the
`27`-energy still contains `X * (X + D*Q^2)`.  Thus the dyadic maximal upgrade
does not itself supply the missing `N/log` saving needed by a BV endpoint. -/
theorem bilinear_prefix_energy27_scale_audit
    (D M Q L : ℝ) :
    D * (M + Q ^ 2) * (27 * (D * M) * L) =
      27 * (D * M) * (D * M + D * Q ^ 2) * L := by
  ring

end

end AnalyticNumberTheory.LargeSieve
