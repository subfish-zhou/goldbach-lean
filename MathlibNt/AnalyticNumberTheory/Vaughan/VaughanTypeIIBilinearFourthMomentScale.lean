

import MathlibNt.AnalyticNumberTheory.Vaughan.VaughanTypeIICanonicalShortLength

/-!
 # Canonical Type-II shell scale and the bilinear fourth-moment frontier

This module makes two logically separate points precise.

* On a `d`-shell of cardinality/size `D` and collected length `M`, the actual
  short tensor energy has scale `D*M` (up to the divisor-square logarithms).
  The `e`-shell contributes no further polynomial factor: its divisors are
  already absorbed by the divisor-square moment.
* Substitution into the existing rowwise short-length large sieve still leaves
  an extra factor equal to that row mass.  We therefore freeze a generic
  bilinear tensor fourth-moment inequality, not a Bombieri--Vinogradov
  conclusion, and prove that it is exactly sufficient for a per-rectangle
  bound with scale `(D+Q^2)(M+Q^2)`.
-/

namespace AnalyticNumberTheory.LargeSieve

open Classical Finset
open scoped BigOperators ArithmeticFunction

noncomputable section

/-- Polynomial scale of a genuine two-variable multiplicative large sieve. -/
def bilinearMultiplicativeScale (D M Q : ℕ) : ℝ :=
  (D : ℝ) * M + (Q : ℝ) ^ 2 * ((D : ℝ) + M) + (Q : ℝ) ^ 4

/-- The scale is the product of the two one-variable large-sieve scales. -/
theorem bilinearMultiplicativeScale_eq (D M Q : ℕ) :
    bilinearMultiplicativeScale D M Q =
      ((D : ℝ) + (Q : ℝ) ^ 2) * ((M : ℝ) + (Q : ℝ) ^ 2) := by
  unfold bilinearMultiplicativeScale
  ring

lemma bilinearMultiplicativeScale_nonneg (D M Q : ℕ) :
    0 ≤ bilinearMultiplicativeScale D M Q := by
  rw [bilinearMultiplicativeScale_eq]
  positivity

/-- A generic character form with genuinely two-dimensional coefficients.
The row coefficients may depend on `d`; no rank-one/separability assumption is
hidden in the interface. -/
def bilinearTensorCharacterForm
    (A : ℕ → ℤ → ℂ) (DS : Finset ℕ) (M q : ℕ)
    (χ : PrimitiveCharacter q) : ℂ :=
  ∑ d ∈ DS, ∑ t ∈ Finset.Icc (1 : ℤ) M,
    A d t * χ.1 (d : ZMod q) * χ.1 (t : ZMod q)

/-- Frobenius coefficient energy of the generic bilinear tensor. -/
def bilinearTensorCoeffEnergy
    (A : ℕ → ℤ → ℂ) (DS : Finset ℕ) (M : ℕ) : ℝ :=
  ∑ d ∈ DS, ∑ t ∈ Finset.Icc (1 : ℤ) M, ‖A d t‖ ^ 2

/-- Minimal analytic frontier: a weighted primitive-character fourth-moment
bound for an arbitrary bilinear tensor.  It is deliberately generic and
per-rectangle; it mentions neither Vaughan coefficients nor a final BV error.
For rank-one `A d t = a d * b t`, its left side is the mixed fourth moment
`sum |sum a_d χ(d)|^2 |sum b_t χ(t)|^2`. -/
def BilinearTensorFourthMomentBound (K : ℝ) : Prop :=
  ∀ (A : ℕ → ℤ → ℂ) (DS : Finset ℕ) (D M Q : ℕ), DS.card ≤ D →
    (∀ d ∈ DS, d < 2 * D) →
    (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
      ∑ χ : PrimitiveCharacter q,
        ‖bilinearTensorCharacterForm A DS M q χ‖ ^ 2) ≤
      K * bilinearMultiplicativeScale D M Q *
        bilinearTensorCoeffEnergy A DS M

/-- The canonical short tensor, including the outer Möbius coefficient. -/
def vaughanCanonicalBilinearTensor
    (b : ℕ → ℂ) (y N v l : ℕ) : ℕ → ℤ → ℂ :=
  fun d t => vaughanMoebiusCoeff d *
    vaughanBilinearTensorCoeff vaughanMangoldtCoeff b y d
      (vaughanCanonicalDyadicBlock N v l) t

lemma vaughanCanonicalBilinearBlock_eq_shortTensorForm
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

lemma vaughanCanonicalBilinearTensor_energy_le
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
  have hμ : ‖vaughanMoebiusCoeff d‖ ^ 2 ≤ (1 : ℝ) := by
    rcases ArithmeticFunction.moebius_eq_or d with h | h | h <;>
      simp [vaughanMoebiusCoeff, h]
  apply Finset.sum_le_sum
  intro t ht
  rw [norm_mul, mul_pow]
  simpa using mul_le_mul_of_nonneg_right hμ
    (sq_nonneg ‖vaughanBilinearTensorCoeff vaughanMangoldtCoeff b y d
      (vaughanCanonicalDyadicBlock N v l) t‖)

/-- The frozen generic fourth moment is sufficient for the actual canonical
Vaughan rectangle.  This is only a per-shell second-moment consumer, not a BV
conclusion. -/
theorem weighted_primitive_vaughanCanonicalBilinear_of_fourthMoment
    (K : ℝ) (hK : 0 ≤ K) (hFourth : BilinearTensorFourthMomentBound K)
    (b : ℕ → ℂ) (y N u v k l Q : ℕ) :
    (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
      ∑ χ : PrimitiveCharacter q,
        ‖vaughanTypeIICanonicalBilinearBlock b y N u v k l q χ‖ ^ 2) ≤
      K * bilinearMultiplicativeScale (2 ^ k) (vaughanCanonicalTensorLength y k) Q *
        vaughanCanonicalShortTensorEnergy vaughanMangoldtCoeff b
          y N u v k l := by
  simp_rw [vaughanCanonicalBilinearBlock_eq_shortTensorForm]
  refine (hFourth (vaughanCanonicalBilinearTensor b y N v l)
    (vaughanCanonicalDyadicBlock N u k) (2 ^ k)
    (vaughanCanonicalTensorLength y k) Q
    (card_vaughanCanonicalDyadicBlock_le_pow N u k) ?_).trans ?_
  · intro d hd
    simpa [Nat.pow_succ, Nat.mul_comm] using
      (vaughanCanonicalDyadicBlock_pow_bounds hd).2
  exact mul_le_mul_of_nonneg_left
    (vaughanCanonicalBilinearTensor_energy_le b y N u v k l)
    (mul_nonneg hK (bilinearMultiplicativeScale_nonneg _ _ _))

private lemma mem_vaughanTensorFiber_iff_local
    (y d e : ℕ) (ES : Finset ℕ) (t : ℤ) :
    e ∈ vaughanTensorFiber y d ES t ↔
      e ∈ ES ∧ ∃ m ∈ Finset.Icc 1 (y / (d * e)), ((e * m : ℕ) : ℤ) = t := by
  simp only [vaughanTensorFiber, Finset.mem_filter]

/-- An `e`-shell whose lower endpoint exceeds the collected length is literally
inactive: no product `e*m=t` with `m≥1` can occur. -/
lemma vaughanBilinearTensorCoeff_eq_zero_of_eShell_above_length
    (b : ℕ → ℂ) (y N v k l d : ℕ) (t : ℤ)
    (ht : t ∈ Finset.Icc (1 : ℤ) (vaughanCanonicalTensorLength y k))
    (hEM : vaughanCanonicalTensorLength y k < 2 ^ l) :
    vaughanBilinearTensorCoeff vaughanMangoldtCoeff b y d
      (vaughanCanonicalDyadicBlock N v l) t = 0 := by
  rw [vaughanBilinearTensorCoeff_eq_fiber b y d _ t
    (fun e he => (mem_vaughanCanonicalDyadicBlock.mp he).1)]
  apply Finset.sum_eq_zero
  intro e he
  obtain ⟨heShell, m, hm, hem⟩ :=
    (mem_vaughanTensorFiber_iff_local y d e
      (vaughanCanonicalDyadicBlock N v l) t).mp he
  have helower : 2 ^ l ≤ e :=
    (vaughanCanonicalDyadicBlock_pow_bounds heShell).1
  have hmpos : 0 < m := (Finset.mem_Icc.mp hm).1
  have hproduct : e * m ≤ vaughanCanonicalTensorLength y k := by
    exact_mod_cast hem.trans_le (Finset.mem_Icc.mp ht).2
  -- Every fiber product is at least the shell base, but at most the short length.
  have hshell : 2 ^ l ≤ vaughanCanonicalTensorLength y k :=
    helower.trans ((Nat.le_mul_of_pos_right e hmpos).trans hproduct)
  exact (not_le_of_gt hEM hshell).elim

/-- Precise `e`-shell dichotomy: above `M` the short tensor energy is zero;
on active shells the polynomial bound below is independent of `E=2^l`. -/
theorem vaughanCanonicalShortTensorEnergy_eq_zero_of_eShell_above_length
    (b : ℕ → ℂ) (y N u v k l : ℕ)
    (hEM : vaughanCanonicalTensorLength y k < 2 ^ l) :
    vaughanCanonicalShortTensorEnergy vaughanMangoldtCoeff b
      y N u v k l = 0 := by
  unfold vaughanCanonicalShortTensorEnergy
  apply Finset.sum_eq_zero
  intro d hd
  apply Finset.sum_eq_zero
  intro t ht
  rw [vaughanBilinearTensorCoeff_eq_zero_of_eShell_above_length
    b y N v k l d t ht hEM]
  norm_num

/-- Exact `d`-shell quotient-mass bound before using `D*M ≤ y`. -/
theorem vaughanQuotientMass_canonical_le_pow_mul_length
    (y N u k : ℕ) :
    vaughanQuotientMass y (vaughanCanonicalDyadicBlock N u k) ≤
      ((2 ^ k : ℕ) : ℝ) * vaughanCanonicalTensorLength y k := by
  unfold vaughanQuotientMass vaughanCanonicalTensorLength
  calc
    (∑ d ∈ vaughanCanonicalDyadicBlock N u k, ((y / d : ℕ) : ℝ)) ≤
        ∑ _d ∈ vaughanCanonicalDyadicBlock N u k,
          ((y / 2 ^ k : ℕ) : ℝ) := by
      apply Finset.sum_le_sum
      intro d hd
      exact_mod_cast Nat.div_le_div_left
        (vaughanCanonicalDyadicBlock_pow_bounds hd).1 (by positivity : 0 < 2 ^ k)
    _ = ((vaughanCanonicalDyadicBlock N u k).card : ℝ) *
        (y / 2 ^ k : ℕ) := by simp
    _ ≤ ((2 ^ k : ℕ) : ℝ) * (y / 2 ^ k : ℕ) := by
      gcongr
      exact_mod_cast card_vaughanCanonicalDyadicBlock_le_pow N u k

/-- True canonical short-tensor scale.  `l` (and hence the `e`-shell size) is
present but contributes no polynomial factor.  The divisor-square moment has
already paid for all collisions `e*m=t`. -/
theorem vaughanCanonicalShortTensorEnergy_le_shellScale
    (b : ℕ → ℂ) (y N u v k l : ℕ) (B C : ℝ)
    (hB : ∀ n ≤ y, ‖b n‖ ≤ B)
    (hMoment : DivisorSquareMomentBound C) (hC : 0 ≤ C) :
    vaughanCanonicalShortTensorEnergy vaughanMangoldtCoeff b
        y N u v k l ≤
      C * B ^ 2 * (((2 ^ k : ℕ) : ℝ) * vaughanCanonicalTensorLength y k) *
        Real.log (y + 1 : ℕ) ^ 5 := by
  rw [← vaughanBilinearTensorEnergy_canonical_eq_short]
  refine (vaughanBilinearTensorEnergy_le_actual b y _ _
    (fun e he => (mem_vaughanCanonicalDyadicBlock.mp he).1)).trans ?_
  refine (vaughanActualTensorCoeffEnergy_le_of_divisorSquareMoment b y
    (vaughanCanonicalDyadicBlock N u k)
    (vaughanCanonicalDyadicBlock N v l) B C
    (fun d hd => (mem_vaughanCanonicalDyadicBlock.mp hd).1)
    (fun e he => (mem_vaughanCanonicalDyadicBlock.mp he).1)
    hB hMoment hC).trans ?_
  have hfac : 0 ≤ C * B ^ 2 * Real.log (y + 1 : ℕ) ^ 5 := by positivity
  calc
    C * B ^ 2 * Real.log (y + 1 : ℕ) ^ 5 *
        vaughanQuotientMass y (vaughanCanonicalDyadicBlock N u k) ≤
      C * B ^ 2 * Real.log (y + 1 : ℕ) ^ 5 *
        (((2 ^ k : ℕ) : ℝ) * vaughanCanonicalTensorLength y k) :=
      mul_le_mul_of_nonneg_left
        (vaughanQuotientMass_canonical_le_pow_mul_length y N u k) hfac
    _ = _ := by ring

/-- Abstract scale of the currently proved rowwise short-length route. -/
def rowwiseShortTypeIIScale (D M Q energy : ℝ) : ℝ :=
  D * (M + Q ^ 2) * energy

/-- Substituting the true shell energy `C*D*M*L` into the rowwise route leaves
one complete row-mass factor `D*M`. -/
theorem rowwiseShortTypeIIScale_after_shellEnergy
    {D M Q energy C L : ℝ}
    (hD : 0 ≤ D) (hM : 0 ≤ M)
    (henergy : energy ≤ C * (D * M) * L) :
    rowwiseShortTypeIIScale D M Q energy ≤
      C * (D * M) * (D * (M + Q ^ 2)) * L := by
  unfold rowwiseShortTypeIIScale
  calc
    D * (M + Q ^ 2) * energy ≤
        D * (M + Q ^ 2) * (C * (D * M) * L) := by
      exact mul_le_mul_of_nonneg_left henergy
        (mul_nonneg hD (add_nonneg hM (sq_nonneg Q)))
    _ = C * (D * M) * (D * (M + Q ^ 2)) * L := by ring

/-- With `N=D*M`, the preceding scale is `C*N*(N+D*Q^2)*L`; it is not
`(N+Q^2(D+M)+Q^4)*polylog` by itself. -/
theorem rowwiseShortTypeIIScale_as_N
    {N D M Q C L : ℝ} (hN : N = D * M) :
    C * (D * M) * (D * (M + Q ^ 2)) * L =
      C * N * (N + D * Q ^ 2) * L := by
  rw [hN]
  ring

/-- The desired bilinear coefficient is exactly
`N + Q^2(D+M) + Q^4` when `N=D*M`. -/
theorem bilinearMultiplicativeScale_as_N
    (N D M Q : ℕ) (hN : N = D * M) :
    bilinearMultiplicativeScale D M Q =
      (N : ℝ) + (Q : ℝ) ^ 2 * ((D : ℝ) + M) + (Q : ℝ) ^ 4 := by
  unfold bilinearMultiplicativeScale
  subst N
  push_cast
  rfl

end

end AnalyticNumberTheory.LargeSieve
