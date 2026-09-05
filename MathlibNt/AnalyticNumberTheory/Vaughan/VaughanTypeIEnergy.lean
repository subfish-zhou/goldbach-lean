

import MathlibNt.AnalyticNumberTheory.Vaughan.VaughanPrefixReduction

/-!
 # Structured Type-I coefficient energy for Vaughan's identity

This module opens the two divisor/convolution sums inside `vaughanTypeICoeff`.
The resulting finite majorant records the outer truncated-divisor multiplicity,
the logarithmic first convolution, and the complete inner truncated-divisor
multiplicity of the middle convolution.  Thus the Type-I lane is not discharged
by treating `vaughanTypeICoeff` as an opaque sequence.
-/

namespace AnalyticNumberTheory.LargeSieve

open Classical Finset
open scoped BigOperators ArithmeticFunction

noncomputable section

/-- Cauchy--Schwarz for a finite real sum, in the cardinality form used for
both divisor layers below. -/
private theorem sum_sq_le_card_mul_sum_sq {α : Type*} (s : Finset α)
    (f : α → ℝ) :
    (∑ a ∈ s, f a) ^ 2 ≤ (s.card : ℝ) * ∑ a ∈ s, (f a) ^ 2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq s (fun _ => (1 : ℝ)) f
  simpa using h

/-- The explicit Cauchy energy of the truncated `μ * log` convolution. -/
def vaughanFirstDivisorEnergy (n u : ℕ) : ℝ :=
  ((n.divisors.filter fun d => d ≤ u).card : ℝ) *
    ∑ d ∈ n.divisors.filter (fun d => d ≤ u),
      (((ArithmeticFunction.moebius d : ℤ) : ℝ) *
        Real.log ((n / d : ℕ) : ℝ)) ^ 2

/-- The explicit nested Cauchy energy of the truncated `μ * Λ` convolution.
The inner divisor cardinality is retained separately for every outer divisor. -/
def vaughanMiddleDivisorEnergy (n u v : ℕ) : ℝ :=
  ((n.divisors.filter fun d => d ≤ u).card : ℝ) *
    ∑ d ∈ n.divisors.filter (fun d => d ≤ u),
      (((n / d).divisors.filter fun e => e ≤ v).card : ℝ) *
        ∑ e ∈ (n / d).divisors.filter (fun e => e ≤ v),
          (((ArithmeticFunction.moebius d : ℤ) : ℝ) *
            ArithmeticFunction.vonMangoldt e) ^ 2

/-- The pointwise structured Type-I budget.  The factor `2` is exactly the
loss in `(A-B)^2 ≤ 2(A^2+B^2)`. -/
def vaughanTypeIStructuredEnergy (n u v : ℕ) : ℝ :=
  2 * (vaughanFirstDivisorEnergy n u + vaughanMiddleDivisorEnergy n u v)

lemma vaughanFirst_sq_le_divisorEnergy (n u : ℕ) :
    Sieve.vaughanFirst n u ^ 2 ≤ vaughanFirstDivisorEnergy n u := by
  unfold Sieve.vaughanFirst vaughanFirstDivisorEnergy
  exact sum_sq_le_card_mul_sum_sq _ _

lemma vaughanMiddle_sq_le_divisorEnergy (n u v : ℕ) :
    Sieve.vaughanMiddle n u v ^ 2 ≤ vaughanMiddleDivisorEnergy n u v := by
  unfold Sieve.vaughanMiddle vaughanMiddleDivisorEnergy
  let D := n.divisors.filter (fun d => d ≤ u)
  let E : ℕ → Finset ℕ := fun d => (n / d).divisors.filter (fun e => e ≤ v)
  let c : ℕ → ℕ → ℝ := fun d e =>
    ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
      ArithmeticFunction.vonMangoldt e
  calc
    (∑ d ∈ D, ∑ e ∈ E d, c d e) ^ 2
        ≤ (D.card : ℝ) * ∑ d ∈ D, (∑ e ∈ E d, c d e) ^ 2 :=
      sum_sq_le_card_mul_sum_sq D (fun d => ∑ e ∈ E d, c d e)
    _ ≤ (D.card : ℝ) *
        ∑ d ∈ D, ((E d).card : ℝ) * ∑ e ∈ E d, (c d e) ^ 2 := by
      gcongr with d hd
      exact sum_sq_le_card_mul_sum_sq (E d) (c d)

/-- Genuine Type-I pointwise estimate, obtained by expanding both divisor
convolutions rather than applying a norm estimate to the already-packaged
coefficient. -/
theorem vaughanTypeI_sq_le_structuredEnergy (n u v : ℕ) :
    vaughanTypeI n u v ^ 2 ≤ vaughanTypeIStructuredEnergy n u v := by
  rw [vaughanTypeI, vaughanTypeIStructuredEnergy]
  have hfirst := vaughanFirst_sq_le_divisorEnergy n u
  have hmiddle := vaughanMiddle_sq_le_divisorEnergy n u v
  nlinarith [sq_nonneg (Sieve.vaughanFirst n u + Sieve.vaughanMiddle n u v)]

lemma vaughanTypeIStructuredEnergy_nonneg (n u v : ℕ) :
    0 ≤ vaughanTypeIStructuredEnergy n u v := by
  unfold vaughanTypeIStructuredEnergy vaughanFirstDivisorEnergy
    vaughanMiddleDivisorEnergy
  positivity

private lemma card_filter_le_succ (s : Finset ℕ) (k : ℕ) :
    (s.filter fun x => x ≤ k).card ≤ k + 1 := by
  calc
    (s.filter fun x => x ≤ k).card ≤ (Finset.range (k + 1)).card := by
      apply Finset.card_le_card
      intro x hx
      rw [Finset.mem_filter] at hx
      rw [Finset.mem_range]
      omega
    _ = k + 1 := Finset.card_range _

/-- A coarser version of the structured energy in which the two truncated
cardinalities are replaced by the literal cutoff factors `u+1` and `v+1`.
The divisor sums themselves (and hence every logarithmic/Λ factor) remain
visible. -/
def vaughanTypeICutoffEnergy (n u v : ℕ) : ℝ :=
  2 * (((u + 1 : ℕ) : ℝ) *
      ∑ d ∈ n.divisors.filter (fun d => d ≤ u),
        (((ArithmeticFunction.moebius d : ℤ) : ℝ) *
          Real.log ((n / d : ℕ) : ℝ)) ^ 2 +
    ((u + 1 : ℕ) : ℝ) *
      ∑ d ∈ n.divisors.filter (fun d => d ≤ u),
        ((v + 1 : ℕ) : ℝ) *
          ∑ e ∈ (n / d).divisors.filter (fun e => e ≤ v),
            (((ArithmeticFunction.moebius d : ℤ) : ℝ) *
              ArithmeticFunction.vonMangoldt e) ^ 2)

lemma vaughanTypeIStructuredEnergy_le_cutoffEnergy (n u v : ℕ) :
    vaughanTypeIStructuredEnergy n u v ≤ vaughanTypeICutoffEnergy n u v := by
  unfold vaughanTypeIStructuredEnergy vaughanFirstDivisorEnergy
    vaughanMiddleDivisorEnergy vaughanTypeICutoffEnergy
  have hDnat := card_filter_le_succ n.divisors u
  have hD : ((n.divisors.filter fun d => d ≤ u).card : ℝ) ≤ (u + 1 : ℕ) := by
    exact_mod_cast hDnat
  gcongr with d hd
  have hEnat := card_filter_le_succ (n / d).divisors v
  exact_mod_cast hEnat

lemma vaughanTypeICutoffEnergy_nonneg (n u v : ℕ) :
    0 ≤ vaughanTypeICutoffEnergy n u v := by
  unfold vaughanTypeICutoffEnergy
  positivity

/-- Pointwise coefficient-energy estimate with the scalar weight `b` left
visible. -/
theorem vaughanTypeICoeff_norm_sq_le (b : ℤ → ℂ) (u v : ℕ) (n : ℤ) :
    ‖vaughanTypeICoeff b u v n‖ ^ 2 ≤
      ‖b n‖ ^ 2 * vaughanTypeIStructuredEnergy n.toNat u v := by
  rw [vaughanTypeICoeff, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    mul_pow]
  have h := vaughanTypeI_sq_le_structuredEnergy n.toNat u v
  have hb : 0 ≤ ‖b n‖ ^ 2 := sq_nonneg _
  have hr : |vaughanTypeI n.toNat u v| ^ 2 =
      vaughanTypeI n.toNat u v ^ 2 := sq_abs _
  rw [hr]
  exact mul_le_mul_of_nonneg_left h hb

/-- Pointwise version with the literal cutoff factors `u+1` and `v+1`. -/
theorem vaughanTypeICoeff_norm_sq_le_cutoff (b : ℤ → ℂ) (u v : ℕ) (n : ℤ) :
    ‖vaughanTypeICoeff b u v n‖ ^ 2 ≤
      ‖b n‖ ^ 2 * vaughanTypeICutoffEnergy n.toNat u v := by
  refine (vaughanTypeICoeff_norm_sq_le b u v n).trans ?_
  exact mul_le_mul_of_nonneg_left
    (vaughanTypeIStructuredEnergy_le_cutoffEnergy n.toNat u v) (sq_nonneg _)

/-- The finite `ℓ²` Type-I coefficient energy on `[1,N]`, with `N`, both
cutoffs, all logarithms, and both divisor multiplicities explicit. -/
theorem vaughanTypeICoeff_energy_le (b : ℤ → ℂ) (N u v : ℕ) :
    (∑ n ∈ Finset.Icc (1 : ℤ) N, ‖vaughanTypeICoeff b u v n‖ ^ 2) ≤
      ∑ n ∈ Finset.Icc (1 : ℤ) N,
        ‖b n‖ ^ 2 * vaughanTypeIStructuredEnergy n.toNat u v := by
  exact Finset.sum_le_sum fun n _ => vaughanTypeICoeff_norm_sq_le b u v n

/-- Fully explicit cutoff-factor form of the finite Type-I energy bound. -/
theorem vaughanTypeICoeff_energy_le_cutoff (b : ℤ → ℂ) (N u v : ℕ) :
    (∑ n ∈ Finset.Icc (1 : ℤ) N, ‖vaughanTypeICoeff b u v n‖ ^ 2) ≤
      ∑ n ∈ Finset.Icc (1 : ℤ) N,
        ‖b n‖ ^ 2 * vaughanTypeICutoffEnergy n.toNat u v := by
  exact Finset.sum_le_sum fun n _ => vaughanTypeICoeff_norm_sq_le_cutoff b u v n

/-- The weighted prefix large-sieve ledger with the Type-I lane replaced by
its genuine divisor/convolution energy.  The Type-II and small lanes remain
visible as the next independent fronts. -/
theorem weighted_vaughan_prefix_large_sieve_typeI_ledger
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
            ‖vaughanTypeIICoeff b u v n‖ ^ 2) +
          (∑ n ∈ Finset.Icc (1 : ℤ) N,
            ‖vaughanSmallCoeff b v n‖ ^ 2)) := by
  refine (weighted_vaughan_prefix_large_sieve_ledger b N Q u v hQ).trans ?_
  apply mul_le_mul_of_nonneg_left
  · gcongr with n hn
    exact vaughanTypeICoeff_norm_sq_le_cutoff b u v n
  · unfold primitiveLargeSieveConstant
    positivity

end

end AnalyticNumberTheory.LargeSieve
