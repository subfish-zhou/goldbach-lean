import AnalyticNumberTheory.Sieve.PanMainTerm
import Mathlib.Tactic

/-! # Reciprocal two-power weight estimate

The W1 lemma C estimate is
`Σ_{d≤Q} μ²(d)·2^{ω(d)}/d ≤ C·(log(Q+2))²`.
Its proof parallels `panMainTotientWeightedSum_le_polylog`
(W3, `PanMainTerm.lean` §4).

For squarefree `d`, `d = ∏_{p|d} p` and
`2^{ω(d)} = ∏_{p|d} 2`, so
`μ²(d)·2^{ω(d)}/d = ∏_{p|d} 2/p`.
Apply the subset bound
`Σ_{q≤Q, squarefree} ∏_{p|q} c p ≤ ∏_{p≤Q} (1+c p)`
with `c p = 2/p`, then `Real.prod_one_add_le_exp_sum`.
Since `Σ_{p≤Q} 2/p = 2·Σ_{p≤Q} 1/p`, Mertens' second theorem
(`mertensSecond_nat`) gives
`Σ_{p≤Q} 1/p ≤ log log Q + O(1)`.
Thus
`rexp(2·(log log Q + K)) = e^{2K}·(log Q)² ≤ C·(log(Q+2))²`.
The finite range `Q ≤ 2`, where the sum is at most 2, is absorbed
into the constant.
-/

namespace AnalyticNumberTheory.Sieve

open Finset Real
open AnalyticNumberTheory.Mertens
open scoped Classical
open scoped ArithmeticFunction.Moebius

/-- Two-power weight sum `Σ_{d≤Q} μ²(d)·2^{ω(d)}/d`,
the left side of W1 lemma C. -/
noncomputable def sumTwoPowWeighted (Q : ℕ) : ℝ :=
  ∑ d ∈ Finset.range (Q + 1),
    ((μ d : ℤ) : ℝ) ^ 2 * (2 : ℝ) ^ d.primeFactors.card / (d : ℝ)

/-- A squarefree natural number equals its prime-factor product:
`n = ∏_{p|n} p`. -/
private lemma squarefree_eq_prod_primeFactors {n : ℕ} (hn : Squarefree n) :
    n = ∏ p ∈ n.primeFactors, p := by
  exact (Nat.prod_primeFactors_of_squarefree hn).symm

/-- For squarefree `d`, `μ²(d)=1`, `2^{ω(d)}=∏_{p|d}2`,
and `d=∏_{p|d}p`, so the summand equals `∏_{p|d}2/p`. -/
theorem sumTwoPowWeighted_term_squarefree (d : ℕ) (hd : Squarefree d) :
    ((μ d : ℤ) : ℝ) ^ 2 * (2 : ℝ) ^ d.primeFactors.card / (d : ℝ) =
      ∏ p ∈ d.primeFactors, (2 : ℝ) / (p : ℝ) := by
  have hmu : ((μ d : ℤ) : ℝ) ^ 2 = 1 := by
    rw [← Int.cast_pow, ArithmeticFunction.moebius_sq_eq_one_of_squarefree hd]
    norm_num
  have hprod : (d : ℝ) = ∏ p ∈ d.primeFactors, (p : ℝ) := by
    rw [← Nat.cast_prod]
    exact_mod_cast squarefree_eq_prod_primeFactors hd
  calc
    ((μ d : ℤ) : ℝ) ^ 2 * (2 : ℝ) ^ d.primeFactors.card / (d : ℝ)
        = (2 : ℝ) ^ d.primeFactors.card / (∏ p ∈ d.primeFactors, (p : ℝ)) := by
          rw [hmu, hprod]
          norm_num
    _ = (∏ p ∈ d.primeFactors, (2 : ℝ)) / (∏ p ∈ d.primeFactors, (p : ℝ)) := by
          rw [← Finset.prod_const]
    _ = ∏ p ∈ d.primeFactors, (2 : ℝ) / (p : ℝ) := by
          rw [← Finset.prod_div_distrib]

/-- The weight vanishes for nonsquarefree `d`, since `μ(d)=0`. -/
theorem sumTwoPowWeighted_term_non_squarefree (d : ℕ) (hd : ¬ Squarefree d) :
    ((μ d : ℤ) : ℝ) ^ 2 * (2 : ℝ) ^ d.primeFactors.card / (d : ℝ) = 0 := by
  have hmu : (μ d : ℤ) = 0 := ArithmeticFunction.moebius_eq_zero_of_not_squarefree hd
  simp [hmu]

/-- The weight is nonnegative. -/
private lemma sumTwoPowWeighted_term_nonneg (d : ℕ) :
    0 ≤ ((μ d : ℤ) : ℝ) ^ 2 * (2 : ℝ) ^ d.primeFactors.card / (d : ℝ) := by
  exact div_nonneg (mul_nonneg (sq_nonneg _) (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _))
    (Nat.cast_nonneg d)

/-- The two-power weight sum is at most `∏_{p≤Q} (1+2/p)`,
by subset expansion with `c p = 2/p`. -/
theorem sumTwoPowWeighted_le_prod_one_add (Q : ℕ) :
    sumTwoPowWeighted Q ≤ ∏ p ∈ primesUpTo Q, (1 + (2 : ℝ) / (p : ℝ)) := by
  unfold sumTwoPowWeighted
  calc
    (∑ d ∈ Finset.range (Q + 1),
        ((μ d : ℤ) : ℝ) ^ 2 * (2 : ℝ) ^ d.primeFactors.card / (d : ℝ))
        = ∑ d ∈ Finset.range (Q + 1),
            if Squarefree d then
              ((μ d : ℤ) : ℝ) ^ 2 * (2 : ℝ) ^ d.primeFactors.card / (d : ℝ)
            else 0 := by
          apply Finset.sum_congr rfl
          intro d hd
          by_cases h : Squarefree d
          · rw [if_pos h]
          · rw [if_neg h]
            exact sumTwoPowWeighted_term_non_squarefree d h
    _ = ∑ d ∈ (Finset.range (Q + 1)).filter Squarefree,
          ((μ d : ℤ) : ℝ) ^ 2 * (2 : ℝ) ^ d.primeFactors.card / (d : ℝ) := by
          rw [Finset.sum_filter]
    _ = ∑ d ∈ (Finset.range (Q + 1)).filter Squarefree,
          ∏ p ∈ d.primeFactors, (2 : ℝ) / (p : ℝ) := by
          apply Finset.sum_congr rfl
          intro d hd
          exact sumTwoPowWeighted_term_squarefree d (Finset.mem_filter.mp hd).2
    _ ≤ ∏ p ∈ primesUpTo Q, (1 + (2 : ℝ) / (p : ℝ)) := by
          exact sum_squarefree_prod_primeFactors_le_prod_one_add Q
            (fun p => (2 : ℝ) / (p : ℝ)) (by
              intro p hp
              exact div_nonneg (by norm_num : (0 : ℝ) ≤ 2) (Nat.cast_nonneg p))

/-- The two-power weight sum is monotone in `Q`, by nonnegative weights. -/
theorem sumTwoPowWeighted_mono : Monotone sumTwoPowWeighted := by
  intro Q₁ Q₂ hQ
  unfold sumTwoPowWeighted
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.range_mono (Nat.add_le_add_right hQ 1)
  · intro d hd hnq
    exact sumTwoPowWeighted_term_nonneg d


/-- **W1 lemma C**:
`Σ_{d≤Q} μ²(d)·2^{ω(d)}/d ≤ C·(log(Q+2))²`.
Use subset expansion, `∏(1+u) ≤ exp(Σu)`,
`Σ_{p≤Q}2/p = 2·Σ_{p≤Q}1/p`, and Mertens' second theorem.
Absorb the initial range `Q ≤ 2` into the constant. -/
theorem sumTwoPowWeighted_le_polylog :
    ∃ C : ℝ, 0 < C ∧ ∀ Q : ℕ,
      sumTwoPowWeighted Q ≤ C * (Real.log (Q + 2)) ^ (2 : ℝ) := by
  classical
  obtain ⟨C₁, hC₁, hM⟩ := mertensSecond_nat
  let K : ℝ := |mertensSecondConstant| + C₁ / log 2
  let C : ℝ := max (2 / (log 2) ^ (2 : ℝ)) (rexp (2 * K))
  have hlg2 : (0 : ℝ) < log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hCpos : 0 < C := by
    dsimp [C]
    exact lt_max_of_lt_left (div_pos (by norm_num : (0 : ℝ) < 2) (Real.rpow_pos_of_pos hlg2 (2 : ℝ)))
  refine ⟨C, hCpos, ?_⟩
  intro Q
  by_cases hQ : Q ≤ 2
  · have hbnd : sumTwoPowWeighted Q ≤ 2 := by
      calc
        sumTwoPowWeighted Q ≤ sumTwoPowWeighted 2 := sumTwoPowWeighted_mono hQ
        _ ≤ ∏ p ∈ primesUpTo 2, (1 + (2 : ℝ) / (p : ℝ)) := sumTwoPowWeighted_le_prod_one_add 2
        _ = 2 := by
              have hP : primesUpTo 2 = ({2} : Finset ℕ) := by
                ext p
                simp only [mem_primesUpTo, Finset.mem_singleton]
                constructor
                · rintro ⟨hp, hp_le⟩
                  exact le_antisymm hp_le hp.two_le
                · rintro rfl
                  exact ⟨Nat.prime_two, le_rfl⟩
              rw [hP]
              norm_num
    have hQ2 : (2 : ℕ) ≤ Q + 2 := by omega
    have hlgQ2nn : (0 : ℝ) ≤ Real.log (Q + 2) :=
      Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ Q + 2))
    have hlogle : (log 2) ^ (2 : ℝ) ≤ (Real.log (Q + 2)) ^ (2 : ℝ) := by
      exact Real.rpow_le_rpow (le_of_lt hlg2)
        (Real.log_le_log (by norm_num : (0 : ℝ) < 2) (by exact_mod_cast hQ2))
        (by norm_num : (0 : ℝ) ≤ (2 : ℝ))
    calc
      sumTwoPowWeighted Q ≤ 2 := hbnd
      _ = 2 / (log 2) ^ (2 : ℝ) * (log 2) ^ (2 : ℝ) := by
        have hx : (log 2) ^ (2 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hlg2 (2 : ℝ)).ne'
        exact (div_mul_cancel₀ _ hx).symm
      _ ≤ 2 / (log 2) ^ (2 : ℝ) * (Real.log (Q + 2)) ^ (2 : ℝ) := by
        exact mul_le_mul_of_nonneg_left hlogle
          (div_nonneg (by norm_num : (0 : ℝ) ≤ 2) (le_of_lt (Real.rpow_pos_of_pos hlg2 (2 : ℝ))))
      _ ≤ C * (Real.log (Q + 2)) ^ (2 : ℝ) := by
        exact mul_le_mul_of_nonneg_right (le_max_left (2 / (log 2) ^ (2 : ℝ)) (rexp (2 * K)))
          (Real.rpow_nonneg hlgQ2nn (2 : ℝ))
  · have hQ3 : 3 ≤ Q := by omega
    have hQ2 : 2 ≤ Q := by omega
    have hQ1 : (1 : ℝ) < (Q : ℝ) := by exact_mod_cast (by omega : 1 < Q)
    have hlogQ : (0 : ℝ) < log (Q : ℝ) := Real.log_pos hQ1
    have hlogQnn : (0 : ℝ) ≤ log (Q : ℝ) := le_of_lt hlogQ
    have hM' : |primeReciprocalSum Q - (log (log (Q : ℝ)) + mertensSecondConstant)| ≤
        C₁ / log (Q : ℝ) := hM Q hQ2
    have hpRS : primeReciprocalSum Q ≤ log (log (Q : ℝ)) + K := by
      have hle1 : primeReciprocalSum Q ≤
          log (log (Q : ℝ)) + mertensSecondConstant + C₁ / log (Q : ℝ) := by
        linarith [(abs_le.mp hM').2]
      have hc : mertensSecondConstant ≤ |mertensSecondConstant| := le_abs_self _
      have hC : C₁ / log (Q : ℝ) ≤ C₁ / log 2 := by
        exact div_le_div_of_nonneg_left (le_of_lt hC₁) hlg2
          (Real.log_le_log (by norm_num : (0 : ℝ) < 2) (by exact_mod_cast hQ2))
      dsimp [K]
      linarith
    have hsum_eq : (∑ p ∈ primesUpTo Q, (2 : ℝ) / (p : ℝ)) = 2 * primeReciprocalSum Q := by
      simp [primeReciprocalSum, Finset.mul_sum, div_eq_mul_inv]
    have hlgQ2nn : (0 : ℝ) ≤ Real.log (Q + 2) :=
      Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ Q + 2))
    have hlogle : (log (Q : ℝ)) ^ (2 : ℝ) ≤ (Real.log (Q + 2)) ^ (2 : ℝ) := by
      exact Real.rpow_le_rpow hlogQnn
        (Real.log_le_log (by positivity : (0 : ℝ) < (Q : ℝ)) (by exact_mod_cast (by omega : Q ≤ Q + 2)))
        (by norm_num : (0 : ℝ) ≤ (2 : ℝ))
    calc
      sumTwoPowWeighted Q ≤ ∏ p ∈ primesUpTo Q, (1 + (2 : ℝ) / (p : ℝ)) :=
            sumTwoPowWeighted_le_prod_one_add Q
      _ ≤ rexp (∑ p ∈ primesUpTo Q, (2 : ℝ) / (p : ℝ)) := by
            exact Real.prod_one_add_le_exp_sum (primesUpTo Q)
              (fun p => div_nonneg (by norm_num : (0 : ℝ) ≤ 2) (Nat.cast_nonneg p))
      _ = rexp (2 * primeReciprocalSum Q) := by rw [hsum_eq]
      _ ≤ rexp (2 * (log (log (Q : ℝ)) + K)) := by
            exact Real.exp_le_exp.mpr (by
              have h2 : (0 : ℝ) ≤ 2 := by norm_num
              exact mul_le_mul_of_nonneg_left hpRS h2)
      _ = rexp (2 * K) * (log (Q : ℝ)) ^ (2 : ℝ) := by
            rw [Real.rpow_def_of_pos hlogQ, ← Real.exp_add]
            congr 1
            ring
      _ ≤ C * (Real.log (Q + 2)) ^ (2 : ℝ) := by
            exact mul_le_mul (le_max_right (2 / (log 2) ^ (2 : ℝ)) (rexp (2 * K))) hlogle
              (Real.rpow_nonneg hlogQnn (2 : ℝ)) (le_of_lt hCpos)
