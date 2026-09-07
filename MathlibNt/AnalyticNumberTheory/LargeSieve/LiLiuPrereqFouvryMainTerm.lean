import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryDispersion
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

/-!
# The finite U and V main-term expansions

Fouvry (1984), (7.11), and the first equality immediately following it:
expand both modulus sums, then remove the coprimality restriction by
Mobius inversion. The mixed term is rearranged as in (7.13).
This stops before Poisson summation and its error estimates.
-/

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

open Finset

noncomputable section

theorem sum_moebius_divisors (n : ℕ) :
    (∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℝ)) =
      if n = 1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℝ => f n)
    (ArithmeticFunction.coe_zeta_mul_coe_moebius (R := ℝ))
  simpa only [ArithmeticFunction.coe_zeta_mul_apply,
    ArithmeticFunction.intCoe_apply, ArithmeticFunction.one_apply] using h

theorem coprime_indicator_eq_moebius {q : ℕ} (hq : q ≠ 0) (m : ℕ) :
    (if m.Coprime q then (1 : ℝ) else 0) =
      ∑ d ∈ q.divisors, if d ∣ m then (ArithmeticFunction.moebius d : ℝ) else 0 := by
  have hg : m.gcd q ≠ 0 :=
    (Nat.gcd_pos_of_pos_right m (Nat.pos_of_ne_zero hq)).ne'
  have hd : q.divisors.filter (fun d => d ∣ m) = (m.gcd q).divisors := by
    ext d
    simp [Nat.mem_divisors, hq, hg, Nat.dvd_gcd_iff, and_comm]
  rw [← Finset.sum_filter, hd, sum_moebius_divisors]

theorem coprime_weight_eq_moebius
    (S : Finset ℕ) (w : ℕ → ℝ) {q : ℕ} (hq : q ≠ 0) :
    (∑ m ∈ S, if m.Coprime q then w m else 0) =
      ∑ d ∈ q.divisors, (ArithmeticFunction.moebius d : ℝ) *
        ∑ m ∈ S, if d ∣ m then w m else 0 := by
  calc
    _ = ∑ m ∈ S,
        (∑ d ∈ q.divisors, if d ∣ m then (ArithmeticFunction.moebius d : ℝ) else 0) *
          w m := by
      apply Finset.sum_congr rfl
      intro m _
      rw [← coprime_indicator_eq_moebius hq]
      split_ifs <;> simp
    _ = _ := by
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro d _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m _
      split_ifs <;> simp

private theorem weighted_row_product
    (S Q : Finset ℕ) (w : ℕ → ℝ) (F G : ℕ → ℕ → ℝ) :
    (∑ m ∈ S, w m * (∑ q ∈ Q, F q m) * (∑ r ∈ Q, G r m)) =
      ∑ q ∈ Q, ∑ r ∈ Q, ∑ m ∈ S, w m * F q m * G r m := by
  simp_rw [mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q _
  rw [Finset.sum_comm]

theorem dispersionU_eq_double_sum
    (S N Q : Finset ℕ) (w β c : ℕ → ℝ) (a : ℤ) :
    dispersionU S N Q w β c a =
      ∑ q ∈ reducedModuli Q a, ∑ r ∈ reducedModuli Q a,
        (c q * c r / ((q.totient : ℝ) * (r.totient : ℝ))) *
          coprimeMass N β q * coprimeMass N β r *
            ∑ m ∈ S, if m.Coprime (q * r) then w m else 0 := by
  unfold dispersionU principalRow
  simp_rw [pow_two, ← mul_assoc]
  rw [weighted_row_product]
  apply Finset.sum_congr rfl
  intro q _
  apply Finset.sum_congr rfl
  intro r _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  simp only [Nat.coprime_mul_iff_right]
  by_cases hq : m.Coprime q <;> by_cases hr : m.Coprime r
  all_goals
    simp only [Nat.Coprime] at hq hr ⊢
    simp [hq, hr, div_eq_mul_inv, mul_inv_rev]
    <;> ring

/-- The exact divisor expansion to which the Poisson estimate for U must be applied. -/
theorem dispersionU_eq_moebius
    (S N Q : Finset ℕ) (w β c : ℕ → ℝ) (a : ℤ)
    (hQ : ∀ q ∈ Q, q ≠ 0) :
    dispersionU S N Q w β c a =
      ∑ q ∈ reducedModuli Q a, ∑ r ∈ reducedModuli Q a,
        (c q * c r / ((q.totient : ℝ) * (r.totient : ℝ))) *
          coprimeMass N β q * coprimeMass N β r *
            ∑ d ∈ (q * r).divisors, (ArithmeticFunction.moebius d : ℝ) *
              ∑ m ∈ S, if d ∣ m then w m else 0 := by
  rw [dispersionU_eq_double_sum]
  apply Finset.sum_congr rfl
  intro q hq
  apply Finset.sum_congr rfl
  intro r hr
  rw [coprime_weight_eq_moebius S w
    (mul_ne_zero (hQ q (Finset.mem_filter.mp hq).1)
      (hQ r (Finset.mem_filter.mp hr).1))]

/-- The mixed term with the m-sum exposed, as in F84 (7.13), without inverse notation. -/
theorem dispersionV_eq_progression_sum
    (S N Q : Finset ℕ) (w β c : ℕ → ℝ) (a : ℤ) :
    dispersionV S N Q w β c a =
      ∑ q ∈ reducedModuli Q a, ∑ r ∈ reducedModuli Q a,
        (c q * c r / (r.totient : ℝ)) * coprimeMass N β r *
          ∑ n ∈ N, β n * ∑ m ∈ S,
            if n.Coprime q ∧ m.Coprime r ∧ Int.ModEq q ((m : ℤ) * n) a
              then w m else 0 := by
  unfold dispersionV progressionRow principalRow
  rw [weighted_row_product]
  apply Finset.sum_congr rfl
  intro q hq
  apply Finset.sum_congr rfl
  intro r _
  have ha : Int.gcd a q = 1 := (Finset.mem_filter.mp hq).2
  calc
    _ = ∑ m ∈ S, ∑ n ∈ N,
        (c q * c r / (r.totient : ℝ)) * coprimeMass N β r *
          (β n * (if n.Coprime q ∧ m.Coprime r ∧
              Int.ModEq q ((m : ℤ) * n) a then w m else 0)) := by
      apply Finset.sum_congr rfl
      intro m _
      by_cases hm : m.Coprime q
      · rw [if_pos hm]
        unfold progressionMass
        simp_rw [Finset.mul_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro n _
        by_cases hmn : Int.ModEq q ((m : ℤ) * n) a
        · have hn : n.Coprime q := (coprime_of_product_congruent ha hmn).2
          by_cases hr : m.Coprime r
          · have hc : n.Coprime q ∧ m.Coprime r ∧
                Int.ModEq q ((m : ℤ) * n) a := ⟨hn, hr, hmn⟩
            simp only [if_pos hmn, if_pos hr, if_pos hc]
            ring
          · have hc : ¬(n.Coprime q ∧ m.Coprime r ∧
                Int.ModEq q ((m : ℤ) * n) a) := fun h => hr h.2.1
            simp only [if_pos hmn, if_neg hr, if_neg hc, mul_zero]
        · have hc : ¬(n.Coprime q ∧ m.Coprime r ∧
              Int.ModEq q ((m : ℤ) * n) a) := fun h => hmn h.2.2
          simp only [if_neg hmn, if_neg hc, mul_zero, zero_mul]
      · rw [if_neg hm, mul_zero, zero_mul]
        symm
        apply Finset.sum_eq_zero
        intro n _
        have hc : ¬(n.Coprime q ∧ m.Coprime r ∧
            Int.ModEq q ((m : ℤ) * n) a) :=
          fun h => hm (coprime_of_product_congruent ha h.2.2).1
        simp only [if_neg hc, mul_zero]
    _ = _ := by
      rw [Finset.sum_comm, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _
      rw [Finset.mul_sum, Finset.mul_sum]

end

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
