import AnalyticNumberTheory.Sieve.W1LemmaB
import AnalyticNumberTheory.Sieve.SumTwoPowWeighted
import AnalyticNumberTheory.Sieve.PanV3SquareMean
import Mathlib.Tactic

/-! # W1 weight estimate

This module assembles
`Σ_{q≤Q} μ²(q)·3^{ω(q)}·φ(q)/q ≤ C·Q·(log(Q+2))²`
from the following estimates:

```text
Σ_{q≤Q} μ²·3^ω·φ/q
  ≤ Σ_{q≤Q} μ²·3^ω                              (lemma A: φ/q ≤ 1)
  = Σ_{q≤Q, squarefree} 3^ω(q)                   (μ² is the squarefree indicator)
  = Σ_{q≤Q, squarefree} Σ_{d|q, squarefree} 2^ω(d) (lemma B)
  ≤ Σ_{d≤Q, squarefree} 2^ω(d)·(Q/d)             (exchange sums and count multiples)
  = Q·Σ_{d≤Q, squarefree} 2^ω(d)/d
  = Q·Σ_{d≤Q} μ²(d)·2^ω(d)/d
  = Q·sumTwoPowWeighted Q
  ≤ C·Q·(log(Q+2))²                              (lemma C).
```

The count of positive multiples is at most `⌊Q/d⌋ ≤ Q/d`.
The shift in `log(Q+2)` is essential, as in lemma C and
`panMainTotientWeightedSum_le_polylog`: using `log Q` would give
right side 0 but left side 1 at `Q = 1`.
-/

namespace AnalyticNumberTheory.Sieve

open Finset Real
open scoped BigOperators
open scoped Classical
open scoped ArithmeticFunction.Moebius

/-! ## 1. Lemma A: φ(q)/q ≤ 1 -/

/-- **Lemma A**: `(φ(q):ℝ)/q ≤ 1` for every natural `q`,
by `Nat.totient_le`. At `q = 0`, totalized division gives a
left side of 0, so the inequality is trivial. -/
theorem totient_div_self_le_one (q : ℕ) : (Nat.totient q : ℝ) / (q : ℝ) ≤ 1 := by
  by_cases hq : q = 0
  · subst q
    simp
  · have hle : Nat.totient q ≤ q := Nat.totient_le q
    have hle' : (Nat.totient q : ℝ) ≤ (q : ℝ) := by exact_mod_cast hle
    have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hq)
    exact (div_le_one hqpos).2 hle'

/-! ## 2. The weighted expression panTypeIWeight3 and lemma A -/

/-- W1 weighted expression:
`panTypeIWeight3 Q = Σ_{q≤Q} μ²(q)·3^{ω(q)}·φ(q)/q`.
The `q = 0` term has zero weight. -/
noncomputable def panTypeIWeight3 (Q : ℕ) : ℝ :=
  ∑ q ∈ Finset.range (Q + 1),
    ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card * (Nat.totient q : ℝ) / (q : ℝ)

/-- Termwise bound `μ²(q)·3^{ω(q)}·φ(q)/q ≤ μ²(q)·3^{ω(q)}`,
by lemma A and nonnegative weights. -/
private lemma panTypeIWeight3_term_le (q : ℕ) :
    ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card * (Nat.totient q : ℝ) / (q : ℝ) ≤
      ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card := by
  calc
    ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card * (Nat.totient q : ℝ) / (q : ℝ)
        = ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card *
            ((Nat.totient q : ℝ) / (q : ℝ)) := by
          rw [mul_div_assoc]
    _ ≤ ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card * 1 := by
          exact mul_le_mul_of_nonneg_left (totient_div_self_le_one q)
            (mul_nonneg (sq_nonneg _) (pow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _))
    _ = ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card := by ring

/-- Rearrangement `a·(b/c) = b·(a/c)`, used to factor `Q`
out of the sum. -/
private lemma mul_div_mul_comm (a b c : ℝ) : a * (b / c) = b * (a / c) := by
  rw [← mul_div_assoc, ← mul_div_assoc, mul_comm a b]

/-- `panTypeIWeight3 Q ≤ Σ_{q≤Q, squarefree} 3^{ω(q)}`:
apply lemma A termwise, then use the squarefree indicator `μ²`. -/
theorem panTypeIWeight3_le_sqfree_three_pow (Q : ℕ) :
    panTypeIWeight3 Q ≤
      ∑ q ∈ (Finset.range (Q + 1)).filter Squarefree, (3 : ℝ) ^ q.primeFactors.card := by
  classical
  unfold panTypeIWeight3
  calc
    (∑ q ∈ Finset.range (Q + 1),
        ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card * (Nat.totient q : ℝ) / (q : ℝ))
        ≤ ∑ q ∈ Finset.range (Q + 1),
            ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card := by
          exact Finset.sum_le_sum (fun q hq => panTypeIWeight3_term_le q)
    _ = ∑ q ∈ (Finset.range (Q + 1)).filter Squarefree, (3 : ℝ) ^ q.primeFactors.card := by
          calc
            (∑ q ∈ Finset.range (Q + 1),
                ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card)
            = ∑ q ∈ Finset.range (Q + 1),
                (if Squarefree q then
                  ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card
                else 0) := by
                apply Finset.sum_congr rfl
                intro q hq
                by_cases h : Squarefree q
                · simp [h]
                · simp [h, ArithmeticFunction.moebius_eq_zero_of_not_squarefree h]
            _ = ∑ q ∈ (Finset.range (Q + 1)).filter Squarefree,
                ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card := by
                rw [Finset.sum_filter]
            _ = ∑ q ∈ (Finset.range (Q + 1)).filter Squarefree, (3 : ℝ) ^ q.primeFactors.card := by
                apply Finset.sum_congr rfl
                intro q hq
                have hsq : Squarefree q := (Finset.mem_filter.mp hq).2
                have hmu : ((μ q : ℤ) : ℝ) ^ 2 = 1 := by
                  rw [← Int.cast_pow, ArithmeticFunction.moebius_sq_eq_one_of_squarefree hsq]
                  norm_num
                rw [hmu]
                simp


/-! ## 3. Exchanging sums and counting multiples -/

/-- The divisors of squarefree `q ≤ Q` belong to the global
squarefree set `{d ≤ Q : Squarefree d}`. -/
private lemma sqfree_divisors_subset_sqfree_range (Q : ℕ) {q : ℕ}
    (hq : q ∈ (Finset.range (Q + 1)).filter Squarefree) :
    q.divisors.filter Squarefree ⊆ (Finset.range (Q + 1)).filter Squarefree := by
  intro d hd
  have hdmem := Finset.mem_filter.mp hd
  have hdvd : d ∣ q := Nat.dvd_of_mem_divisors hdmem.1
  have hqmem : q ∈ Finset.range (Q + 1) := (Finset.mem_filter.mp hq).1
  have hqSq : Squarefree q := (Finset.mem_filter.mp hq).2
  have hq_ne : q ≠ 0 := by
    intro hq0
    rw [hq0] at hqSq
    exact not_squarefree_zero hqSq
  have hdle : d ≤ q := Nat.le_of_dvd (Nat.pos_of_ne_zero hq_ne) hdvd
  rw [Finset.mem_filter]
  constructor
  · rw [Finset.mem_range]
    have hq_le : q ≤ Q := Nat.lt_succ_iff.mp (Finset.mem_range.mp hqmem)
    omega
  · exact hdmem.2

/-- **Double-sum bound**: for nonnegative `g`,
`Σ_{q≤Q, squarefree} Σ_{d|q, squarefree} g(d)
 ≤ Σ_{d≤Q, squarefree} g(d)·(Q/d)`.
Extend the inner index to the fixed squarefree set up to `Q`
using indicators, then reorder by `d` with `Finset.sum_comm`
and `Finset.sum_boole`. Count positive multiples via
`v3_card_multiples_Icc` and `Nat.cast_div_le` to get
`#{1≤q≤Q : d|q} ≤ ⌊Q/d⌋ ≤ Q/d`. -/
private lemma sqfreeDoubleSum_le (Q : ℕ) (g : ℕ → ℝ) (hg : ∀ d, 0 ≤ g d) :
    (∑ q ∈ (Finset.range (Q + 1)).filter Squarefree,
        ∑ d ∈ q.divisors.filter Squarefree, g d) ≤
      ∑ d ∈ (Finset.range (Q + 1)).filter Squarefree, g d * ((Q : ℝ) / (d : ℝ)) := by
  classical
  calc
    (∑ q ∈ (Finset.range (Q + 1)).filter Squarefree,
        ∑ d ∈ q.divisors.filter Squarefree, g d)
        = ∑ q ∈ (Finset.range (Q + 1)).filter Squarefree,
            ∑ d ∈ (Finset.range (Q + 1)).filter Squarefree,
              (if d ∈ q.divisors.filter Squarefree then g d else 0) := by
          apply Finset.sum_congr rfl
          intro q hq
          rw [← Finset.sum_filter]
          congr 1
          apply Finset.ext
          intro d
          constructor
          · intro hd
            exact Finset.mem_filter.mpr ⟨sqfree_divisors_subset_sqfree_range Q hq hd, hd⟩
          · intro hd
            exact (Finset.mem_filter.mp hd).2
    _ = ∑ q ∈ (Finset.range (Q + 1)).filter Squarefree,
          ∑ d ∈ (Finset.range (Q + 1)).filter Squarefree,
            g d * (if d ∈ q.divisors.filter Squarefree then (1 : ℝ) else 0) := by
          apply Finset.sum_congr rfl
          intro q hq
          apply Finset.sum_congr rfl
          intro d hd
          by_cases h : d ∈ q.divisors.filter Squarefree
          · simp [h]
          · simp [h]
    _ = ∑ d ∈ (Finset.range (Q + 1)).filter Squarefree,
          ∑ q ∈ (Finset.range (Q + 1)).filter Squarefree,
            g d * (if d ∈ q.divisors.filter Squarefree then (1 : ℝ) else 0) := by
          rw [Finset.sum_comm]
    _ = ∑ d ∈ (Finset.range (Q + 1)).filter Squarefree,
          g d * (∑ q ∈ (Finset.range (Q + 1)).filter Squarefree,
            (if d ∈ q.divisors.filter Squarefree then (1 : ℝ) else 0)) := by
          apply Finset.sum_congr rfl
          intro d hd
          rw [Finset.mul_sum]
    _ = ∑ d ∈ (Finset.range (Q + 1)).filter Squarefree,
          g d * (((Finset.range (Q + 1)).filter Squarefree).filter
            (fun q => d ∈ q.divisors.filter Squarefree)).card := by
          apply Finset.sum_congr rfl
          intro d hd
          rw [Finset.sum_boole (p := fun q : ℕ => d ∈ q.divisors.filter Squarefree)
            (s := (Finset.range (Q + 1)).filter Squarefree)]
    _ ≤ ∑ d ∈ (Finset.range (Q + 1)).filter Squarefree, g d * ((Q : ℝ) / (d : ℝ)) := by
          apply Finset.sum_le_sum
          intro d hd
          have hsqd : Squarefree d := (Finset.mem_filter.mp hd).2
          have hd_ne0 : d ≠ 0 := by
            intro hd0
            rw [hd0] at hsqd
            exact not_squarefree_zero hsqd
          have hd1 : 1 ≤ d := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hd_ne0)
          have hcnt1 : (((Finset.range (Q + 1)).filter Squarefree).filter
                (fun q => d ∈ q.divisors.filter Squarefree)).card ≤
              (((Finset.range (Q + 1)).filter Squarefree).filter (fun q => d ∣ q)).card := by
            exact Finset.card_le_card (by
              intro q hq
              rcases Finset.mem_filter.mp hq with ⟨hqS, hdq⟩
              exact Finset.mem_filter.mpr ⟨hqS,
                Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hdq).1⟩)
          have hcnt2 : (((Finset.range (Q + 1)).filter Squarefree).filter (fun q => d ∣ q)).card ≤
              ((Finset.Icc 1 Q).filter (fun q => d ∣ q)).card := by
            exact Finset.card_le_card (by
              intro q hq
              rcases Finset.mem_filter.mp hq with ⟨hqS, hdq⟩
              rw [Finset.mem_filter]
              constructor
              · rw [Finset.mem_Icc]
                constructor
                · have hqSq : Squarefree q := (Finset.mem_filter.mp hqS).2
                  have hq_ne0 : q ≠ 0 := by
                    intro hq0
                    rw [hq0] at hqSq
                    exact not_squarefree_zero hqSq
                  exact Nat.succ_le_of_lt (Nat.pos_of_ne_zero hq_ne0)
                · have hqmem : q ∈ Finset.range (Q + 1) := (Finset.mem_filter.mp hqS).1
                  exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hqmem)
              · exact hdq)
          have hcnt3 : ((Finset.Icc 1 Q).filter (fun q => d ∣ q)).card = Q / d :=
            v3_card_multiples_Icc Q d hd1
          have hcount : (((Finset.range (Q + 1)).filter Squarefree).filter
                (fun q => d ∈ q.divisors.filter Squarefree)).card ≤ (Q : ℝ) / (d : ℝ) := by
            calc
              (((Finset.range (Q + 1)).filter Squarefree).filter
                  (fun q => d ∈ q.divisors.filter Squarefree)).card
                  ≤ (((Finset.Icc 1 Q).filter (fun q => d ∣ q)).card : ℝ) := by
                    exact_mod_cast (le_trans hcnt1 hcnt2)
              _ ≤ (Q : ℝ) / (d : ℝ) := by
                    calc
                      (((Finset.Icc 1 Q).filter (fun q => d ∣ q)).card : ℝ) = ((Q / d : ℕ) : ℝ) := by
                        rw [hcnt3]
                      _ ≤ (Q : ℝ) / (d : ℝ) := Nat.cast_div_le
          exact mul_le_mul_of_nonneg_left hcount (hg d)

/-- Restore the Moebius-square weight:
`Σ_{d≤Q, squarefree} 2^{ω(d)}/d
 = Σ_{d≤Q} μ²(d)·2^{ω(d)}/d = sumTwoPowWeighted Q`.
Nonsquarefree terms vanish; squarefree terms have `μ² = 1`. -/
private lemma sqfreeTwoPowSum_eq_sumTwoPowWeighted (Q : ℕ) :
    (∑ d ∈ (Finset.range (Q + 1)).filter Squarefree,
        (2 : ℝ) ^ d.primeFactors.card / (d : ℝ)) =
      sumTwoPowWeighted Q := by
  classical
  unfold sumTwoPowWeighted
  symm
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
        · simp [h]
        · simp [h, ArithmeticFunction.moebius_eq_zero_of_not_squarefree h]
    _ = ∑ d ∈ (Finset.range (Q + 1)).filter Squarefree,
          ((μ d : ℤ) : ℝ) ^ 2 * (2 : ℝ) ^ d.primeFactors.card / (d : ℝ) := by
          rw [Finset.sum_filter]
    _ = ∑ d ∈ (Finset.range (Q + 1)).filter Squarefree,
          (2 : ℝ) ^ d.primeFactors.card / (d : ℝ) := by
          apply Finset.sum_congr rfl
          intro d hd
          have hsq : Squarefree d := (Finset.mem_filter.mp hd).2
          have hmu : ((μ d : ℤ) : ℝ) ^ 2 = 1 := by
            rw [← Int.cast_pow, ArithmeticFunction.moebius_sq_eq_one_of_squarefree hsq]
            norm_num
          rw [hmu]
          norm_num

/-- **W1 assembly**: `panTypeIWeight3 Q ≤ Q·sumTwoPowWeighted Q`
for every `Q`, by lemma A, the termwise expansion in lemma B,
exchange of sums, counting multiples, and restoration of `μ²`. -/
theorem panTypeIWeight3_le_Q_mul_sumTwoPowWeighted (Q : ℕ) :
    panTypeIWeight3 Q ≤ (Q : ℝ) * sumTwoPowWeighted Q := by
  classical
  calc
    panTypeIWeight3 Q ≤ ∑ q ∈ (Finset.range (Q + 1)).filter Squarefree,
        (3 : ℝ) ^ q.primeFactors.card := panTypeIWeight3_le_sqfree_three_pow Q
    _ = ∑ q ∈ (Finset.range (Q + 1)).filter Squarefree,
          ∑ d ∈ q.divisors.filter Squarefree, (2 : ℝ) ^ d.primeFactors.card := by
          apply Finset.sum_congr rfl
          intro q hq
          exact three_pow_omega_eq_sum_two_pow (Finset.mem_filter.mp hq).2
    _ ≤ ∑ d ∈ (Finset.range (Q + 1)).filter Squarefree,
          (2 : ℝ) ^ d.primeFactors.card * ((Q : ℝ) / (d : ℝ)) := by
          exact sqfreeDoubleSum_le Q (fun d => (2 : ℝ) ^ d.primeFactors.card)
            (fun d => pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) d.primeFactors.card)
    _ = (Q : ℝ) * ∑ d ∈ (Finset.range (Q + 1)).filter Squarefree,
          (2 : ℝ) ^ d.primeFactors.card / (d : ℝ) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro d hd
          exact mul_div_mul_comm ((2 : ℝ) ^ d.primeFactors.card) (Q : ℝ) (d : ℝ)
    _ = (Q : ℝ) * sumTwoPowWeighted Q := by
          rw [sqfreeTwoPowSum_eq_sumTwoPowWeighted Q]


/-! ## 4. W1 theorem -/

/-- **W1 theorem**:
`Σ_{q≤Q} μ²(q)·3^{ω(q)}·φ(q)/q ≤ C·Q·(log(Q+2))²`
for all `Q : ℕ`.
Apply lemma A (`φ/q ≤ 1`), restrict to squarefree integers,
expand by lemma B, exchange sums and count positive multiples
by `Q/d`, restore `μ²`, and apply lemma C
(`sumTwoPowWeighted_le_polylog`).
The shift `Q+2` matches lemma C; replacing it by `Q`
would make the bound false at `Q = 1`. -/
theorem panTypeIWeight3_le_polylog :
    ∃ C : ℝ, 0 < C ∧ ∀ Q : ℕ,
      panTypeIWeight3 Q ≤ C * (Q : ℝ) * (Real.log (Q + 2)) ^ (2 : ℝ) := by
  classical
  obtain ⟨C₁, hC₁pos, hC₁⟩ := sumTwoPowWeighted_le_polylog
  refine ⟨C₁, hC₁pos, ?_⟩
  intro Q
  calc
    panTypeIWeight3 Q ≤ (Q : ℝ) * sumTwoPowWeighted Q :=
      panTypeIWeight3_le_Q_mul_sumTwoPowWeighted Q
    _ ≤ (Q : ℝ) * (C₁ * (Real.log (Q + 2)) ^ (2 : ℝ)) := by
          exact mul_le_mul_of_nonneg_left (hC₁ Q) (Nat.cast_nonneg Q)
    _ = C₁ * (Q : ℝ) * (Real.log (Q + 2)) ^ (2 : ℝ) := by ring

end AnalyticNumberTheory.Sieve
