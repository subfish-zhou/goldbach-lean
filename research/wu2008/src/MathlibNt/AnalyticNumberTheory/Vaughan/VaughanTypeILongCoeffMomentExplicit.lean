

import MathlibNt.AnalyticNumberTheory.Vaughan.VaughanTypeILongVariable
import MathlibNt.AnalyticNumberTheory.Vaughan.VaughanTypeIIActualTensorMomentExplicit

/-!
 # Explicit moment bound for the long-variable Vaughan Type-I coefficient

The two truncated convolutions are opened before summing over `n`.  The
Möbius factor has absolute value at most one.  In the middle convolution the
nonnegative truncated `Λ`-sum is enlarged to the full divisor sum and then
identified with `log`.  Consequently each Type-I piece is bounded by
`τ(n) log (N+1)`, uniformly in both cutoffs.  The divisor-square moment with
constant `27` then gives an `N log^5(N+1)` coefficient moment.
-/

namespace AnalyticNumberTheory.LargeSieve

open Classical Finset
open scoped BigOperators ArithmeticFunction

noncomputable section

private lemma moebius_cast_abs_le_one (d : ℕ) :
    |((ArithmeticFunction.moebius d : ℤ) : ℝ)| ≤ 1 := by
  exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := d))

private lemma abs_sum_bi_le_card_mul
    {α : Type*} (s : Finset α) (f : α → ℝ) (L : ℝ)
    (hf : ∀ a ∈ s, |f a| ≤ L) :
    |∑ a ∈ s, f a| ≤ (s.card : ℝ) * L := by
  calc
    |∑ a ∈ s, f a| ≤ ∑ a ∈ s, |f a| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _a ∈ s, L := Finset.sum_le_sum hf
    _ = (s.card : ℝ) * L := by simp

private lemma log_nat_le_log_succ
    {m N : ℕ} (hm : 0 < m) (hmN : m ≤ N) :
    Real.log (m : ℝ) ≤ Real.log (N + 1 : ℕ) := by
  apply Real.strictMonoOn_log.monotoneOn
  · show (0 : ℝ) < (m : ℝ)
    exact_mod_cast hm
  · show (0 : ℝ) < ((N + 1 : ℕ) : ℝ)
    exact_mod_cast Nat.succ_pos N
  · exact_mod_cast hmN.trans (Nat.le_succ N)

private lemma vaughanFirst_abs_le_divisors_mul_log
    {n N u : ℕ} (hn : 0 < n) (hnN : n ≤ N) :
    |Sieve.vaughanFirst n u| ≤
      (n.divisors.card : ℝ) * Real.log (N + 1 : ℕ) := by
  unfold Sieve.vaughanFirst
  let D := n.divisors.filter (fun d => d ≤ u)
  have hterm : ∀ d ∈ D,
      |((ArithmeticFunction.moebius d : ℤ) : ℝ) *
          Real.log ((n / d : ℕ) : ℝ)| ≤ Real.log (N + 1 : ℕ) := by
    intro d hd
    have hddiv : d ∈ n.divisors := (Finset.mem_filter.mp hd).1
    have hdpos : 0 < d := Nat.pos_of_mem_divisors hddiv
    have hdle : d ≤ n := Nat.le_of_dvd hn (Nat.dvd_of_mem_divisors hddiv)
    have hqpos : 0 < n / d := Nat.div_pos hdle hdpos
    have hlog0 : 0 ≤ Real.log ((n / d : ℕ) : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hqpos)
    have hlog : Real.log ((n / d : ℕ) : ℝ) ≤ Real.log (N + 1 : ℕ) :=
      log_nat_le_log_succ hqpos ((Nat.div_le_self n d).trans hnN)
    rw [abs_mul, abs_of_nonneg hlog0]
    calc
      |((ArithmeticFunction.moebius d : ℤ) : ℝ)| * Real.log ((n / d : ℕ) : ℝ)
          ≤ 1 * Real.log ((n / d : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_right (moebius_cast_abs_le_one d) hlog0
      _ ≤ Real.log (N + 1 : ℕ) := by simpa using hlog
  calc
    |∑ d ∈ D,
        ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
          Real.log ((n / d : ℕ) : ℝ)|
        ≤ (D.card : ℝ) * Real.log (N + 1 : ℕ) :=
      abs_sum_bi_le_card_mul D _ _ hterm
    _ ≤ (n.divisors.card : ℝ) * Real.log (N + 1 : ℕ) := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast Finset.card_filter_le n.divisors (fun d => d ≤ u)
      · exact Real.log_nonneg (by
          exact_mod_cast Nat.succ_le_succ (Nat.zero_le N))

private lemma vaughanMiddle_abs_le_divisors_mul_log
    {n N u v : ℕ} (hn : 0 < n) (hnN : n ≤ N) :
    |Sieve.vaughanMiddle n u v| ≤
      (n.divisors.card : ℝ) * Real.log (N + 1 : ℕ) := by
  unfold Sieve.vaughanMiddle
  let D := n.divisors.filter (fun d => d ≤ u)
  have houter : ∀ d ∈ D,
      |∑ e ∈ (n / d).divisors.filter (fun e => e ≤ v),
          ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
            ArithmeticFunction.vonMangoldt e| ≤ Real.log (N + 1 : ℕ) := by
    intro d hd
    have hddiv : d ∈ n.divisors := (Finset.mem_filter.mp hd).1
    have hdpos : 0 < d := Nat.pos_of_mem_divisors hddiv
    have hdle : d ≤ n := Nat.le_of_dvd hn (Nat.dvd_of_mem_divisors hddiv)
    have hqpos : 0 < n / d := Nat.div_pos hdle hdpos
    let E := (n / d).divisors.filter (fun e => e ≤ v)
    have hsum_nonneg : 0 ≤ ∑ e ∈ E, ArithmeticFunction.vonMangoldt e := by
      exact Finset.sum_nonneg fun e _ => ArithmeticFunction.vonMangoldt_nonneg
    have hsubset : E ⊆ (n / d).divisors := Finset.filter_subset _ _
    have hsum_full :
        (∑ e ∈ E, ArithmeticFunction.vonMangoldt e) ≤
          Real.log ((n / d : ℕ) : ℝ) := by
      calc
        (∑ e ∈ E, ArithmeticFunction.vonMangoldt e) ≤
            ∑ e ∈ (n / d).divisors, ArithmeticFunction.vonMangoldt e :=
          Finset.sum_le_sum_of_subset_of_nonneg hsubset
            (fun e _ _ => ArithmeticFunction.vonMangoldt_nonneg)
        _ = Real.log ((n / d : ℕ) : ℝ) := ArithmeticFunction.vonMangoldt_sum
    have hlog : Real.log ((n / d : ℕ) : ℝ) ≤ Real.log (N + 1 : ℕ) :=
      log_nat_le_log_succ hqpos ((Nat.div_le_self n d).trans hnN)
    calc
      |∑ e ∈ E,
          ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
            ArithmeticFunction.vonMangoldt e| =
          |((ArithmeticFunction.moebius d : ℤ) : ℝ)| *
            (∑ e ∈ E, ArithmeticFunction.vonMangoldt e) := by
              rw [← Finset.mul_sum, abs_mul, abs_of_nonneg hsum_nonneg]
      _ ≤ 1 * (∑ e ∈ E, ArithmeticFunction.vonMangoldt e) :=
        mul_le_mul_of_nonneg_right (moebius_cast_abs_le_one d) hsum_nonneg
      _ ≤ Real.log ((n / d : ℕ) : ℝ) := by simpa using hsum_full
      _ ≤ Real.log (N + 1 : ℕ) := hlog
  calc
    |∑ d ∈ D, ∑ e ∈ (n / d).divisors.filter (fun e => e ≤ v),
        ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
          ArithmeticFunction.vonMangoldt e|
        ≤ (D.card : ℝ) * Real.log (N + 1 : ℕ) :=
      abs_sum_bi_le_card_mul D _ _ houter
    _ ≤ (n.divisors.card : ℝ) * Real.log (N + 1 : ℕ) := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast Finset.card_filter_le n.divisors (fun d => d ≤ u)
      · exact Real.log_nonneg (by
          exact_mod_cast Nat.succ_le_succ (Nat.zero_le N))

/-- Uniform pointwise Type-I estimate obtained from the opened `μ * log` and
`μ * Λ` convolutions.  In particular it has no polynomial dependence on the
cutoffs `u,v`. -/
theorem vaughanTypeI_abs_le_two_divisors_mul_log
    {n N u v : ℕ} (hn : 0 < n) (hnN : n ≤ N) :
    |vaughanTypeI n u v| ≤
      2 * (n.divisors.card : ℝ) * Real.log (N + 1 : ℕ) := by
  rw [vaughanTypeI]
  calc
    |Sieve.vaughanFirst n u - Sieve.vaughanMiddle n u v| ≤
        |Sieve.vaughanFirst n u| + |Sieve.vaughanMiddle n u v| := abs_sub _ _
    _ ≤ (n.divisors.card : ℝ) * Real.log (N + 1 : ℕ) +
        (n.divisors.card : ℝ) * Real.log (N + 1 : ℕ) :=
      add_le_add (vaughanFirst_abs_le_divisors_mul_log hn hnN)
        (vaughanMiddle_abs_le_divisors_mul_log hn hnN)
    _ = 2 * (n.divisors.card : ℝ) * Real.log (N + 1 : ℕ) := by ring

/-- Pointwise square bound for the actual long-variable coefficient. -/
theorem vaughanTypeILongCoeff_norm_sq_le_divisor_sq
    (b : ℤ → ℂ) (N u v : ℕ) (B : ℝ) (n : ℤ)
    (hn : n ∈ Finset.Icc (1 : ℤ) N) (hB : ‖b n‖ ≤ B) :
    ‖vaughanTypeILongCoeff b u v n‖ ^ 2 ≤
      4 * B ^ 2 * (n.toNat.divisors.card : ℝ) ^ 2 *
        Real.log (N + 1 : ℕ) ^ 2 := by
  have hnpos : 0 < n := lt_of_lt_of_le Int.zero_lt_one (Finset.mem_Icc.mp hn).1
  have hntpos : 0 < n.toNat := by omega
  have hntN : n.toNat ≤ N := by
    have hcast : (n.toNat : ℤ) = n := Int.toNat_of_nonneg hnpos.le
    exact_mod_cast hcast.trans_le (Finset.mem_Icc.mp hn).2
  have hI := vaughanTypeI_abs_le_two_divisors_mul_log
    (n := n.toNat) (N := N) (u := u) (v := v) hntpos hntN
  unfold vaughanTypeILongCoeff
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow]
  have hb2 := pow_le_pow_left₀ (norm_nonneg (b n)) hB 2
  have hI2 := pow_le_pow_left₀ (abs_nonneg (vaughanTypeI n.toNat u v)) hI 2
  calc
    ‖b n‖ ^ 2 * |vaughanTypeI n.toNat u v| ^ 2 ≤
        B ^ 2 * (2 * (n.toNat.divisors.card : ℝ) *
          Real.log (N + 1 : ℕ)) ^ 2 :=
      mul_le_mul hb2 hI2 (sq_nonneg _) (sq_nonneg _)
    _ = 4 * B ^ 2 * (n.toNat.divisors.card : ℝ) ^ 2 *
        Real.log (N + 1 : ℕ) ^ 2 := by ring

/-- Explicit `N log^5(N+1)` moment bound.  The constant is
`4 * 27 = 108`; all dependence on `N,u,v` is displayed (and the estimate is
uniform in `u,v`). -/
theorem vaughanTypeILongCoeffMoment_le_explicit
    (b : ℤ → ℂ) (N u v : ℕ) (B : ℝ)
    (hB : ∀ n ∈ Finset.Icc (1 : ℤ) N, ‖b n‖ ≤ B) :
    vaughanTypeILongCoeffMoment b N u v ≤
      108 * B ^ 2 * (N : ℝ) * Real.log (N + 1 : ℕ) ^ 5 := by
  unfold vaughanTypeILongCoeffMoment
  let L : ℝ := Real.log (N + 1 : ℕ)
  calc
    (∑ n ∈ Finset.Icc (1 : ℤ) N, ‖vaughanTypeILongCoeff b u v n‖ ^ 2) ≤
        ∑ n ∈ Finset.Icc (1 : ℤ) N,
          4 * B ^ 2 * (n.toNat.divisors.card : ℝ) ^ 2 * L ^ 2 := by
      apply Finset.sum_le_sum
      intro n hn
      simpa [L] using vaughanTypeILongCoeff_norm_sq_le_divisor_sq
        b N u v B n hn (hB n hn)
    _ = 4 * B ^ 2 * L ^ 2 * divisorSquarePrefix N := by
      unfold divisorSquarePrefix
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      ring
    _ ≤ 4 * B ^ 2 * L ^ 2 *
        (27 * (N : ℝ) * L ^ 3) := by
      apply mul_le_mul_of_nonneg_left
      · exact divisorSquareMomentBound_27 N
      · positivity
    _ = 108 * B ^ 2 * (N : ℝ) * Real.log (N + 1 : ℕ) ^ 5 := by
      dsimp [L]
      ring

/-- Concrete inhabitant of the frozen Type-I coefficient-moment interface. -/
theorem vaughanTypeILongCoeffMomentBound_of_bounded
    (b : ℤ → ℂ) (N u v : ℕ) (B : ℝ)
    (hB : ∀ n ∈ Finset.Icc (1 : ℤ) N, ‖b n‖ ≤ B) :
    VaughanTypeILongCoeffMomentBound b N u v (108 * B ^ 2) 5 := by
  unfold VaughanTypeILongCoeffMomentBound
  simpa [mul_assoc] using vaughanTypeILongCoeffMoment_le_explicit b N u v B hB

/-- Premise-free-in-the-moment weighted primitive Type-I prefix-maximal bound.
The only coefficient assumption is the displayed finite `B`-bound; no analytic
moment hypothesis remains. -/
theorem weighted_primitive_vaughanTypeILong_unconditional
    (b : ℤ → ℂ) (N Q u v : ℕ) (B : ℝ) (hQ : 0 < Q)
    (hB : ∀ n ∈ Finset.Icc (1 : ℤ) N, ‖b n‖ ≤ B) :
    (∑ q ∈ Finset.Icc 1 Q,
      ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ : PrimitiveCharacter q,
          primitiveCharacterPrefixMaxSquare (vaughanTypeILongCoeff b u v) 0 N q χ) ≤
      (((Nat.log2 N + 1 : ℕ) : ℝ) ^ 2) *
        primitiveLargeSieveConstant N Q *
          ((108 * B ^ 2) * (N : ℝ) * Real.log (N + 1 : ℕ) ^ 5) := by
  exact weighted_primitive_vaughanTypeILong_of_moment
    b N Q u v (108 * B ^ 2) 5 hQ
      (vaughanTypeILongCoeffMomentBound_of_bounded b N u v B hB)

/-- The same unconditional result with the left side written as the exact
short-times-long rearranged Type-I prefixes. -/
theorem weighted_primitive_vaughanTypeILong_rearranged_unconditional
    (b : ℤ → ℂ) (N Q u v : ℕ) (B : ℝ) (hQ : 0 < Q)
    (hB : ∀ n ∈ Finset.Icc (1 : ℤ) N, ‖b n‖ ≤ B) :
    (∑ q ∈ Finset.Icc 1 Q,
      ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ : PrimitiveCharacter q,
          vaughanTypeILongPrefixMaxSquare b N u v q χ) ≤
      (((Nat.log2 N + 1 : ℕ) : ℝ) ^ 2) *
        primitiveLargeSieveConstant N Q *
          ((108 * B ^ 2) * (N : ℝ) * Real.log (N + 1 : ℕ) ^ 5) := by
  simpa only [← primitiveCharacterPrefixMaxSquare_typeI_eq_long] using
    weighted_primitive_vaughanTypeILong_unconditional b N Q u v B hQ hB

end

end AnalyticNumberTheory.LargeSieve
