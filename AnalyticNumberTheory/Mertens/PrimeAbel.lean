import AnalyticNumberTheory.Mertens.Basic
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Abel summation for the reciprocal-prime Dirichlet series

This file packages the general `LSeries_eq_mul_integral_of_nonneg` theorem for
the coefficient sequence which is `1 / p` at primes and zero elsewhere.  Its
partial sums are exactly `primeReciprocalSum`, so the resulting integral is a
direct Abel/Mellin bridge for Mertens' second theorem.
-/

namespace AnalyticNumberTheory.Mertens

open Filter Finset Real
open Asymptotics
open scoped Topology

/-- The reciprocal-prime coefficient sequence, extended by zero away from primes. -/
noncomputable def primeReciprocalCoeff (n : ℕ) : ℝ :=
  if n.Prime then 1 / (n : ℝ) else 0

theorem primeReciprocalCoeff_nonneg (n : ℕ) : 0 ≤ primeReciprocalCoeff n := by
  simp only [primeReciprocalCoeff]
  split_ifs <;> positivity

/--
Expanding the L-series shows explicitly that its exponent is shifted by one:
at `s = ε` this is the prime Dirichlet sum `∑ p, p ^ (-(1 + ε))`.
-/
theorem primeReciprocalLSeries_eq_primeDirichletSum (s : ℂ) :
    LSeries (fun n => primeReciprocalCoeff n) s =
      ∑' n : ℕ, if n.Prime then (n : ℂ) ^ (-(1 + s)) else 0 := by
  rw [LSeries_def₀ (s := s) (by simp [primeReciprocalCoeff])]
  apply tsum_congr
  intro n
  by_cases hn : n.Prime
  · simp only [primeReciprocalCoeff, hn, ↓reduceIte, div_eq_mul_inv, ← Complex.cpow_neg]
    push_cast
    rw [one_mul]
    rw [← Complex.cpow_neg_one, ← Complex.cpow_add _ _ (Nat.cast_ne_zero.mpr hn.ne_zero)]
    congr 2
    ring
  · simp [primeReciprocalCoeff, hn]

/-- The partial sums of `primeReciprocalCoeff` are the finite reciprocal-prime sums. -/
theorem sum_Icc_primeReciprocalCoeff (n : ℕ) :
    (∑ k ∈ Icc 1 n, primeReciprocalCoeff k) = primeReciprocalSum n := by
  unfold primeReciprocalCoeff primeReciprocalSum primesUpTo
  rw [← sum_filter]
  congr 1
  ext k
  simp only [mem_filter, mem_Icc, mem_range]
  constructor
  · rintro ⟨⟨_, hkn⟩, hkprime⟩
    exact ⟨Nat.lt_succ_of_le hkn, hkprime⟩
  · rintro ⟨hkn, hkprime⟩
    exact ⟨⟨hkprime.one_lt.le, Nat.le_of_lt_succ hkn⟩, hkprime⟩

theorem primeReciprocalSum_le_succ (n : ℕ) :
    primeReciprocalSum n ≤ (n + 1 : ℕ) := by
  unfold primeReciprocalSum
  calc
    (primesUpTo n).sum (fun p => 1 / (p : ℝ))
        ≤ (primesUpTo n).sum (fun _ => (1 : ℝ)) := by
          apply sum_le_sum
          intro p hp
          have hp0 : (0 : ℝ) < p := by
            exact_mod_cast (mem_primesUpTo.mp hp).1.pos
          rw [one_div]
          exact (inv_le_one₀ hp0).2 (by
            exact_mod_cast (mem_primesUpTo.mp hp).1.one_le)
    _ = ((primesUpTo n).card : ℝ) := by simp
    _ ≤ (n + 1 : ℕ) := by
      have hcard := card_le_card (show primesUpTo n ⊆ range (n + 1) by
        intro p hp
        exact mem_range.mpr (Nat.lt_succ_of_le (mem_primesUpTo.mp hp).2))
      have hcard' : (primesUpTo n).card ≤ n + 1 := by simpa using hcard
      exact_mod_cast hcard'

/-- The reciprocal-prime sum is bounded by the corresponding harmonic sum. -/
theorem primeReciprocalSum_le_one_add_log (n : ℕ) :
    primeReciprocalSum n ≤ 1 + Real.log n := by
  unfold primeReciprocalSum
  calc
    (primesUpTo n).sum (fun p => 1 / (p : ℝ)) ≤
        ∑ k ∈ Icc 1 n, 1 / (k : ℝ) := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro p hp
        rw [mem_Icc]
        exact ⟨(mem_primesUpTo.mp hp).1.one_le, (mem_primesUpTo.mp hp).2⟩
      · intro p _ _
        positivity
    _ = (harmonic n : ℝ) := by
      rw [harmonic_eq_sum_Icc]
      push_cast
      simp [one_div]
    _ ≤ 1 + Real.log n := harmonic_le_one_add_log n

/-- A coarse unconditional growth bound, sufficient for the half-plane `1 < re s`. -/
theorem primeReciprocalSum_isBigO_natCast :
    primeReciprocalSum =O[atTop] fun n : ℕ => (n : ℝ) := by
  rw [isBigO_iff]
  refine ⟨2, ?_⟩
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnonneg := primeReciprocalSum_nonneg n
  have hle := primeReciprocalSum_le_succ n
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg, Real.norm_eq_abs,
    abs_of_nonneg (Nat.cast_nonneg n)]
  exact hle.trans (by exact_mod_cast (show n + 1 ≤ 2 * n by omega))

/-- The reciprocal-prime sum grows more slowly than every positive real
power.  This elementary estimate extends the Abel bridge to `Re(s) > 0`. -/
theorem primeReciprocalSum_isBigO_rpow {r : ℝ} (hr : 0 < r) :
    primeReciprocalSum =O[atTop] fun n : ℕ => (n : ℝ) ^ r := by
  have hsumlog : primeReciprocalSum =O[atTop]
      fun n : ℕ => Real.log (n : ℝ) := by
    apply IsBigO.of_bound 2
    have hlogEvent : ∀ᶠ n : ℕ in atTop, 1 ≤ Real.log (n : ℝ) :=
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
        (eventually_ge_atTop 1)
    filter_upwards [hlogEvent] with n hlog1
    rw [Real.norm_eq_abs, abs_of_nonneg (primeReciprocalSum_nonneg n),
      Real.norm_eq_abs, abs_of_nonneg (le_trans zero_le_one hlog1)]
    calc
      primeReciprocalSum n ≤ 1 + Real.log n :=
        primeReciprocalSum_le_one_add_log n
      _ ≤ 2 * Real.log n := by linarith
  exact hsumlog.trans
    ((isLittleO_log_rpow_atTop hr).isBigO.comp_tendsto
      tendsto_natCast_atTop_atTop)

/--
An Abel/Mellin representation of the reciprocal-prime L-series.  The explicit
growth hypothesis is deliberately separated from the analytic identity: any
subsequent bound for `primeReciprocalSum` can be inserted here without changing
the bridge.
-/
theorem primeReciprocalLSeries_eq_mul_integral
    {r : ℝ} (hr : 0 ≤ r) {s : ℂ} (hs : r < s.re)
    (hO : primeReciprocalSum =O[atTop] fun n : ℕ => (n : ℝ) ^ r) :
    LSeries (fun n => primeReciprocalCoeff n) s =
      s * ∫ t in Set.Ioi (1 : ℝ),
        (primeReciprocalSum ⌊t⌋₊ : ℂ) * (t : ℂ) ^ (-(s + 1)) := by
  rw [LSeries_eq_mul_integral_of_nonneg primeReciprocalCoeff hr hs]
  · congr 1
    apply MeasureTheory.integral_congr_ae
    filter_upwards with t
    have hsum :
        (∑ k ∈ Icc 1 ⌊t⌋₊, (primeReciprocalCoeff k : ℂ)) =
          (primeReciprocalSum ⌊t⌋₊ : ℂ) := by
      exact_mod_cast sum_Icc_primeReciprocalCoeff ⌊t⌋₊
    rw [hsum]
  · simpa only [sum_Icc_primeReciprocalCoeff] using hO
  · exact primeReciprocalCoeff_nonneg

/--
The Abel/Mellin bridge written directly as a prime Dirichlet sum at exponent
`1 + s`.
-/
theorem primeDirichletSum_eq_mul_integral
    {r : ℝ} (hr : 0 ≤ r) {s : ℂ} (hs : r < s.re)
    (hO : primeReciprocalSum =O[atTop] fun n : ℕ => (n : ℝ) ^ r) :
    (∑' n : ℕ, if n.Prime then (n : ℂ) ^ (-(1 + s)) else 0) =
      s * ∫ t in Set.Ioi (1 : ℝ),
        (primeReciprocalSum ⌊t⌋₊ : ℂ) * (t : ℂ) ^ (-(s + 1)) := by
  rw [← primeReciprocalLSeries_eq_primeDirichletSum]
  exact primeReciprocalLSeries_eq_mul_integral hr hs hO

/-- The prime Dirichlet Abel formula in the full range needed at the pole:
every positive real displacement `ε` from `s = 1`. -/
theorem primeDirichletSum_eq_mul_integral_of_pos
    (ε : ℝ) (hε : 0 < ε) :
    (∑' n : ℕ, if n.Prime then (n : ℂ) ^ (-(1 + (ε : ℂ))) else 0) =
      (ε : ℂ) * ∫ t in Set.Ioi (1 : ℝ),
        (primeReciprocalSum ⌊t⌋₊ : ℂ) *
          (t : ℂ) ^ (-((ε : ℂ) + 1)) := by
  have hr : 0 ≤ ε / 2 := by linarith
  have hrs : ε / 2 < ((ε : ℂ)).re := by simp; linarith
  simpa [add_comm] using
    (primeDirichletSum_eq_mul_integral hr hrs
      (primeReciprocalSum_isBigO_rpow (by linarith : 0 < ε / 2)))

/-- Real prime-indexed form of the positive-displacement Abel formula. -/
theorem realPrimeDirichletSum_eq_mul_integral_of_pos
    (ε : ℝ) (hε : 0 < ε) :
    (↑(∑' p : Nat.Primes, (p : ℝ) ^ (-(1 + ε))) : ℂ) =
      (ε : ℂ) * ∫ t in Set.Ioi (1 : ℝ),
        (primeReciprocalSum ⌊t⌋₊ : ℂ) *
          (t : ℂ) ^ (-((ε : ℂ) + 1)) := by
  rw [Complex.ofReal_tsum]
  calc
    (∑' p : Nat.Primes, (↑((p : ℝ) ^ (-(1 + ε))) : ℂ)) =
        ∑' n : ℕ, if n.Prime then (n : ℂ) ^ (-(1 + (ε : ℂ))) else 0 := by
      change (∑' p : ↑({n : ℕ | n.Prime} : Set ℕ),
        (↑((p : ℝ) ^ (-(1 + ε))) : ℂ)) = _
      rw [_root_.tsum_subtype {n : ℕ | n.Prime}
        (fun n : ℕ => (↑((n : ℝ) ^ (-(1 + ε))) : ℂ))]
      apply tsum_congr
      intro n
      simp only [Set.indicator, Set.mem_ofPred_eq]
      split_ifs
      · rw [Complex.ofReal_cpow (Nat.cast_nonneg n)]
        simp
      · rfl
    _ = _ := primeDirichletSum_eq_mul_integral_of_pos ε hε

/--
An unconditional specialization of the Abel/Mellin bridge.  Its coarse growth
proof only gives `1 < re s`; sharper Mertens bounds can instead be supplied to
`primeReciprocalLSeries_eq_mul_integral` to reach every positive real part.
-/
theorem primeReciprocalLSeries_eq_mul_integral_of_one_lt_re
    {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => primeReciprocalCoeff n) s =
      s * ∫ t in Set.Ioi (1 : ℝ),
        (primeReciprocalSum ⌊t⌋₊ : ℂ) * (t : ℂ) ^ (-(s + 1)) := by
  have hO : primeReciprocalSum =O[atTop] fun n : ℕ => (n : ℝ) ^ (1 : ℝ) := by
    simpa only [Real.rpow_one] using primeReciprocalSum_isBigO_natCast
  exact primeReciprocalLSeries_eq_mul_integral zero_le_one hs hO

end AnalyticNumberTheory.Mertens
