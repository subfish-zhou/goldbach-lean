import AnalyticNumberTheory.Sieve.PanMeanValueBody
import AnalyticNumberTheory.LargeSieve.Multiplicative
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic

/-! # AnalyticNumberTheory.Sieve.PanV1SquareMean

## Type I square-sum bounds and per-modulus large-sieve reduction

This module proves two components relevant to
`panTypeICharMeanSieveBound` and `PanTypeICharacterMeanValue`
(`PanMeanValueBody.lean` §§5--5.1):

1. **Elementary square-sum bound**:
   `Σ_{n≤N} vaughanFirst(n,u)² ≤ N·(1+log(N+1))⁵`.
   First use `|vaughanFirst(n,u)| ≤ τ(n)·log(n+1)`,
   where `τ(n) = n.divisors.card` and `|μ(d)| ≤ 1`.
   Double counting gives
   `Σ_{n≤N} τ(n)² = Σ_{d,e≤N} ⌊N/lcm(d,e)⌋`.
   Then `gcd·lcm = de` and `gcd = Σ_{g|gcd} φ(g)` reduce
   the reciprocal-lcm sum to
   `Σ_g (φ(g)/g²)·H(N/g)² ≤ (1+log(N+1))³`.
   Harmonic estimates come from `Mathlib.NumberTheory.Harmonic`.
2. **Per-modulus character square-sum bound**:
   `Σ_χ ‖V_χ(m)‖²
    ≤ (φ(q)/q)·largeSieveBound(m+1,1/q²)·Σ_{n≤m} vaughanFirst(n,u)²`.
   Combine `characterSieveModulus_le` with `largeSieveRationalPoints`,
   then replace the `y`-maximum by a sum to obtain
   `panTypeICharSqrtMeanMaxY_le_sieveSqrtSum`.

These are per-modulus bounds, not a proof of the all-character
`panTypeICharSquareMeanBound` summed over `q ≤ Q`.
The classical Bombieri--Davenport argument uses primitive characters
and Gauss sums `|τ(χ)|² = q`; an all-character extension requires
additional control. The final bound here leaves only the additive
large-sieve constant, the `vaughanFirst` L² sum, and the outer
`(y,a)` weights.
-/

namespace AnalyticNumberTheory.Sieve

open Finset Real

open AnalyticNumberTheory.LargeSieve

open scoped Classical
open scoped ArithmeticFunction
open scoped ArithmeticFunction.Moebius

noncomputable section

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

/-! ## 1. Elementary pointwise bound for vaughanFirst -/

/-- `μ(d) ∈ {-1, 0, 1}`: `|μ d| ≤ 1`. -/
lemma moebius_abs_le_one (d : ℕ) : |((μ d : ℤ) : ℝ)| ≤ 1 := by
  by_cases h : Squarefree d
  · have hμ : (μ d : ℤ) = (-1 : ℤ) ^ ArithmeticFunction.cardFactors d := by
      unfold ArithmeticFunction.moebius
      simp [h]
    rw [hμ]
    have hpow : |(((-1 : ℤ) ^ ArithmeticFunction.cardFactors d : ℤ) : ℝ)| = 1 := by
      rw [← Int.cast_abs, abs_pow, abs_neg, abs_one]
      norm_num
    rw [hpow]
  · have hμ : (μ d : ℤ) = 0 := ArithmeticFunction.moebius_eq_zero_of_not_squarefree h
    rw [hμ]
    norm_num

/-- `vaughanFirst 0 u = 0` (`0.divisors = ∅`). -/
lemma vaughanFirst_zero (u : ℕ) : vaughanFirst 0 u = 0 := by
  unfold vaughanFirst
  simp [Nat.divisors_zero]

/-- **Pointwise bound**:
`|vaughanFirst(n,u)| ≤ τ(n)·log(n+1)`, with
`τ(n) = n.divisors.card`. The case `n = 0` is trivial because
`vaughanFirst 0 u = 0`. -/
lemma vaughanFirst_abs_le (n u : ℕ) :
    |vaughanFirst n u| ≤ (n.divisors.card : ℝ) * Real.log (n + 1) := by
  by_cases hn : n = 0
  · subst n
    simp [vaughanFirst_zero]
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    let s : Finset ℕ := n.divisors.filter (fun d => d ≤ u)
    have hterm : ∀ d ∈ s,
        |((μ d : ℤ) : ℝ) * Real.log ((n / d : ℕ) : ℝ)| ≤ Real.log (n + 1) := by
      intro d hd
      have hdmem : d ∈ n.divisors := (Finset.mem_filter.mp hd).1
      have hdn : d ∣ n := (Nat.mem_divisors.mp hdmem).1
      have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdn hnpos
      have hnd : 1 ≤ n / d := Nat.div_pos (Nat.le_of_dvd hnpos hdn) hdpos
      have hlog_nonneg : 0 ≤ Real.log ((n / d : ℕ) : ℝ) :=
        Real.log_nonneg (by exact_mod_cast hnd)
      have hlog_le : Real.log ((n / d : ℕ) : ℝ) ≤ Real.log (n + 1) := by
        apply Real.log_le_log
        · exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 1) hnd)
        · exact_mod_cast (le_trans (Nat.div_le_self n d) (Nat.le_succ n))
      calc
        |((μ d : ℤ) : ℝ) * Real.log ((n / d : ℕ) : ℝ)|
            = |((μ d : ℤ) : ℝ)| * |Real.log ((n / d : ℕ) : ℝ)| := abs_mul _ _
        _ = |((μ d : ℤ) : ℝ)| * Real.log ((n / d : ℕ) : ℝ) := by
              rw [abs_of_nonneg hlog_nonneg]
        _ ≤ (1 : ℝ) * Real.log ((n : ℝ) + 1) := by
              exact mul_le_mul (moebius_abs_le_one d) hlog_le hlog_nonneg (by norm_num)
        _ = Real.log (n + 1) := by simp
    calc
      |vaughanFirst n u| ≤ ∑ d ∈ s, |((μ d : ℤ) : ℝ) * Real.log ((n / d : ℕ) : ℝ)| := by
            unfold vaughanFirst s
            exact Finset.abs_sum_le_sum_abs
              (fun d => ((μ d : ℤ) : ℝ) * Real.log ((n / d : ℕ) : ℝ))
              (n.divisors.filter (fun d => d ≤ u))
      _ ≤ ∑ d ∈ s, Real.log (n + 1) := by
            exact Finset.sum_le_sum (fun d hd => hterm d hd)
      _ = (s.card : ℝ) * Real.log (n + 1) := by
            simp [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (n.divisors.card : ℝ) * Real.log (n + 1) := by
            have hc : s.card ≤ n.divisors.card :=
              Finset.card_le_card (Finset.filter_subset (fun d => d ≤ u) n.divisors)
            have hlog : 0 ≤ Real.log (n + 1) := by
              have h1 : 1 ≤ n + 1 := by omega
              exact Real.log_nonneg (by exact_mod_cast h1)
            exact mul_le_mul_of_nonneg_right (by exact_mod_cast hc) hlog

/-! ## 2. Harmonic sums and multiple counts for the τ² estimate -/

/-- Harmonic bound `Σ_{k=1}^{M} 1/k ≤ 1+log(M+1)`,
a consequence of mathlib's harmonic-sum estimates. -/
lemma harmonic_Icc_le (M : ℕ) :
    (∑ k ∈ Finset.Icc 1 M, (1 : ℝ) / (k : ℝ)) ≤ 1 + Real.log (M + 1) := by
  have h1 : (∑ k ∈ Finset.Icc 1 M, (1 : ℝ) / (k : ℝ)) = (harmonic M : ℝ) := by
    rw [harmonic_eq_sum_Icc]
    simp [one_div]
  calc
    (∑ k ∈ Finset.Icc 1 M, (1 : ℝ) / (k : ℝ)) = (harmonic M : ℝ) := h1
    _ ≤ 1 + Real.log (M : ℝ) := harmonic_le_one_add_log M
    _ ≤ 1 + Real.log (M + 1) := by
          by_cases hM0 : M = 0
          · subst M
            simp
          · have hMpos : 0 < (M : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hM0)
            have hMle : (M : ℝ) ≤ (M + 1 : ℝ) := by norm_num
            exact add_le_add (le_refl (1 : ℝ)) (Real.log_le_log hMpos hMle)

/-- Multiple count: `#{n ∈ Icc 1 N : m | n} = N/m` for `m ≥ 1`. -/
lemma card_multiples_Icc (N m : ℕ) (hm : 1 ≤ m) :
    ((Finset.Icc 1 N).filter (fun n => m ∣ n)).card = N / m := by
  have hc := Nat.card_multiples N m
  have hbij : ((Finset.range N).filter (fun e => m ∣ e + 1)).card =
      ((Finset.Icc 1 N).filter (fun n => m ∣ n)).card := by
    apply Finset.card_bij (s := (Finset.range N).filter (fun e => m ∣ e + 1))
      (t := (Finset.Icc 1 N).filter (fun n => m ∣ n))
      (i := fun e _ => e + 1)
    · intro e he
      rw [Finset.mem_filter] at he
      rw [Finset.mem_filter]
      constructor
      · rw [Finset.mem_Icc]
        have he' : e < N := (Finset.mem_range.mp he.1)
        constructor <;> omega
      · exact he.2
    · intro a ha b hb h
      omega
    · intro n hn
      rw [Finset.mem_filter] at hn
      rcases hn with ⟨hnIcc, hmn⟩
      refine ⟨n - 1, ?_, ?_⟩
      · rw [Finset.mem_filter]
        constructor
        · rw [Finset.mem_range]
          have h1 : 1 ≤ n := (Finset.mem_Icc.mp hnIcc).1
          have hN : n ≤ N := (Finset.mem_Icc.mp hnIcc).2
          omega
        · have h1 : 1 ≤ n := (Finset.mem_Icc.mp hnIcc).1
          simpa [Nat.sub_add_cancel h1] using hmn
      · have h1 : 1 ≤ n := (Finset.mem_Icc.mp hnIcc).1
        omega
  rw [← hbij, hc]

/-! ## 3. Reciprocal-lcm sums and Σ_{n≤N} τ(n)² ≤ N·(1+log(N+1))³ -/

/-- `1/lcm(d,e) = gcd(d,e)/(d·e)` in `ℝ`, for `d,e ≥ 1`. -/
private lemma lcm_inv_eq_gcd_div {d e : ℕ} (hd : 1 ≤ d) (he : 1 ≤ e) :
    (1 : ℝ) / (Nat.lcm d e : ℝ) = (Nat.gcd d e : ℝ) / ((d : ℝ) * (e : ℝ)) := by
  have hgmul : (Nat.gcd d e : ℝ) * (Nat.lcm d e : ℝ) = (d : ℝ) * (e : ℝ) := by
    exact_mod_cast (Nat.gcd_mul_lcm d e)
  have hne_d : (d : ℝ) ≠ 0 := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 1) hd).ne'
  have hne_e : (e : ℝ) ≠ 0 := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 1) he).ne'
  have hne_g : (Nat.gcd d e : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.gcd_pos_of_pos_left e (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 1) hd)).ne'
  have hne_l : (Nat.lcm d e : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.lcm_pos (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 1) hd)
      (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 1) he)).ne'
  field_simp [hne_d, hne_e, hne_g, hne_l]
  rw [mul_comm (Nat.lcm d e : ℝ)]
  exact hgmul.symm

/-- **Double reciprocal-lcm sum**:
`Σ_{d,e≤N} 1/lcm(d,e) ≤ (1+log(N+1))³`.
Use `lcm = de/gcd` and `gcd(d,e) = Σ_{g|d, g|e} φ(g)` to write
`Σ_{d,e} 1/lcm(d,e) = Σ_{g≤N} (φ(g)/g²)·(Σ_{d'≤N/g} 1/d')²`.
This is at most
`(1+log(N+1))²·Σ_{g≤N} φ(g)/g²
 ≤ (1+log(N+1))²·Σ_{g≤N} 1/g ≤ (1+log(N+1))³`. -/
lemma lcm_inv_sum_le (N : ℕ) :
    (∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 N, (1 : ℝ) / (Nat.lcm d e : ℝ)) ≤
      (1 + Real.log (N + 1)) ^ 3 := by
  -- Uniform harmonic bound: for M ≤ N, H(M) ≤ 1+log(N+1).
  have hH : ∀ M : ℕ, M ≤ N →
      (∑ k ∈ Finset.Icc 1 M, (1 : ℝ) / (k : ℝ)) ≤ 1 + Real.log (N + 1) := by
    intro M hMN
    calc
      (∑ k ∈ Finset.Icc 1 M, (1 : ℝ) / (k : ℝ)) ≤ 1 + Real.log (M + 1) := harmonic_Icc_le M
      _ ≤ 1 + Real.log (N + 1) := by
            have hle : M + 1 ≤ N + 1 := Nat.succ_le_succ hMN
            have hpos : 0 < (M + 1 : ℕ) := Nat.succ_pos M
            exact add_le_add (le_refl (1 : ℝ))
              (Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast hle))
  -- 1/lcm(d,e) = gcd(d,e)/(de)
  have hstep1 : (∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 N, (1 : ℝ) / (Nat.lcm d e : ℝ)) =
      (∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 N, (Nat.gcd d e : ℝ) / ((d : ℝ) * (e : ℝ))) := by
    apply Finset.sum_congr rfl
    intro d hd
    apply Finset.sum_congr rfl
    intro e he
    exact lcm_inv_eq_gcd_div (Finset.mem_Icc.mp hd).1 (Finset.mem_Icc.mp he).1
  -- gcd(d,e) = Σ_{g | gcd d e} φ(g) (Nat.sum_totient)
  have htot : ∀ d e : ℕ,
      (Nat.gcd d e : ℝ) = ∑ g ∈ (Nat.gcd d e).divisors, (Nat.totient g : ℝ) := by
    intro d e
    conv_lhs => rw [← Nat.sum_totient (Nat.gcd d e)]
    rw [Nat.cast_sum]
  have hstep2 : (∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 N, (Nat.gcd d e : ℝ) / ((d : ℝ) * (e : ℝ))) =
      (∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 N,
        ∑ g ∈ (Nat.gcd d e).divisors, (Nat.totient g : ℝ) / ((d : ℝ) * (e : ℝ))) := by
    apply Finset.sum_congr rfl
    intro d hd
    apply Finset.sum_congr rfl
    intro e he
    rw [htot d e, Finset.sum_div]
  -- Reindex using g | gcd d e iff g | d and g | e, then sum over g first.
  have hstep3 : (∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 N,
        ∑ g ∈ (Nat.gcd d e).divisors, (Nat.totient g : ℝ) / ((d : ℝ) * (e : ℝ))) =
      (∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 N,
        ∑ g ∈ Finset.Icc 1 N, (if g ∣ d ∧ g ∣ e then
          (Nat.totient g : ℝ) / ((d : ℝ) * (e : ℝ)) else 0)) := by
    apply Finset.sum_congr rfl
    intro d hd
    apply Finset.sum_congr rfl
    intro e he
    have hset : (Nat.gcd d e).divisors =
        (Finset.Icc 1 N).filter (fun g => g ∣ d ∧ g ∣ e) := by
      ext g
      constructor
      · intro hgm
        rw [Finset.mem_filter, Finset.mem_Icc]
        rw [Nat.mem_divisors] at hgm
        rcases hgm with ⟨hgcd, hg0⟩
        have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
        have he1 : 1 ≤ e := (Finset.mem_Icc.mp he).1
        have hgpos : 0 < g := Nat.pos_of_dvd_of_pos hgcd
          (Nat.gcd_pos_of_pos_left e (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 1) hd1))
        have hgN : g ≤ N := le_trans (Nat.le_of_dvd (Nat.gcd_pos_of_pos_left e
          (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 1) hd1)) hgcd)
          (le_trans (Nat.le_of_dvd (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 1) hd1)
            (Nat.gcd_dvd_left d e)) (Finset.mem_Icc.mp hd).2)
        refine ⟨⟨hgpos, hgN⟩, ?_⟩
        exact ⟨dvd_trans hgcd (Nat.gcd_dvd_left d e), dvd_trans hgcd (Nat.gcd_dvd_right d e)⟩
      · intro hgm
        rw [Finset.mem_filter, Finset.mem_Icc] at hgm
        rcases hgm with ⟨⟨hg1, hgN⟩, hgde⟩
        rw [Nat.mem_divisors]
        constructor
        · exact Nat.dvd_gcd hgde.1 hgde.2
        · exact (Nat.gcd_pos_of_pos_left e (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 1)
            (Finset.mem_Icc.mp hd).1)).ne'
    rw [← Finset.sum_filter (s := Finset.Icc 1 N) (p := fun g => g ∣ d ∧ g ∣ e)
      (f := fun g => (Nat.totient g : ℝ) / ((d : ℝ) * (e : ℝ)))]
    rw [hset]
  -- Exchange the order of summation.
  have hstep4 : (∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 N,
        ∑ g ∈ Finset.Icc 1 N, (if g ∣ d ∧ g ∣ e then
          (Nat.totient g : ℝ) / ((d : ℝ) * (e : ℝ)) else 0)) =
      (∑ g ∈ Finset.Icc 1 N, ∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 N,
        (if g ∣ d ∧ g ∣ e then (Nat.totient g : ℝ) / ((d : ℝ) * (e : ℝ)) else 0)) := by
    let F : ℕ → ℕ → ℕ → ℝ := fun d e g =>
      if g ∣ d ∧ g ∣ e then (Nat.totient g : ℝ) / ((d : ℝ) * (e : ℝ)) else 0
    have hswap1 : (∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 N, ∑ g ∈ Finset.Icc 1 N, F d e g) =
        (∑ d ∈ Finset.Icc 1 N, ∑ g ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 N, F d e g) := by
      apply Finset.sum_congr rfl
      intro d hd
      exact Finset.sum_comm (s := Finset.Icc 1 N) (t := Finset.Icc 1 N) (f := fun e g => F d e g)
    have hswap2 : (∑ d ∈ Finset.Icc 1 N, ∑ g ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 N, F d e g) =
        (∑ g ∈ Finset.Icc 1 N, ∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 N, F d e g) := by
      exact Finset.sum_comm (s := Finset.Icc 1 N) (t := Finset.Icc 1 N)
        (f := fun d g => ∑ e ∈ Finset.Icc 1 N, F d e g)
    exact hswap1.trans hswap2
  -- For fixed g, factor the expression and sum over multiples.
  have hfixed : ∀ g : ℕ, g ∈ Finset.Icc 1 N →
      (∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 N,
        (if g ∣ d ∧ g ∣ e then (Nat.totient g : ℝ) / ((d : ℝ) * (e : ℝ)) else 0)) =
      (Nat.totient g : ℝ) / (g : ℝ) ^ 2 *
        (∑ d ∈ Finset.Icc 1 (N / g), (1 : ℝ) / (d : ℝ)) *
        (∑ e ∈ Finset.Icc 1 (N / g), (1 : ℝ) / (e : ℝ)) := by
    intro g hg
    have hg1 : 1 ≤ g := (Finset.mem_Icc.mp hg).1
    have hgpos : 0 < (g : ℝ) := by exact_mod_cast hg1
    -- Factor: if g|d and g|e then φ(g)/(de) else 0 = φ(g)·(if g|d then 1/d else 0)·(if g|e then 1/e else 0).
    have hfac : ∀ d e : ℕ, 1 ≤ d → 1 ≤ e →
        (if g ∣ d ∧ g ∣ e then (Nat.totient g : ℝ) / ((d : ℝ) * (e : ℝ)) else 0) =
          (Nat.totient g : ℝ) * (if g ∣ d then (1 : ℝ) / (d : ℝ) else 0) *
            (if g ∣ e then (1 : ℝ) / (e : ℝ) else 0) := by
      intro d e hd he
      by_cases hgd : g ∣ d <;> by_cases hge : g ∣ e <;> simp [hgd, hge]
      · field_simp [show (d : ℝ) ≠ 0 by exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 1) hd).ne',
          show (e : ℝ) ≠ 0 by exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 1) he).ne']
    -- For fixed g, Σ_{d≤N, g|d} 1/d = (1/g)·H(N/g).
    have hmultiples : ∀ g : ℕ, 1 ≤ g →
        (∑ d ∈ Finset.Icc 1 N, (if g ∣ d then (1 : ℝ) / (d : ℝ) else 0)) =
          (1 : ℝ) / (g : ℝ) * (∑ d ∈ Finset.Icc 1 (N / g), (1 : ℝ) / (d : ℝ)) := by
      intro g hg1
      have hg1pos : 0 < g := hg1
      rw [← Finset.sum_filter (s := Finset.Icc 1 N) (p := fun d => g ∣ d)
        (f := fun d => (1 : ℝ) / (d : ℝ))]
      calc
        (∑ d ∈ (Finset.Icc 1 N).filter (fun d => g ∣ d), (1 : ℝ) / (d : ℝ))
            = ∑ d' ∈ Finset.Icc 1 (N / g), (1 : ℝ) / ((g * d' : ℕ) : ℝ) := by
                apply Finset.sum_bij (s := (Finset.Icc 1 N).filter (fun d => g ∣ d))
                  (t := Finset.Icc 1 (N / g))
                  (f := fun d => (1 : ℝ) / (d : ℝ))
                  (g := fun d' => (1 : ℝ) / ((g * d' : ℕ) : ℝ))
                  (i := fun d _ => d / g)
                · intro d hd
                  rw [Finset.mem_filter] at hd
                  rcases hd with ⟨hdIcc, hgd⟩
                  rw [Finset.mem_Icc]
                  constructor
                  · -- 1 ≤ d/g
                    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hdIcc).1
                    exact Nat.div_pos (Nat.le_of_dvd (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 1) hd1) hgd) hg1pos
                  · -- d/g ≤ N/g
                    exact Nat.div_le_div_right (Finset.mem_Icc.mp hdIcc).2
                · intro a ha b hb h
                  have hga : g ∣ a := (Finset.mem_filter.mp ha).2
                  have hgb : g ∣ b := (Finset.mem_filter.mp hb).2
                  calc
                    a = g * (a / g) := (Nat.mul_div_cancel' hga).symm
                    _ = g * (b / g) := by rw [h]
                    _ = b := Nat.mul_div_cancel' hgb
                · intro d' hd'
                  rw [Finset.mem_Icc] at hd'
                  rcases hd' with ⟨hd'1, hd'N⟩
                  refine ⟨g * d', ?_, ?_⟩
                  · rw [Finset.mem_filter]
                    constructor
                    · rw [Finset.mem_Icc]
                      constructor
                      · exact le_trans hg1 (Nat.le_mul_of_pos_right g (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 1) hd'1))
                      · -- g·d' ≤ N
                        have hle : d' * g ≤ N := (Nat.le_div_iff_mul_le hg1pos).mp hd'N
                        simpa [Nat.mul_comm] using hle
                    · exact dvd_mul_right g d'
                  · -- (g·d')/g = d'
                    exact Nat.mul_div_right d' hg1pos
                · intro d hd
                  have hgd : g ∣ d := (Finset.mem_filter.mp hd).2
                  rw [Nat.mul_div_cancel' hgd]
        _ = (1 : ℝ) / (g : ℝ) * (∑ d ∈ Finset.Icc 1 (N / g), (1 : ℝ) / (d : ℝ)) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro d hd
              have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
              field_simp [hgpos.ne',
                show (d : ℝ) ≠ 0 by exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 1) hd1).ne']
              rw [Nat.cast_mul]
    calc
      (∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 N,
          (if g ∣ d ∧ g ∣ e then (Nat.totient g : ℝ) / ((d : ℝ) * (e : ℝ)) else 0))
          = (∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 N,
              (Nat.totient g : ℝ) * (if g ∣ d then (1 : ℝ) / (d : ℝ) else 0) *
                (if g ∣ e then (1 : ℝ) / (e : ℝ) else 0)) := by
            apply Finset.sum_congr rfl
            intro d hd
            apply Finset.sum_congr rfl
            intro e he
            exact hfac d e (Finset.mem_Icc.mp hd).1 (Finset.mem_Icc.mp he).1
      _ = (Nat.totient g : ℝ) *
            (∑ d ∈ Finset.Icc 1 N, (if g ∣ d then (1 : ℝ) / (d : ℝ) else 0)) *
            (∑ e ∈ Finset.Icc 1 N, (if g ∣ e then (1 : ℝ) / (e : ℝ) else 0)) := by
            -- Factor the double sum: Σ_d Σ_e (φ·B_d·C_e) = φ·(Σ_d B_d)·(Σ_e C_e).
            let B : ℕ → ℝ := fun d => if g ∣ d then (1 : ℝ) / (d : ℝ) else 0
            let C : ℕ → ℝ := fun e => if g ∣ e then (1 : ℝ) / (e : ℝ) else 0
            calc
              (∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 N, ((Nat.totient g : ℝ) * B d) * C e)
                  = ∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 N, (Nat.totient g : ℝ) * (B d * C e) := by
                    apply Finset.sum_congr rfl
                    intro d hd
                    apply Finset.sum_congr rfl
                    intro e he
                    ring
              _ = (Nat.totient g : ℝ) * (∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 N, B d * C e) := by
                    rw [Finset.mul_sum]
                    apply Finset.sum_congr rfl
                    intro d hd
                    rw [Finset.mul_sum]
              _ = (Nat.totient g : ℝ) * ((∑ d ∈ Finset.Icc 1 N, B d) * (∑ e ∈ Finset.Icc 1 N, C e)) := by
                    congr 1
                    calc
                      (∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 N, B d * C e)
                          = ∑ d ∈ Finset.Icc 1 N, B d * (∑ e ∈ Finset.Icc 1 N, C e) := by
                                apply Finset.sum_congr rfl
                                intro d hd
                                rw [← Finset.mul_sum (s := Finset.Icc 1 N) (f := fun e => C e) (a := B d)]
                      _ = (∑ d ∈ Finset.Icc 1 N, B d) * (∑ e ∈ Finset.Icc 1 N, C e) := by
                                rw [← Finset.sum_mul (s := Finset.Icc 1 N) (f := fun d => B d)
                                  (a := (∑ e ∈ Finset.Icc 1 N, C e))]
              _ = ((Nat.totient g : ℝ) * ∑ d ∈ Finset.Icc 1 N, B d) * (∑ e ∈ Finset.Icc 1 N, C e) := by ring
      _ = (Nat.totient g : ℝ) / (g : ℝ) ^ 2 *
            (∑ d ∈ Finset.Icc 1 (N / g), (1 : ℝ) / (d : ℝ)) *
            (∑ e ∈ Finset.Icc 1 (N / g), (1 : ℝ) / (e : ℝ)) := by
            rw [hmultiples g hg1]
            field_simp [hgpos.ne']
  -- Combine: Σ_g (φ(g)/g²)·H(N/g)² ≤ (1+log(N+1))²·Σ_g 1/g ≤ (1+log(N+1))³.
  calc
    (∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 N, (1 : ℝ) / (Nat.lcm d e : ℝ))
    = (∑ g ∈ Finset.Icc 1 N, ∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 N,
        (if g ∣ d ∧ g ∣ e then (Nat.totient g : ℝ) / ((d : ℝ) * (e : ℝ)) else 0)) := by
          rw [hstep1, hstep2, hstep3, hstep4]
    _ = (∑ g ∈ Finset.Icc 1 N, (Nat.totient g : ℝ) / (g : ℝ) ^ 2 *
        (∑ d ∈ Finset.Icc 1 (N / g), (1 : ℝ) / (d : ℝ)) *
        (∑ e ∈ Finset.Icc 1 (N / g), (1 : ℝ) / (e : ℝ))) := by
          apply Finset.sum_congr rfl
          intro g hg
          exact hfixed g hg
    _ ≤ (∑ g ∈ Finset.Icc 1 N, (1 : ℝ) / (g : ℝ) * (1 + Real.log (N + 1)) ^ 2) := by
          apply Finset.sum_le_sum
          intro g hg
          have hg1 : 1 ≤ g := (Finset.mem_Icc.mp hg).1
          have hHg : (∑ d ∈ Finset.Icc 1 (N / g), (1 : ℝ) / (d : ℝ)) ≤ 1 + Real.log (N + 1) :=
            hH (N / g) (Nat.div_le_self N g)
          have hphi : (Nat.totient g : ℝ) / (g : ℝ) ^ 2 ≤ (1 : ℝ) / (g : ℝ) := by
            have htg : Nat.totient g ≤ g := Nat.totient_le g
            have hgpos : 0 < (g : ℝ) := by exact_mod_cast hg1
            calc
              (Nat.totient g : ℝ) / (g : ℝ) ^ 2 ≤ (g : ℝ) / (g : ℝ) ^ 2 := by
                    exact div_le_div_of_nonneg_right (by exact_mod_cast htg) (sq_nonneg _)
              _ = (1 : ℝ) / (g : ℝ) := by field_simp [hgpos.ne']
          have h1 : (Nat.totient g : ℝ) / (g : ℝ) ^ 2 * (1 + Real.log (N + 1)) ^ 2 ≤
              (1 : ℝ) / (g : ℝ) * (1 + Real.log (N + 1)) ^ 2 := by
            exact mul_le_mul_of_nonneg_right hphi (sq_nonneg _)
          calc
            (Nat.totient g : ℝ) / (g : ℝ) ^ 2 *
                (∑ d ∈ Finset.Icc 1 (N / g), (1 : ℝ) / (d : ℝ)) *
                (∑ e ∈ Finset.Icc 1 (N / g), (1 : ℝ) / (e : ℝ))
                ≤ (Nat.totient g : ℝ) / (g : ℝ) ^ 2 * (1 + Real.log (N + 1)) ^ 2 := by
                      -- Both harmonic factors are nonnegative and at most 1+log(N+1).
                      have hcoef : 0 ≤ (Nat.totient g : ℝ) / (g : ℝ) ^ 2 := by positivity
                      have hHnonneg : 0 ≤ (∑ d ∈ Finset.Icc 1 (N / g), (1 : ℝ) / (d : ℝ)) := by
                        exact Finset.sum_nonneg (fun _ _ => div_nonneg zero_le_one (by positivity))
                      have hclog : 0 ≤ 1 + Real.log (N + 1) := by
                        have hlog : 0 ≤ Real.log (N + 1) :=
                          Real.log_nonneg (by exact_mod_cast (show 1 ≤ N + 1 by omega))
                        linarith
                      have hHmul : (∑ d ∈ Finset.Icc 1 (N / g), (1 : ℝ) / (d : ℝ)) *
                            (∑ e ∈ Finset.Icc 1 (N / g), (1 : ℝ) / (e : ℝ)) ≤
                          (1 + Real.log (N + 1)) * (1 + Real.log (N + 1)) := by
                        exact mul_le_mul hHg hHg hHnonneg hclog
                      calc
                        (Nat.totient g : ℝ) / (g : ℝ) ^ 2 *
                            (∑ d ∈ Finset.Icc 1 (N / g), (1 : ℝ) / (d : ℝ)) *
                            (∑ e ∈ Finset.Icc 1 (N / g), (1 : ℝ) / (e : ℝ))
                            = (Nat.totient g : ℝ) / (g : ℝ) ^ 2 *
                              ((∑ d ∈ Finset.Icc 1 (N / g), (1 : ℝ) / (d : ℝ)) *
                                (∑ e ∈ Finset.Icc 1 (N / g), (1 : ℝ) / (e : ℝ))) := by ring
                        _ ≤ (Nat.totient g : ℝ) / (g : ℝ) ^ 2 *
                              ((1 + Real.log (N + 1)) * (1 + Real.log (N + 1))) := by
                              exact mul_le_mul_of_nonneg_left hHmul hcoef
                        _ = (Nat.totient g : ℝ) / (g : ℝ) ^ 2 * (1 + Real.log (N + 1)) ^ 2 := by
                              rw [← pow_two]
            _ ≤ (1 : ℝ) / (g : ℝ) * (1 + Real.log (N + 1)) ^ 2 := h1
    _ = (1 + Real.log (N + 1)) ^ 2 * (∑ g ∈ Finset.Icc 1 N, (1 : ℝ) / (g : ℝ)) := by
          rw [← Finset.sum_mul (s := Finset.Icc 1 N)
            (f := fun g => (1 : ℝ) / (g : ℝ)) (a := (1 + Real.log (N + 1)) ^ 2)]
          ring
    _ ≤ (1 + Real.log (N + 1)) ^ 2 * (1 + Real.log (N + 1)) := by
          exact mul_le_mul_of_nonneg_left (harmonic_Icc_le N) (sq_nonneg _)
    _ = (1 + Real.log (N + 1)) ^ 3 := by ring

/-! ## 4. Summing τ(n)² up to N -/

/-- **Divisor square-sum bound**:
`Σ_{n≤N} τ(n)² ≤ N·(1+log(N+1))³`.
Double count `τ(n)² = #{(d,e) : d|n, e|n}` and exchange sums:
`Σ_{n≤N} τ(n)² = Σ_{d,e≤N} ⌊N/lcm(d,e)⌋`. -/
lemma divisorCountSq_sum_le (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, ((n.divisors.card : ℝ) ^ 2)) ≤
      (N : ℝ) * (1 + Real.log (N + 1)) ^ 3 := by
  -- τ(n)² = Σ_{d∈n.divisors} Σ_{e∈n.divisors} 1
  have hsq : ∀ n : ℕ, ((n.divisors.card : ℝ) ^ 2) =
      ∑ d ∈ n.divisors, ∑ e ∈ n.divisors, (1 : ℝ) := by
    intro n
    have hc : (n.divisors.card : ℝ) = ∑ d ∈ n.divisors, (1 : ℝ) := by
      rw [Finset.card_eq_sum_ones]
      simp
    rw [hc, pow_two]
    rw [Finset.sum_mul (s := n.divisors) (f := fun _ : ℕ => (1 : ℝ))
      (a := ∑ e ∈ n.divisors, (1 : ℝ))]
    apply Finset.sum_congr rfl
    intro d hd
    rw [Finset.mul_sum]
    simp
  -- For each n, replace divisor pairs by the lcm-divisibility condition on (Icc 1 N)².
  have hper : ∀ n ∈ Finset.Icc 1 N,
      (∑ d ∈ n.divisors, ∑ e ∈ n.divisors, (1 : ℝ)) =
        ∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 N, (if Nat.lcm d e ∣ n then (1 : ℝ) else 0) := by
    intro n hn
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have hnN : n ≤ N := (Finset.mem_Icc.mp hn).2
    have hsub : n.divisors ⊆ Finset.Icc 1 N := by
      intro d hd
      rw [Finset.mem_Icc]
      have hdn : d ∣ n := (Nat.mem_divisors.mp hd).1
      constructor
      · exact Nat.pos_of_dvd_of_pos hdn hn1
      · exact le_trans (Nat.le_of_dvd hn1 hdn) hnN
    have hin : ∀ d : ℕ, d ∈ n.divisors →
        (∑ e ∈ n.divisors, (1 : ℝ)) =
          ∑ e ∈ Finset.Icc 1 N, (if Nat.lcm d e ∣ n then (1 : ℝ) else 0) := by
      intro d hd
      have hdn : d ∣ n := (Nat.mem_divisors.mp hd).1
      have hset : n.divisors = (Finset.Icc 1 N).filter (fun e => Nat.lcm d e ∣ n) := by
        ext e
        constructor
        · intro he
          have hen : e ∣ n := (Nat.mem_divisors.mp he).1
          rw [Finset.mem_filter, Finset.mem_Icc]
          refine ⟨⟨Nat.pos_of_dvd_of_pos hen hn1, le_trans (Nat.le_of_dvd hn1 hen) hnN⟩, ?_⟩
          exact (Nat.lcm_dvd_iff).2 ⟨hdn, hen⟩
        · intro he
          rw [Finset.mem_filter, Finset.mem_Icc] at he
          rcases he with ⟨⟨he1, heN⟩, hle⟩
          rw [Nat.mem_divisors]
          exact ⟨(Nat.lcm_dvd_iff.mp hle).2, Nat.ne_of_gt hn1⟩
      calc
        (∑ e ∈ n.divisors, (1 : ℝ)) = ∑ e ∈ (Finset.Icc 1 N).filter (fun e => Nat.lcm d e ∣ n), (1 : ℝ) := by
              rw [hset]
        _ = ∑ e ∈ Finset.Icc 1 N, (if Nat.lcm d e ∣ n then (1 : ℝ) else 0) := by
              rw [Finset.sum_filter]
    calc
      (∑ d ∈ n.divisors, ∑ e ∈ n.divisors, (1 : ℝ))
      = ∑ d ∈ n.divisors, ∑ e ∈ Finset.Icc 1 N, (if Nat.lcm d e ∣ n then (1 : ℝ) else 0) := by
            apply Finset.sum_congr rfl
            intro d hd
            exact hin d hd
      _ = ∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 N, (if Nat.lcm d e ∣ n then (1 : ℝ) else 0) := by
            apply Finset.sum_subset hsub
            intro d hdIcc hdnot
            have hdn' : ¬ d ∣ n := by
              intro hdn
              apply hdnot
              rw [Nat.mem_divisors]
              exact ⟨hdn, Nat.ne_of_gt hn1⟩
            apply Finset.sum_eq_zero
            intro e he
            have hle : ¬ Nat.lcm d e ∣ n := by
              intro hle
              exact hdn' (dvd_trans (Nat.dvd_lcm_left d e) hle)
            simp [hle]
  calc
    (∑ n ∈ Finset.Icc 1 N, ((n.divisors.card : ℝ) ^ 2))
    = ∑ n ∈ Finset.Icc 1 N, ∑ d ∈ n.divisors, ∑ e ∈ n.divisors, (1 : ℝ) := by
          apply Finset.sum_congr rfl
          intro n hn
          exact hsq n
    _ = ∑ n ∈ Finset.Icc 1 N, ∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 N, (if Nat.lcm d e ∣ n then (1 : ℝ) else 0) := by
          apply Finset.sum_congr rfl
          intro n hn
          exact hper n hn
    _ = ∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N, (if Nat.lcm d e ∣ n then (1 : ℝ) else 0) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro d hd
          rw [Finset.sum_comm]
    _ = ∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 N, ((N / Nat.lcm d e : ℕ) : ℝ) := by
          apply Finset.sum_congr rfl
          intro d hd
          apply Finset.sum_congr rfl
          intro e he
          rw [Finset.sum_boole (p := fun n : ℕ => Nat.lcm d e ∣ n) (s := Finset.Icc 1 N)]
          have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
          have hlcm : 1 ≤ Nat.lcm d e :=
            le_trans hd1 (Nat.le_lcm_left d (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 1) (Finset.mem_Icc.mp he).1))
          rw [card_multiples_Icc N (Nat.lcm d e) hlcm]
    _ ≤ ∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 N, (N : ℝ) / (Nat.lcm d e : ℝ) := by
          apply Finset.sum_le_sum
          intro d hd
          apply Finset.sum_le_sum
          intro e he
          exact Nat.cast_div_le
    _ = (N : ℝ) * (∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 N, (1 : ℝ) / (Nat.lcm d e : ℝ)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro d hd
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro e he
          ring
    _ ≤ (N : ℝ) * (1 + Real.log (N + 1)) ^ 3 := by
          exact mul_le_mul_of_nonneg_left (lcm_inv_sum_le N) (by exact_mod_cast Nat.zero_le N)

/-! ## 5. Square-sum bound for vaughanFirst -/

/-- **Vaughan V1 square-sum bound**:
`Σ_{n≤N} vaughanFirst(n,u)² ≤ N·(1+log(N+1))⁵`,
using the elementary pointwise bound `|vaughanFirst| ≤ τ·log`
and the divisor square-sum bound. -/
theorem vaughanFirst_l2_sum_le (u : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ,
    (∑ n ∈ Finset.range (N + 1), (vaughanFirst n u) ^ 2) ≤
      C * (N : ℝ) * (1 + Real.log (N + 1)) ^ 5 := by
  refine ⟨1, by norm_num, ?_⟩
  intro N
  calc
    (∑ n ∈ Finset.range (N + 1), (vaughanFirst n u) ^ 2)
    = (vaughanFirst 0 u) ^ 2 + ∑ n ∈ Finset.Icc 1 N, (vaughanFirst n u) ^ 2 := by
          rw [Finset.sum_range_succ']
          -- Move the zero term from the right-hand position to the left.
          rw [add_comm ((vaughanFirst 0 u) ^ 2)]
          congr 1
          -- Σ_{k∈range N} f(k+1) = Σ_{n∈Icc 1 N} f n via the bijection k ↦ k+1.
          apply Finset.sum_bij (s := Finset.range N) (t := Finset.Icc 1 N)
            (f := fun k => (vaughanFirst (k + 1) u) ^ 2)
            (g := fun n => (vaughanFirst n u) ^ 2)
            (i := fun k _ => k + 1)
          · intro k hk
            rw [Finset.mem_Icc]
            have hk' : k < N := Finset.mem_range.mp hk
            constructor
            · exact Nat.succ_pos k
            · exact Nat.succ_le_of_lt hk'
          · intro k₁ hk₁ k₂ hk₂ h
            omega
          · intro n hn
            rw [Finset.mem_Icc] at hn
            refine ⟨n - 1, ?_, ?_⟩
            · rw [Finset.mem_range]
              omega
            · have hn1 : 1 ≤ n := hn.1
              omega
          · intro k hk
            rfl
    _ ≤ ∑ n ∈ Finset.Icc 1 N, (vaughanFirst n u) ^ 2 := by
          simp [vaughanFirst_zero]
    _ ≤ ∑ n ∈ Finset.Icc 1 N, ((n.divisors.card : ℝ) ^ 2 * (Real.log (n + 1)) ^ 2) := by
          apply Finset.sum_le_sum
          intro n hn
          have hnonneg : 0 ≤ (n.divisors.card : ℝ) * Real.log (n + 1) := by
            have hlog : 0 ≤ Real.log (n + 1) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ n + 1 by omega))
            exact mul_nonneg (by exact_mod_cast Nat.zero_le _) hlog
          have h1 : (vaughanFirst n u) ^ 2 ≤ ((n.divisors.card : ℝ) * Real.log (n + 1)) ^ 2 := by
            exact sq_le_sq.mpr (by simpa [abs_of_nonneg hnonneg] using vaughanFirst_abs_le n u)
          calc
            (vaughanFirst n u) ^ 2 ≤ ((n.divisors.card : ℝ) * Real.log (n + 1)) ^ 2 := h1
            _ = (n.divisors.card : ℝ) ^ 2 * (Real.log (n + 1)) ^ 2 := by ring
    _ ≤ (Real.log (N + 1)) ^ 2 * (∑ n ∈ Finset.Icc 1 N, ((n.divisors.card : ℝ) ^ 2)) := by
          -- Use log(n+1) ≤ log(N+1) and factor out the constant.
          have hlog : ∀ n ∈ Finset.Icc 1 N, Real.log (n + 1) ≤ Real.log (N + 1) := by
            intro n hn
            apply Real.log_le_log
            · exact_mod_cast (Nat.succ_pos n)
            · exact_mod_cast (Nat.succ_le_succ (Finset.mem_Icc.mp hn).2)
          calc
            (∑ n ∈ Finset.Icc 1 N, (n.divisors.card : ℝ) ^ 2 * (Real.log (n + 1)) ^ 2)
                ≤ ∑ n ∈ Finset.Icc 1 N, (n.divisors.card : ℝ) ^ 2 * (Real.log (N + 1)) ^ 2 := by
                    apply Finset.sum_le_sum
                    intro n hn
                    exact mul_le_mul_of_nonneg_left
                      (sq_le_sq.mpr (by
                        have h1 : 0 ≤ Real.log (n + 1) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ n + 1 by omega))
                        have h2 : 0 ≤ Real.log (N + 1) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ N + 1 by omega))
                        simpa [abs_of_nonneg h1, abs_of_nonneg h2] using hlog n hn))
                      (sq_nonneg _)
            _ = (Real.log (N + 1)) ^ 2 * (∑ n ∈ Finset.Icc 1 N, (n.divisors.card : ℝ) ^ 2) := by
                  rw [← Finset.sum_mul (s := Finset.Icc 1 N)
                    (f := fun n => (n.divisors.card : ℝ) ^ 2)
                    (a := (Real.log (N + 1)) ^ 2)]
                  ring
    _ ≤ (Real.log (N + 1)) ^ 2 * ((N : ℝ) * (1 + Real.log (N + 1)) ^ 3) := by
          exact mul_le_mul_of_nonneg_left (divisorCountSq_sum_le N) (sq_nonneg _)
    _ = (Real.log (N + 1)) ^ 2 * (N : ℝ) * (1 + Real.log (N + 1)) ^ 3 := by ring
    _ ≤ 1 * (N : ℝ) * (1 + Real.log (N + 1)) ^ 5 := by
          have hlog : 0 ≤ Real.log (N + 1) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ N + 1 by omega))
          have hle1 : (Real.log (N + 1)) ^ 2 ≤ (1 + Real.log (N + 1)) ^ 2 := by
            exact sq_le_sq.mpr (by
              have h1 : Real.log (N + 1) ≤ 1 + Real.log (N + 1) := by linarith
              simpa [abs_of_nonneg hlog, abs_of_nonneg (by linarith : 0 ≤ 1 + Real.log (N + 1))] using h1)
          have hle2 : (1 + Real.log (N + 1)) ^ 3 ≤ (1 + Real.log (N + 1)) ^ 5 := by
            have hc : 1 ≤ 1 + Real.log (N + 1) := by linarith
            have hcpos : 0 ≤ 1 + Real.log (N + 1) := by linarith
            calc
              (1 + Real.log (N + 1)) ^ 3 = (1 + Real.log (N + 1)) ^ 3 * 1 := by ring
              _ ≤ (1 + Real.log (N + 1)) ^ 3 * (1 + Real.log (N + 1)) ^ 2 := by
                    exact mul_le_mul_of_nonneg_left
                      (by simpa using (pow_le_pow_left₀ (by norm_num : 0 ≤ (1 : ℝ)) hc 2))
                      (pow_nonneg hcpos 3)
              _ = (1 + Real.log (N + 1)) ^ 5 := by ring
          have hN : 0 ≤ (N : ℝ) := by exact_mod_cast Nat.zero_le N
          calc
            (Real.log (N + 1)) ^ 2 * (N : ℝ) * (1 + Real.log (N + 1)) ^ 3
                = (Real.log (N + 1)) ^ 2 * ((N : ℝ) * (1 + Real.log (N + 1)) ^ 3) := by ring
            _ ≤ (1 + Real.log (N + 1)) ^ 2 * ((N : ℝ) * (1 + Real.log (N + 1)) ^ 3) := by
                  exact mul_le_mul_of_nonneg_right hle1 (mul_nonneg hN (pow_nonneg (by linarith) 3))
            _ = (N : ℝ) * ((1 + Real.log (N + 1)) ^ 2 * (1 + Real.log (N + 1)) ^ 3) := by ring
            _ ≤ (N : ℝ) * (1 + Real.log (N + 1)) ^ 5 := by
                  have hpow : (1 + Real.log (N + 1)) ^ 2 * (1 + Real.log (N + 1)) ^ 3 =
                      (1 + Real.log (N + 1)) ^ 5 := by ring
                  rw [← hpow]
            _ ≤ 1 * (N : ℝ) * (1 + Real.log (N + 1)) ^ 5 := by simp

/-! ## 6. Per-modulus large-sieve reduction of character square sums -/

/-- Reindex an `ℕ` range sum as an `ℤ` interval sum
using the natural embedding `n ↦ n`. -/
private lemma sum_range_to_Icc_int {m : ℕ} {β : Type*} [AddCommMonoid β] (f : ℕ → β)
    (g : ℤ → β) (hfg : ∀ n : ℕ, f n = g (n : ℤ)) :
    (∑ n ∈ Finset.range (m + 1), f n) = ∑ n ∈ Finset.Icc (0 : ℤ) (m : ℤ), g n := by
  rw [Finset.sum_bij (s := Finset.range (m + 1)) (t := Finset.Icc (0 : ℤ) (m : ℤ))
    (f := f) (g := g) (i := fun n _ => (n : ℤ))]
  · intro n hn
    rw [Finset.mem_Icc]
    have hn' : n < m + 1 := Finset.mem_range.mp hn
    constructor <;> omega
  · intro n₁ hn₁ n₂ hn₂ h
    exact_mod_cast h
  · intro z hz
    rw [Finset.mem_Icc] at hz
    refine ⟨z.toNat, ?_, ?_⟩
    · rw [Finset.mem_range]
      omega
    · exact Int.toNat_of_nonneg hz.1
  · intro n hn
    exact hfg n

/-- **Per-modulus character square-sum bound**: for `q ≥ 1`,
`Σ_χ ‖V_χ(m)‖²
 ≤ (φ(q)/q)·largeSieveBound(m+1,1/q²)·Σ_{n≤m} vaughanFirst(n,u)²`.
Combine `characterSieveModulus_le` and `largeSieveRationalPoints`.
This is only a per-modulus estimate; it does not establish
`panTypeICharSquareMeanBound` over `q ≤ Q`.
Primitive-character and Gauss-sum analysis, with additional
all-character control, is needed for that separate mean-value question. -/
theorem panTypeICharSqSum_le_additiveSieve (q m u : ℕ) (hq : 0 < q) :
    panTypeICharSqSum q m u ≤
      ((q.totient : ℝ) / (q : ℝ)) *
        largeSieveBound (m + 1) (1 / (q : ℝ) ^ 2) *
          (∑ n ∈ Finset.range (m + 1), (vaughanFirst n u) ^ 2) := by
  haveI : NeZero q := ⟨Nat.ne_of_gt hq⟩
  let a : ℤ → ℂ := fun n => if 0 ≤ n then (vaughanFirst n.toNat u : ℂ) else 0
  let M : ℤ := -1
  let N : ℕ := m + 1
  -- Icc (M+1) (M+N) = Icc 0 (m:ℤ)
  have hIcc : Finset.Icc (M + 1) (M + N) = Finset.Icc (0 : ℤ) (m : ℤ) := by
    dsimp [M, N]
    have h2 : (-1 : ℤ) + ((m : ℤ) + 1) = (m : ℤ) := by omega
    rw [h2]
  -- Coefficient identity: a (n : ℤ) = vaughanFirst n u.
  have ha : ∀ n : ℕ, a (n : ℤ) = (vaughanFirst n u : ℂ) := by
    intro n
    have htn : (n : ℤ).toNat = n := by
      have hz : ((n : ℤ).toNat : ℤ) = (n : ℤ) := Int.toNat_of_nonneg (by omega)
      exact_mod_cast hz
    simp [a, htn]
  -- Character sum: Σ_{Icc} a n·χ(n) = panTypeIV1CharSum q m u χ.
  have hchar : ∀ χ : DirichletCharacter ℂ q,
      (∑ n ∈ Finset.Icc (0 : ℤ) (m : ℤ), a n * χ (n : ZMod q)) =
        panTypeIV1CharSum q m u χ := by
    intro χ
    unfold panTypeIV1CharSum
    rw [← sum_range_to_Icc_int (f := fun n => (vaughanFirst n u : ℂ) * χ (n : ZMod q))
      (g := fun n => a n * χ (n : ZMod q))]
    · intro n
      simp [ha n]
  -- Reindex the charReal sum: Σ_{Icc} charReal(n·r/q)·a n = Σ_{range} charReal·vaughanFirst.
  have hcr : ∀ r : ℕ,
      (∑ n ∈ Finset.Icc (0 : ℤ) (m : ℤ),
        (charReal ((n : ℝ) * ((r : ℝ) / (q : ℝ))) : ℂ) * a n) =
      ∑ n ∈ Finset.range (m + 1),
        (charReal ((n : ℝ) * ((r : ℝ) / (q : ℝ))) : ℂ) * (vaughanFirst n u : ℂ) := by
    intro r
    rw [← sum_range_to_Icc_int
      (f := fun n => (charReal ((n : ℝ) * ((r : ℝ) / (q : ℝ))) : ℂ) * (vaughanFirst n u : ℂ))
      (g := fun n => (charReal ((n : ℝ) * ((r : ℝ) / (q : ℝ))) : ℂ) * a n)]
    · intro n
      simp [ha n]
  -- characterSieveModulus_le (M = -1, N = m+1)
  have hcs := characterSieveModulus_le (q := q) a M N
  -- Left side: Σ_χ‖panTypeIV1‖² = Σ_χ‖Σ_{Icc (M+1)(M+N)}‖².
  have hcsL : (∑ χ : DirichletCharacter ℂ q, ‖panTypeIV1CharSum q m u χ‖ ^ 2) =
      (∑ χ : DirichletCharacter ℂ q, ‖∑ n ∈ Finset.Icc (M + 1) (M + N), a n * χ (n : ZMod q)‖ ^ 2) := by
    rw [hIcc]
    apply Finset.sum_congr rfl
    intro χ hχ
    rw [(hchar χ).symm]
  -- Rational-point inclusion: {r/q : r < q} ⊆ rationalPoints q.
  have hsubset : (Finset.range q).image (fun r : ℕ => (r : ℝ) / (q : ℝ)) ⊆ rationalPoints q := by
    intro x hx
    unfold rationalPoints
    rw [Finset.mem_biUnion]
    rcases Finset.mem_image.mp hx with ⟨r, hr, rfl⟩
    refine ⟨q, Finset.mem_Icc.mpr ⟨hq, le_rfl⟩, ?_⟩
    exact Finset.mem_image.mpr ⟨r, hr, rfl⟩
  -- Apply the additive large sieve.
  have hls := largeSieveRationalPoints M N q hq a
  -- Bound the sum over r by the sum over the deduplicated rational-point set.
  have hRstep : (∑ r ∈ Finset.range q,
        ‖∑ n ∈ Finset.Icc (M + 1) (M + N),
          (charReal ((n : ℝ) * ((r : ℝ) / (q : ℝ))) : ℂ) * a n‖ ^ 2)
      ≤ (∑ x ∈ rationalPoints q,
        ‖∑ n ∈ Finset.Icc (M + 1) (M + N), (charReal ((n : ℝ) * x) : ℂ) * a n‖ ^ 2) := by
    rw [hIcc]
    have hinj : Set.InjOn (fun r : ℕ => (r : ℝ) / (q : ℝ)) ↑(Finset.range q) := by
      intro r₁ hr₁ r₂ hr₂ h
      have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
      have hnum : (r₁ : ℝ) = (r₂ : ℝ) := by
        have : (r₁ : ℝ) / (q : ℝ) = (r₂ : ℝ) / (q : ℝ) := h
        field_simp [hq0] at this
        exact this
      exact_mod_cast hnum
    calc
      (∑ r ∈ Finset.range q, ‖∑ n ∈ Finset.Icc (0 : ℤ) (m : ℤ),
          (charReal ((n : ℝ) * ((r : ℝ) / (q : ℝ))) : ℂ) * a n‖ ^ 2)
      = ∑ x ∈ (Finset.range q).image (fun r : ℕ => (r : ℝ) / (q : ℝ)),
          ‖∑ n ∈ Finset.Icc (0 : ℤ) (m : ℤ), (charReal ((n : ℝ) * x) : ℂ) * a n‖ ^ 2 := by
          rw [Finset.sum_image]
          exact hinj
      _ ≤ ∑ x ∈ rationalPoints q,
          ‖∑ n ∈ Finset.Icc (0 : ℤ) (m : ℤ), (charReal ((n : ℝ) * x) : ℂ) * a n‖ ^ 2 := by
          exact Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun _ _ _ => sq_nonneg _)
  -- Identify the L² sum of coefficients.
  have hL2 : (∑ n ∈ Finset.Icc (0 : ℤ) (m : ℤ), ‖a n‖ ^ 2) =
      (∑ n ∈ Finset.range (m + 1), (vaughanFirst n u) ^ 2) := by
    rw [← sum_range_to_Icc_int (f := fun n => ‖(vaughanFirst n u : ℂ)‖ ^ 2)
      (g := fun n => ‖a n‖ ^ 2)]
    · apply Finset.sum_congr rfl
      intro n hn
      simp [sq_abs]
    · intro n
      simp [ha n]
  -- Combine the estimates.
  have hqφ : 0 < (q : ℝ) / (q.totient : ℝ) := by
    have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
    have hφR : 0 < (q.totient : ℝ) := by exact_mod_cast (Nat.totient_pos.mpr hq)
    exact div_pos hqR hφR
  have hmain : (q : ℝ) / (q.totient : ℝ) * panTypeICharSqSum q m u ≤
      largeSieveBound (m + 1) (1 / (q : ℝ) ^ 2) *
        (∑ n ∈ Finset.range (m + 1), (vaughanFirst n u) ^ 2) := by
    calc
      (q : ℝ) / (q.totient : ℝ) * panTypeICharSqSum q m u
      = ((q : ℝ) / (q.totient : ℝ)) *
          (∑ χ : DirichletCharacter ℂ q, ‖panTypeIV1CharSum q m u χ‖ ^ 2) := by
            rfl
      _ = ((q : ℝ) / (q.totient : ℝ)) * (∑ χ : DirichletCharacter ℂ q,
            ‖∑ n ∈ Finset.Icc (M + 1) (M + N), a n * χ (n : ZMod q)‖ ^ 2) := by
            rw [hcsL]
      _ ≤ (∑ r ∈ Finset.range q,
            ‖∑ n ∈ Finset.Icc (M + 1) (M + N),
              (charReal ((n : ℝ) * ((r : ℝ) / (q : ℝ))) : ℂ) * a n‖ ^ 2) := by
            simpa [mul_div_assoc] using hcs
      _ ≤ (∑ x ∈ rationalPoints q,
            ‖∑ n ∈ Finset.Icc (M + 1) (M + N), (charReal ((n : ℝ) * x) : ℂ) * a n‖ ^ 2) := hRstep
      _ ≤ largeSieveBound (m + 1) (1 / (q : ℝ) ^ 2) *
            (∑ n ∈ Finset.Icc (M + 1) (M + N), ‖a n‖ ^ 2) := hls
      _ = largeSieveBound (m + 1) (1 / (q : ℝ) ^ 2) *
            (∑ n ∈ Finset.range (m + 1), (vaughanFirst n u) ^ 2) := by
            rw [hIcc, hL2]
  -- Divide by q/φ to obtain S ≤ (φ/q)·T.
  calc
    panTypeICharSqSum q m u
        ≤ largeSieveBound (m + 1) (1 / (q : ℝ) ^ 2) *
            (∑ n ∈ Finset.range (m + 1), (vaughanFirst n u) ^ 2) /
              ((q : ℝ) / (q.totient : ℝ)) := by
          exact (le_div_iff₀ hqφ).mpr (by simpa [mul_comm] using hmain)
    _ = ((q.totient : ℝ) / (q : ℝ)) *
          largeSieveBound (m + 1) (1 / (q : ℝ) ^ 2) *
          (∑ n ∈ Finset.range (m + 1), (vaughanFirst n u) ^ 2) := by
          field_simp [show (q : ℝ) ≠ 0 by exact_mod_cast (Nat.ne_of_gt hq),
            show (q.totient : ℝ) ≠ 0 by exact_mod_cast (Nat.totient_pos.mpr hq).ne']

/-! ## 7. Replacing panTypeICharSqrtMeanMaxY by a sum over y -/

/-- `panTypeICharSqrtMean` is nonnegative, since absolute values
and square roots are nonnegative. -/
private lemma panTypeICharSqrtMean_nonneg (y X q : ℕ) (f : ℕ → ℝ) (u : ℕ) :
    0 ≤ panTypeICharSqrtMean y X q f u := by
  unfold panTypeICharSqrtMean
  exact Finset.sum_nonneg (fun a ha =>
    mul_nonneg (div_nonneg (abs_nonneg _) (abs_nonneg _)) (Real.sqrt_nonneg _))

/-- **Maximum-to-sum bound**:
`panTypeICharSqrtMeanMaxY ≤ Σ_{y≤x} panTypeICharSqrtMean y`,
since the summands are nonnegative. -/
theorem panTypeICharSqrtMeanMaxY_le_sum (X q x : ℕ) (f : ℕ → ℝ) (u : ℕ) :
    panTypeICharSqrtMeanMaxY X q x f u ≤
      ∑ y ∈ Finset.range (x + 1), panTypeICharSqrtMean y X q f u := by
  unfold panTypeICharSqrtMeanMaxY
  apply Finset.max'_le
  intro z hz
  rcases Finset.mem_image.mp hz with ⟨y, hy, rfl⟩
  exact Finset.single_le_sum (fun y' hy' => panTypeICharSqrtMean_nonneg y' X q f u) hy

/-! ## 8. Character square sums bounded by the sieve constant and the V1 square sum -/

/-- **Expanded per-modulus reduction**: after removing the maximum,
bound `panTypeICharSqrtMeanMaxY` by elementary quantities.
For each `y ≤ x`, `a ≤ X`,
`√(Σ_χ‖V_χ(y/a)‖²)
 ≤ √((φ(q)/q)·largeSieveBound(y/a+1,1/q²))
   ·√(Σ_{n≤y/a} vaughanFirst(n,u)²)`.
Only the sieve constant, V1 square sum, and outer weights remain.
A mean over moduli is a separate step involving Gauss-sum and
primitive-character analysis. -/
theorem panTypeICharSqrtMeanMaxY_le_sieveSqrtSum (X q x : ℕ) (f : ℕ → ℝ) (u : ℕ) (hq : 0 < q) :
    panTypeICharSqrtMeanMaxY X q x f u ≤
      ∑ y ∈ Finset.range (x + 1), ∑ a ∈ Finset.Icc 1 X,
        |f a| / |Real.log ((y / a : ℕ) : ℝ)| *
          Real.sqrt (((q.totient : ℝ) / (q : ℝ)) *
            largeSieveBound (y / a + 1) (1 / (q : ℝ) ^ 2)) *
          Real.sqrt (∑ n ∈ Finset.range (y / a + 1), (vaughanFirst n u) ^ 2) := by
  calc
    panTypeICharSqrtMeanMaxY X q x f u
        ≤ ∑ y ∈ Finset.range (x + 1), panTypeICharSqrtMean y X q f u :=
          panTypeICharSqrtMeanMaxY_le_sum X q x f u
    _ = ∑ y ∈ Finset.range (x + 1), ∑ a ∈ Finset.Icc 1 X,
        |f a| / |Real.log ((y / a : ℕ) : ℝ)| * Real.sqrt (panTypeICharSqSum q (y / a) u) := by
          rfl
    _ ≤ ∑ y ∈ Finset.range (x + 1), ∑ a ∈ Finset.Icc 1 X,
        |f a| / |Real.log ((y / a : ℕ) : ℝ)| *
          Real.sqrt (((q.totient : ℝ) / (q : ℝ)) *
            largeSieveBound (y / a + 1) (1 / (q : ℝ) ^ 2) *
            (∑ n ∈ Finset.range (y / a + 1), (vaughanFirst n u) ^ 2)) := by
          apply Finset.sum_le_sum
          intro y hy
          apply Finset.sum_le_sum
          intro a ha
          exact mul_le_mul_of_nonneg_left
            (Real.sqrt_le_sqrt (panTypeICharSqSum_le_additiveSieve q (y / a) u hq))
            (div_nonneg (abs_nonneg _) (abs_nonneg _))
    _ ≤ ∑ y ∈ Finset.range (x + 1), ∑ a ∈ Finset.Icc 1 X,
        |f a| / |Real.log ((y / a : ℕ) : ℝ)| *
          Real.sqrt (((q.totient : ℝ) / (q : ℝ)) *
            largeSieveBound (y / a + 1) (1 / (q : ℝ) ^ 2)) *
          Real.sqrt (∑ n ∈ Finset.range (y / a + 1), (vaughanFirst n u) ^ 2) := by
          apply Finset.sum_le_sum
          intro y hy
          apply Finset.sum_le_sum
          intro a ha
          have hAB : 0 ≤ ((q.totient : ℝ) / (q : ℝ)) *
              largeSieveBound (y / a + 1) (1 / (q : ℝ) ^ 2) := by
            have h1 : 0 ≤ (q.totient : ℝ) / (q : ℝ) := by positivity
            have h2 : 0 ≤ largeSieveBound (y / a + 1) (1 / (q : ℝ) ^ 2) := by
              exact largeSieveBound_nonneg (y / a + 1) (by positivity)
            exact mul_nonneg h1 h2
          rw [Real.sqrt_mul hAB (∑ n ∈ Finset.range (y / a + 1), (vaughanFirst n u) ^ 2)]
          simp [mul_assoc]

end

end AnalyticNumberTheory.Sieve
