import AnalyticNumberTheory.Sieve.PanMeanValueBody
import AnalyticNumberTheory.Sieve.PanV1SquareMean
import AnalyticNumberTheory.LargeSieve.Multiplicative
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic

/-! # AnalyticNumberTheory.Sieve.PanV3SquareMean

## Type II square-sum bounds and per-modulus large-sieve reduction

This module proves two components relevant to
`panTypeIICharMeanSieveBound` and `PanTypeIICharacterMeanValue`
(`PanMeanValueBody.lean` §§5, 5.2), parallel to `PanV1SquareMean.lean`:

1. **Elementary square-sum bound**:
   `Σ_{n≤N} vaughanThird(n,u,v)² ≤ N·(1+log(N+1))⁵`.
   The bilinear inner sum satisfies
   `Σ_{e|n/d, v<e} Λ(e) ≤ Σ_{e|n/d} Λ(e) = log(n/d)`,
   by `ArithmeticFunction.vonMangoldt_sum` and `Λ ≥ 0`.
   With `|μ(d)| ≤ 1` and `τ(n) = n.divisors.card`, this gives
   `|vaughanThird(n,u,v)| ≤ τ(n)·log(n+1)`.
   Double counting and the lcm reduction yield
   `Σ_{n≤N} τ(n)² ≤ N·(1+log(N+1))³`.
2. **Per-modulus character square-sum bound**:
   `Σ_χ ‖V_χ(m)‖²
    ≤ (φ(q)/q)·largeSieveBound(m+1,1/q²)·Σ_{n≤m} vaughanThird(n,u,v)²`,
   where `V_χ(m) = Σ_{n≤m} vaughanThird(n,u,v)·χ(n)`
   is `panTypeIIV3CharSum`. Combine `characterSieveModulus_le`
   with `largeSieveRationalPoints`, then replace the maximum by
   a sum to obtain `panTypeIICharSqrtMeanMaxY_le_sieveSqrtSum`.

This does not prove the all-character `panTypeIICharSquareMeanBound`
over `q ≤ Q`. The classical Bombieri--Davenport theorem uses
primitive characters and Gauss sums `|τ(χ)|² = q`; the
all-character version requires additional control and has a
principal-character obstruction at `u = v = 1`
(see `PanTypeIIBoundAudit.lean`). The final per-modulus reduction
here leaves only the sieve constant, the V3 L² sum, and outer
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

/-! ## 1. Elementary pointwise bound for vaughanThird -/

/-- `μ(d) ∈ {-1, 0, 1}`: `|μ d| ≤ 1`. -/
lemma v3_moebius_abs_le_one (d : ℕ) : |((μ d : ℤ) : ℝ)| ≤ 1 := by
  exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := d))

/-- `vaughanThird 0 u v = 0`: the filtered divisor set of 0 is empty. -/
lemma vaughanThird_zero (u v : ℕ) : vaughanThird 0 u v = 0 := by
  unfold vaughanThird
  simp [Nat.divisors_zero]

/-- Nonnegativity of von Mangoldt, an alias for mathlib's
`ArithmeticFunction.vonMangoldt_nonneg`. -/
lemma v3_vonMangoldt_nonneg (e : ℕ) : 0 ≤ Λ e :=
  ArithmeticFunction.vonMangoldt_nonneg

/-- **Pointwise V3 bound**:
`|vaughanThird(n,u,v)| ≤ τ(n)·log(n+1)`, where
`τ(n) = n.divisors.card`. The bilinear inner sum is bounded by
`Σ_{e|n/d} Λ(e) = log(n/d)` using `vonMangoldt_sum` and `Λ ≥ 0`;
the outer coefficients satisfy `|μ(d)| ≤ 1`.
At `n = 0`, use `vaughanThird 0 u v = 0`. -/
lemma vaughanThird_abs_le (n u v : ℕ) :
    |vaughanThird n u v| ≤ (n.divisors.card : ℝ) * Real.log (n + 1) := by
  by_cases hn : n = 0
  · subst n
    simp [vaughanThird_zero]
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    let s : Finset ℕ := n.divisors.filter (fun d => u < d)
    let t : ℕ → Finset ℕ := fun d => (n / d).divisors.filter (fun e => v < e)
    have hterm : ∀ d ∈ s, (∑ e ∈ t d, |((μ d : ℤ) : ℝ) * Λ e|) ≤ Real.log (n + 1) := by
      intro d hd
      have hdmem : d ∈ n.divisors := (Finset.mem_filter.mp hd).1
      have hdn : d ∣ n := (Nat.mem_divisors.mp hdmem).1
      have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdn hnpos
      have hnd : 1 ≤ n / d := Nat.div_pos (Nat.le_of_dvd hnpos hdn) hdpos
      have hlog_le : Real.log ((n / d : ℕ) : ℝ) ≤ Real.log (n + 1) := by
        apply Real.log_le_log
        · exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 1) hnd)
        · exact_mod_cast (le_trans (Nat.div_le_self n d) (Nat.le_succ n))
      calc
        (∑ e ∈ t d, |((μ d : ℤ) : ℝ) * Λ e|)
            = ∑ e ∈ t d, (|((μ d : ℤ) : ℝ)| * Λ e) := by
              apply Finset.sum_congr rfl
              intro e he
              rw [abs_mul]
              rw [abs_of_nonneg (v3_vonMangoldt_nonneg e)]
        _ ≤ ∑ e ∈ t d, Λ e := by
              apply Finset.sum_le_sum
              intro e he
              exact mul_le_of_le_one_left (v3_vonMangoldt_nonneg e) (v3_moebius_abs_le_one d)
        _ ≤ ∑ e ∈ (n / d).divisors, Λ e := by
              exact Finset.sum_le_sum_of_subset_of_nonneg
                (Finset.filter_subset (fun e => v < e) (n / d).divisors)
                (fun _ _ _ => v3_vonMangoldt_nonneg _)
        _ = Real.log ((n / d : ℕ) : ℝ) := by
              exact ArithmeticFunction.vonMangoldt_sum (n := n / d)
        _ ≤ Real.log (n + 1) := hlog_le
    calc
      |vaughanThird n u v| ≤ ∑ d ∈ s, |∑ e ∈ t d, ((μ d : ℤ) : ℝ) * Λ e| := by
            unfold vaughanThird s t
            exact Finset.abs_sum_le_sum_abs
              (fun d => ∑ e ∈ (n / d).divisors.filter (fun e => v < e), ((μ d : ℤ) : ℝ) * Λ e)
              (n.divisors.filter (fun d => u < d))
      _ ≤ ∑ d ∈ s, ∑ e ∈ t d, |((μ d : ℤ) : ℝ) * Λ e| := by
            apply Finset.sum_le_sum
            intro d hd
            exact Finset.abs_sum_le_sum_abs (fun e => ((μ d : ℤ) : ℝ) * Λ e) (t d)
      _ ≤ ∑ d ∈ s, Real.log (n + 1) := by
            exact Finset.sum_le_sum (fun d hd => hterm d hd)
      _ = (s.card : ℝ) * Real.log (n + 1) := by
            simp [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (n.divisors.card : ℝ) * Real.log (n + 1) := by
            have hc : s.card ≤ n.divisors.card :=
              Finset.card_le_card (Finset.filter_subset (fun d => u < d) n.divisors)
            have hlog : 0 ≤ Real.log (n + 1) := by
              have h1 : 1 ≤ n + 1 := by omega
              exact Real.log_nonneg (by exact_mod_cast h1)
            exact mul_le_mul_of_nonneg_right (by exact_mod_cast hc) hlog

/-! ## 2. Harmonic sums and multiple counts for the τ² estimate -/

/-- Harmonic bound `Σ_{k=1}^{M} 1/k ≤ 1+log(M+1)`,
a consequence of mathlib's harmonic-sum estimates. -/
lemma v3_harmonic_Icc_le (M : ℕ) :
    (∑ k ∈ Finset.Icc 1 M, (1 : ℝ) / (k : ℝ)) ≤ 1 + Real.log (M + 1) := by
  exact harmonic_Icc_le M

/-- Multiple count: `#{n ∈ Icc 1 N : m | n} = N/m` for `m ≥ 1`. -/
lemma v3_card_multiples_Icc (N m : ℕ) (hm : 1 ≤ m) :
    ((Finset.Icc 1 N).filter (fun n => m ∣ n)).card = N / m := by
  exact card_multiples_Icc N m hm

/-! ## 3. Reciprocal-lcm sums and Σ_{n≤N} τ(n)² ≤ N·(1+log(N+1))³ -/

/-- `1/lcm(d,e) = gcd(d,e)/(d·e)` in `ℝ`, for `d,e ≥ 1`. -/
private lemma lcm_inv_eq_gcd_div {d e : ℕ} (hd : 1 ≤ d) (he : 1 ≤ e) :
    (1 : ℝ) / (Nat.lcm d e : ℝ) = (Nat.gcd d e : ℝ) / ((d : ℝ) * (e : ℝ)) := by
  exact pan_lcm_inv_eq_gcd_div hd he

/-- **Double reciprocal-lcm sum**:
`Σ_{d,e≤N} 1/lcm(d,e) ≤ (1+log(N+1))³`.
Use `lcm = de/gcd` and `gcd(d,e) = Σ_{g|d, g|e} φ(g)` to write
`Σ_{d,e} 1/lcm(d,e) = Σ_{g≤N} (φ(g)/g²)·(Σ_{d'≤N/g} 1/d')²`.
This is at most
`(1+log(N+1))²·Σ_{g≤N} φ(g)/g²
 ≤ (1+log(N+1))²·Σ_{g≤N} 1/g ≤ (1+log(N+1))³`. -/
lemma v3_lcm_inv_sum_le (N : ℕ) :
    (∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 N, (1 : ℝ) / (Nat.lcm d e : ℝ)) ≤
      (1 + Real.log (N + 1)) ^ 3 := by
  exact lcm_inv_sum_le N

/-! ## 4. Summing τ(n)² up to N -/

/-- **Divisor square-sum bound**:
`Σ_{n≤N} τ(n)² ≤ N·(1+log(N+1))³`.
Double count `τ(n)² = #{(d,e) : d|n, e|n}` and exchange sums:
`Σ_{n≤N} τ(n)² = Σ_{d,e≤N} ⌊N/lcm(d,e)⌋`. -/
lemma v3_divisorCountSq_sum_le (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, ((n.divisors.card : ℝ) ^ 2)) ≤
      (N : ℝ) * (1 + Real.log (N + 1)) ^ 3 := by
  exact divisorCountSq_sum_le N

/-! ## 5. Square-sum bound for vaughanThird -/

/-- **Vaughan V3 square-sum bound**:
`Σ_{n≤N} vaughanThird(n,u,v)² ≤ N·(1+log(N+1))⁵`,
using the elementary pointwise bound `|vaughanThird| ≤ τ·log`
and the divisor square-sum bound. -/
theorem vaughanThird_l2_sum_le (u v : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ,
    (∑ n ∈ Finset.range (N + 1), (vaughanThird n u v) ^ 2) ≤
      C * (N : ℝ) * (1 + Real.log (N + 1)) ^ 5 := by
  refine ⟨1, by norm_num, ?_⟩
  intro N
  calc
    (∑ n ∈ Finset.range (N + 1), (vaughanThird n u v) ^ 2)
    = (vaughanThird 0 u v) ^ 2 + ∑ n ∈ Finset.Icc 1 N, (vaughanThird n u v) ^ 2 := by
          -- Split off zero using the standard range/interval identity.
          exact Finset.sum_range_eq_add_Ico (fun n => (vaughanThird n u v) ^ 2)
            (Nat.succ_pos N)
    _ ≤ ∑ n ∈ Finset.Icc 1 N, (vaughanThird n u v) ^ 2 := by
          simp [vaughanThird_zero]
    _ ≤ ∑ n ∈ Finset.Icc 1 N, ((n.divisors.card : ℝ) ^ 2 * (Real.log (n + 1)) ^ 2) := by
          apply Finset.sum_le_sum
          intro n hn
          have hnonneg : 0 ≤ (n.divisors.card : ℝ) * Real.log (n + 1) := by
            have hlog : 0 ≤ Real.log (n + 1) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ n + 1 by omega))
            exact mul_nonneg (by exact_mod_cast Nat.zero_le _) hlog
          have h1 : (vaughanThird n u v) ^ 2 ≤ ((n.divisors.card : ℝ) * Real.log (n + 1)) ^ 2 := by
            exact sq_le_sq.mpr (by simpa [abs_of_nonneg hnonneg] using vaughanThird_abs_le n u v)
          calc
            (vaughanThird n u v) ^ 2 ≤ ((n.divisors.card : ℝ) * Real.log (n + 1)) ^ 2 := h1
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
          exact mul_le_mul_of_nonneg_left (v3_divisorCountSq_sum_le N) (sq_nonneg _)
    _ = (Real.log (N + 1)) ^ 2 * (N : ℝ) * (1 + Real.log (N + 1)) ^ 3 := by ring
    _ ≤ 1 * (N : ℝ) * (1 + Real.log (N + 1)) ^ 5 := by
          have hlog : 0 ≤ Real.log (N + 1) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ N + 1 by omega))
          have hle1 : (Real.log (N + 1)) ^ 2 ≤ (1 + Real.log (N + 1)) ^ 2 := by
            exact sq_le_sq.mpr (by
              have h1 : Real.log (N + 1) ≤ 1 + Real.log (N + 1) := by linarith
              simpa [abs_of_nonneg hlog, abs_of_nonneg (by linarith : 0 ≤ 1 + Real.log (N + 1))] using h1)
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
  exact pan_sum_range_to_Icc_int f g hfg

/-- **Per-modulus character square-sum bound**: for `q ≥ 1`,
`Σ_χ ‖V_χ(m)‖²
 ≤ (φ(q)/q)·largeSieveBound(m+1,1/q²)·Σ_{n≤m} vaughanThird(n,u,v)²`.
Combine `characterSieveModulus_le` and `largeSieveRationalPoints`.
This is only a per-modulus estimate; it does not establish
`panTypeIICharSquareMeanBound` over `q ≤ Q`.
Primitive-character and Gauss-sum analysis, with additional
all-character control, is needed for that separate mean-value question. -/
theorem panTypeIICharSqSum_le_additiveSieve (q m u v : ℕ) (hq : 0 < q) :
    panTypeIICharSqSum q m u v ≤
      ((q.totient : ℝ) / (q : ℝ)) *
        largeSieveBound (m + 1) (1 / (q : ℝ) ^ 2) *
          (∑ n ∈ Finset.range (m + 1), (vaughanThird n u v) ^ 2) := by
  haveI : NeZero q := ⟨Nat.ne_of_gt hq⟩
  let a : ℤ → ℂ := fun n => if 0 ≤ n then (vaughanThird n.toNat u v : ℂ) else 0
  let M : ℤ := -1
  let N : ℕ := m + 1
  -- Icc (M+1) (M+N) = Icc 0 (m:ℤ)
  have hIcc : Finset.Icc (M + 1) (M + N) = Finset.Icc (0 : ℤ) (m : ℤ) := by
    dsimp [M, N]
    have h2 : (-1 : ℤ) + ((m : ℤ) + 1) = (m : ℤ) := by omega
    rw [h2]
  -- Coefficient identity: a (n : ℤ) = vaughanThird n u v.
  have ha : ∀ n : ℕ, a (n : ℤ) = (vaughanThird n u v : ℂ) := by
    intro n
    simp [a]
  -- Character sum: Σ_{Icc} a n·χ(n) = panTypeIIV3CharSum q m u v χ.
  have hchar : ∀ χ : DirichletCharacter ℂ q,
      (∑ n ∈ Finset.Icc (0 : ℤ) (m : ℤ), a n * χ (n : ZMod q)) =
        panTypeIIV3CharSum q m u v χ := by
    intro χ
    unfold panTypeIIV3CharSum
    rw [← sum_range_to_Icc_int (f := fun n => (vaughanThird n u v : ℂ) * χ (n : ZMod q))
      (g := fun n => a n * χ (n : ZMod q))]
    · intro n
      simp [ha n]
  -- Reindex the charReal sum: Σ_{Icc} charReal(n·r/q)·a n = Σ_{range} charReal·vaughanThird.
  have hcr : ∀ r : ℕ,
      (∑ n ∈ Finset.Icc (0 : ℤ) (m : ℤ),
        (charReal ((n : ℝ) * ((r : ℝ) / (q : ℝ))) : ℂ) * a n) =
      ∑ n ∈ Finset.range (m + 1),
        (charReal ((n : ℝ) * ((r : ℝ) / (q : ℝ))) : ℂ) * (vaughanThird n u v : ℂ) := by
    intro r
    rw [← sum_range_to_Icc_int
      (f := fun n => (charReal ((n : ℝ) * ((r : ℝ) / (q : ℝ))) : ℂ) * (vaughanThird n u v : ℂ))
      (g := fun n => (charReal ((n : ℝ) * ((r : ℝ) / (q : ℝ))) : ℂ) * a n)]
    · intro n
      simp [ha n]
  -- characterSieveModulus_le (M = -1, N = m+1)
  have hcs := characterSieveModulus_le (q := q) a M N
  -- Left side: Σ_χ‖panTypeIIV3‖² = Σ_χ‖Σ_{Icc (M+1)(M+N)}‖².
  have hcsL : (∑ χ : DirichletCharacter ℂ q, ‖panTypeIIV3CharSum q m u v χ‖ ^ 2) =
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
      (∑ n ∈ Finset.range (m + 1), (vaughanThird n u v) ^ 2) := by
    rw [← sum_range_to_Icc_int (f := fun n => ‖(vaughanThird n u v : ℂ)‖ ^ 2)
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
  have hmain : (q : ℝ) / (q.totient : ℝ) * panTypeIICharSqSum q m u v ≤
      largeSieveBound (m + 1) (1 / (q : ℝ) ^ 2) *
        (∑ n ∈ Finset.range (m + 1), (vaughanThird n u v) ^ 2) := by
    calc
      (q : ℝ) / (q.totient : ℝ) * panTypeIICharSqSum q m u v
      = ((q : ℝ) / (q.totient : ℝ)) *
          (∑ χ : DirichletCharacter ℂ q, ‖panTypeIIV3CharSum q m u v χ‖ ^ 2) := by
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
            (∑ n ∈ Finset.range (m + 1), (vaughanThird n u v) ^ 2) := by
            rw [hIcc, hL2]
  -- Divide by q/φ to obtain S ≤ (φ/q)·T.
  calc
    panTypeIICharSqSum q m u v
        ≤ largeSieveBound (m + 1) (1 / (q : ℝ) ^ 2) *
            (∑ n ∈ Finset.range (m + 1), (vaughanThird n u v) ^ 2) /
              ((q : ℝ) / (q.totient : ℝ)) := by
          exact (le_div_iff₀ hqφ).mpr (by simpa [mul_comm] using hmain)
    _ = ((q.totient : ℝ) / (q : ℝ)) *
          largeSieveBound (m + 1) (1 / (q : ℝ) ^ 2) *
          (∑ n ∈ Finset.range (m + 1), (vaughanThird n u v) ^ 2) := by
          field_simp [show (q : ℝ) ≠ 0 by exact_mod_cast (Nat.ne_of_gt hq),
            show (q.totient : ℝ) ≠ 0 by exact_mod_cast (Nat.totient_pos.mpr hq).ne']

/-! ## 7. Replacing panTypeIICharSqrtMeanMaxY by a sum over y -/

/-- `panTypeIICharSqrtMean` is nonnegative, since absolute values
and square roots are nonnegative. -/
private lemma panTypeIICharSqrtMean_nonneg (y X q : ℕ) (f : ℕ → ℝ) (u v : ℕ) :
    0 ≤ panTypeIICharSqrtMean y X q f u v := by
  unfold panTypeIICharSqrtMean
  exact Finset.sum_nonneg (fun a ha =>
    mul_nonneg (div_nonneg (abs_nonneg _) (abs_nonneg _)) (Real.sqrt_nonneg _))

/-- **Maximum-to-sum bound**:
`panTypeIICharSqrtMeanMaxY ≤ Σ_{y≤x} panTypeIICharSqrtMean y`,
since the summands are nonnegative. -/
theorem panTypeIICharSqrtMeanMaxY_le_sum (X q x : ℕ) (f : ℕ → ℝ) (u v : ℕ) :
    panTypeIICharSqrtMeanMaxY X q x f u v ≤
      ∑ y ∈ Finset.range (x + 1), panTypeIICharSqrtMean y X q f u v := by
  unfold panTypeIICharSqrtMeanMaxY
  apply Finset.max'_le
  intro z hz
  rcases Finset.mem_image.mp hz with ⟨y, hy, rfl⟩
  exact Finset.single_le_sum (fun y' hy' => panTypeIICharSqrtMean_nonneg y' X q f u v) hy

/-! ## 8. Character square sums bounded by the sieve constant and the V3 square sum -/

/-- **Expanded per-modulus reduction**: after removing the maximum,
bound `panTypeIICharSqrtMeanMaxY` by elementary quantities.
For each `y ≤ x`, `a ≤ X`,
`√(Σ_χ‖V_χ(y/a)‖²)
 ≤ √((φ(q)/q)·largeSieveBound(y/a+1,1/q²))
   ·√(Σ_{n≤y/a} vaughanThird(n,u,v)²)`.
Only the sieve constant, V3 square sum, and outer weights remain.
A mean over moduli is a separate step involving Gauss-sum and
primitive-character analysis. -/
theorem panTypeIICharSqrtMeanMaxY_le_sieveSqrtSum (X q x : ℕ) (f : ℕ → ℝ) (u v : ℕ) (hq : 0 < q) :
    panTypeIICharSqrtMeanMaxY X q x f u v ≤
      ∑ y ∈ Finset.range (x + 1), ∑ a ∈ Finset.Icc 1 X,
        |f a| / |Real.log ((y / a : ℕ) : ℝ)| *
          Real.sqrt (((q.totient : ℝ) / (q : ℝ)) *
            largeSieveBound (y / a + 1) (1 / (q : ℝ) ^ 2)) *
          Real.sqrt (∑ n ∈ Finset.range (y / a + 1), (vaughanThird n u v) ^ 2) := by
  calc
    panTypeIICharSqrtMeanMaxY X q x f u v
        ≤ ∑ y ∈ Finset.range (x + 1), panTypeIICharSqrtMean y X q f u v :=
          panTypeIICharSqrtMeanMaxY_le_sum X q x f u v
    _ = ∑ y ∈ Finset.range (x + 1), ∑ a ∈ Finset.Icc 1 X,
        |f a| / |Real.log ((y / a : ℕ) : ℝ)| * Real.sqrt (panTypeIICharSqSum q (y / a) u v) := by
          rfl
    _ ≤ ∑ y ∈ Finset.range (x + 1), ∑ a ∈ Finset.Icc 1 X,
        |f a| / |Real.log ((y / a : ℕ) : ℝ)| *
          Real.sqrt (((q.totient : ℝ) / (q : ℝ)) *
            largeSieveBound (y / a + 1) (1 / (q : ℝ) ^ 2) *
            (∑ n ∈ Finset.range (y / a + 1), (vaughanThird n u v) ^ 2)) := by
          apply Finset.sum_le_sum
          intro y hy
          apply Finset.sum_le_sum
          intro a ha
          exact mul_le_mul_of_nonneg_left
            (Real.sqrt_le_sqrt (panTypeIICharSqSum_le_additiveSieve q (y / a) u v hq))
            (div_nonneg (abs_nonneg _) (abs_nonneg _))
    _ ≤ ∑ y ∈ Finset.range (x + 1), ∑ a ∈ Finset.Icc 1 X,
        |f a| / |Real.log ((y / a : ℕ) : ℝ)| *
          Real.sqrt (((q.totient : ℝ) / (q : ℝ)) *
            largeSieveBound (y / a + 1) (1 / (q : ℝ) ^ 2)) *
          Real.sqrt (∑ n ∈ Finset.range (y / a + 1), (vaughanThird n u v) ^ 2) := by
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
          rw [Real.sqrt_mul hAB (∑ n ∈ Finset.range (y / a + 1), (vaughanThird n u v) ^ 2)]
          simp [mul_assoc]

end

end AnalyticNumberTheory.Sieve
