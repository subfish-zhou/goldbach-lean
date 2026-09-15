import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Tactic

/-! # AnalyticNumberTheory.Sieve.VaughanIdentity

## Vaughan's identity

Vaughan (1977) decomposes the von Mangoldt function as

  Λ(n) = Σ_{d|n, d≤u} μ(d) log(n/d)
       + Σ_{d|n, u<d} Σ_{e|n/d, e≤v} μ(d) Λ(e)
       + Σ_{d|n, u<d} Σ_{e|n/d, v<e} μ(d) Λ(e).

This is a structural bridge in the Bombieri--Vinogradov and weighted
Pan mean-value arguments (`PanMeanValueUniform`). The first term is
Type I, a convolution of truncated `μ` with `log`; the third is
Type II, bilinear in two truncated factors. The middle term is
reorganized by Moebius inversion.

This module treats only exact finite algebra, with no analytic estimates.
The first identity holds for all `n,u,v`. Starting from mathlib's
`ArithmeticFunction.moebius_mul_log_eq_vonMangoldt` (`μ * log = Λ`),
split the convolution at `d ≤ u` / `u < d`, then at `e ≤ v` / `v < e`.

References:
  - Vaughan, R.C. (1977), Acta Arith. 32, 125-142
  - Halberstam & Richert, "Sieve Methods" (1974), Ch. 9-10
  - Iwaniec & Kowalski, "Analytic Number Theory" (2004), Ch. 13.4
-/

namespace AnalyticNumberTheory.Sieve

open Finset
open scoped ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open scoped ArithmeticFunction.zeta

noncomputable section

/-! ## 1. Truncated terms -/

/-- Type I main term: `Σ_{d|n, d≤u} μ(d) log(n/d)`. -/
noncomputable def vaughanFirst (n u : ℕ) : ℝ :=
  ∑ d ∈ n.divisors.filter (fun d => d ≤ u), ((μ d : ℤ) : ℝ) * Real.log ((n / d : ℕ) : ℝ)

/-- Intermediate term (Type I'):
`Σ_{d|n, u<d} Σ_{e|n/d, e≤v} μ(d) Λ(e)`. -/
noncomputable def vaughanSecond (n u v : ℕ) : ℝ :=
  ∑ d ∈ n.divisors.filter (fun d => u < d),
    ∑ e ∈ (n / d).divisors.filter (fun e => e ≤ v), ((μ d : ℤ) : ℝ) * Λ e

/-- Type II bilinear term:
`Σ_{d|n, u<d} Σ_{e|n/d, v<e} μ(d) Λ(e)`. -/
noncomputable def vaughanThird (n u v : ℕ) : ℝ :=
  ∑ d ∈ n.divisors.filter (fun d => u < d),
    ∑ e ∈ (n / d).divisors.filter (fun e => v < e), ((μ d : ℤ) : ℝ) * Λ e

/-- Middle term in the classical three-term form (Type I'):
`Σ_{d|n, d≤u} Σ_{e|n/d, e≤v} μ(d) Λ(e)`. -/
noncomputable def vaughanMiddle (n u v : ℕ) : ℝ :=
  ∑ d ∈ n.divisors.filter (fun d => d ≤ u),
    ∑ e ∈ (n / d).divisors.filter (fun e => e ≤ v), ((μ d : ℤ) : ℝ) * Λ e

/-! ## 2. Exact three-part identity -/

/-- **Vaughan's identity, exact form**: for any `n u v : ℕ`,
`Λ n = vaughanFirst n u + vaughanSecond n u v + vaughanThird n u v`.
No hypotheses `n > u` or `n > v` are needed; this is finite
convolution algebra. -/
theorem vaughanIdentity (n u v : ℕ) :
    Λ n = vaughanFirst n u + vaughanSecond n u v + vaughanThird n u v := by
  unfold vaughanFirst vaughanSecond vaughanThird
  have hΛ : Λ n = ∑ d ∈ n.divisors, ((μ d : ℤ) : ℝ) * Real.log ((n / d : ℕ) : ℝ) := by
    rw [← ArithmeticFunction.moebius_mul_log_eq_vonMangoldt]
    rw [ArithmeticFunction.mul_apply]
    rw [Nat.sum_divisorsAntidiagonal
      (f := fun i j => ((μ : ArithmeticFunction ℝ) i) * ArithmeticFunction.log j)]
    simp only [ArithmeticFunction.intCoe_apply, ArithmeticFunction.log_apply]
  rw [hΛ]
  rw [← Finset.sum_filter_add_sum_filter_not (s := n.divisors) (p := fun d => d ≤ u)]
  simp only [not_le]
  -- In the u < d part, replace log(n/d) by Σ_{e|n/d} Λ e.
  have hlog : (∑ d ∈ n.divisors.filter (fun d => u < d),
        ((μ d : ℤ) : ℝ) * Real.log ((n / d : ℕ) : ℝ)) =
      ∑ d ∈ n.divisors.filter (fun d => u < d),
        ((μ d : ℤ) : ℝ) * (∑ e ∈ (n / d).divisors, Λ e) := by
    congr 1 with d
    rw [← ArithmeticFunction.vonMangoldt_sum (n := n / d)]
  rw [hlog]
  -- Split each e-sum at e ≤ v / v < e and distribute the coefficient and sums.
  have hsplitE : (∑ d ∈ n.divisors.filter (fun d => u < d),
        ((μ d : ℤ) : ℝ) * (∑ e ∈ (n / d).divisors, Λ e)) =
      (∑ d ∈ n.divisors.filter (fun d => u < d),
          ∑ e ∈ (n / d).divisors.filter (fun e => e ≤ v), ((μ d : ℤ) : ℝ) * Λ e) +
        (∑ d ∈ n.divisors.filter (fun d => u < d),
          ∑ e ∈ (n / d).divisors.filter (fun e => v < e), ((μ d : ℤ) : ℝ) * Λ e) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    rw [Finset.mul_sum]
    rw [← Finset.sum_filter_add_sum_filter_not (s := (n / d).divisors) (p := fun e => e ≤ v)]
    simp only [not_le]
  rw [hsplitE]
  abel

/-! ## 3. Classical three-term form for n > v -/

/-- Moebius divisor sum: `Σ_{d|m} μ(d) = [m=1]`,
from `μ * ζ = 1` (the convolution unit) and `coe_mul_zeta_apply`. -/
theorem moebiusDivisorSum_eq_ite (m : ℕ) :
    (∑ d ∈ m.divisors, ((μ d : ℤ) : ℝ)) = if m = 1 then 1 else 0 := by
  have h : (((μ : ArithmeticFunction ℝ) * ζ) m) = (1 : ArithmeticFunction ℝ) m := by
    rw [ArithmeticFunction.coe_moebius_mul_coe_zeta]
  rw [ArithmeticFunction.coe_mul_zeta_apply] at h
  simp only [ArithmeticFunction.intCoe_apply] at h
  rw [h, ArithmeticFunction.one_apply]

/-- If `e | n` and `n ≠ 0`, then `n/e = 1 ↔ e = n`. -/
private theorem div_eq_one_iff_eq {n e : ℕ} (he : e ∣ n) (hn : n ≠ 0) :
    n / e = 1 ↔ e = n := by
  constructor
  · exact Nat.eq_of_dvd_of_div_eq_one he
  · intro rfl
    exact Nat.div_self (Nat.pos_of_ne_zero hn)

/-- **Exchange of Vaughan's double sum**:
rewrite `Σ_{d|n} Σ_{e|n/d, e≤v} μ(d)Λ(e)` as
`Σ_{e|n, e≤v} Λ(e)·Σ_{d|n/e} μ(d)` by swapping the finite
divisibility-indexed pairs `(d,e)`. -/
theorem vaughanDoubleSum_swap (n v : ℕ) :
    (∑ d ∈ n.divisors, ∑ e ∈ (n / d).divisors.filter (fun e => e ≤ v),
        ((μ d : ℤ) : ℝ) * Λ e) =
      ∑ e ∈ n.divisors.filter (fun e => e ≤ v),
        Λ e * (∑ d ∈ (n / e).divisors, ((μ d : ℤ) : ℝ)) := by
  simp_rw [Finset.mul_sum]
  rw [← Finset.sum_sigma (s := n.divisors) (t := fun d => (n / d).divisors.filter (fun e => e ≤ v))
    (f := fun x => ((μ x.1 : ℤ) : ℝ) * Λ x.2)]
  rw [← Finset.sum_sigma (s := n.divisors.filter (fun e => e ≤ v)) (t := fun e => (n / e).divisors)
    (f := fun x => Λ x.1 * ((μ x.2 : ℤ) : ℝ))]
  apply Finset.sum_bij (i := fun x _ => ⟨x.2, x.1⟩)
  · intro x hx
    rcases Finset.mem_sigma.mp hx with ⟨hd, he⟩
    rcases Finset.mem_filter.mp he with ⟨hem, hev⟩
    have hdn : x.1 ∣ n := (Nat.mem_divisors.mp hd).1
    have hn0 : n ≠ 0 := (Nat.mem_divisors.mp hd).2
    have hden : x.2 ∣ n / x.1 := (Nat.mem_divisors.mp hem).1
    have hen : x.2 ∣ n := dvd_trans hden (Nat.div_dvd_of_dvd hdn)
    rw [Finset.mem_sigma]
    constructor
    · rw [Finset.mem_filter]
      constructor
      · rw [Nat.mem_divisors]
        exact ⟨hen, hn0⟩
      · exact hev
    · rw [Nat.mem_divisors]
      constructor
      · exact (Nat.dvd_div_iff_mul_dvd hen).2
          (by simpa [Nat.mul_comm] using (Nat.dvd_div_iff_mul_dvd hdn).1 hden)
      · exact Nat.ne_of_gt (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hen)
          (Nat.pos_of_dvd_of_pos hen (Nat.pos_of_ne_zero hn0)))
  · intro a ha b hb h
    cases a with
    | mk d₁ e₁ =>
      cases b with
      | mk d₂ e₂ =>
          apply Sigma.ext
          · exact congrArg Sigma.snd h
          · exact heq_of_eq (congrArg Sigma.fst h)
  · intro b hb
    rcases Finset.mem_sigma.mp hb with ⟨he, hd⟩
    rcases Finset.mem_filter.mp he with ⟨hem, hev⟩
    have hen : b.1 ∣ n := (Nat.mem_divisors.mp hem).1
    have hn0 : n ≠ 0 := (Nat.mem_divisors.mp hem).2
    have hden : b.2 ∣ n / b.1 := (Nat.mem_divisors.mp hd).1
    have hdn : b.2 ∣ n := dvd_trans hden (Nat.div_dvd_of_dvd hen)
    refine ⟨⟨b.2, b.1⟩, ?_, rfl⟩
    rw [Finset.mem_sigma]
    constructor
    · rw [Nat.mem_divisors]
      exact ⟨hdn, hn0⟩
    · rw [Finset.mem_filter]
      constructor
      · rw [Nat.mem_divisors]
        constructor
        · exact (Nat.dvd_div_iff_mul_dvd hdn).2
            (by simpa [Nat.mul_comm] using (Nat.dvd_div_iff_mul_dvd hen).1 hden)
        · exact Nat.ne_of_gt (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hdn)
            (Nat.pos_of_dvd_of_pos hdn (Nat.pos_of_ne_zero hn0)))
      · exact hev
  · intro x hx
    rw [mul_comm]

/-- Full second-level sum:
`Σ_{d|n} Σ_{e|n/d, e≤v} μ(d)Λ(e) = Λ(n)·[n≤v]`. -/
theorem vaughanFullSecondSum (n v : ℕ) :
    (∑ d ∈ n.divisors, ∑ e ∈ (n / d).divisors.filter (fun e => e ≤ v),
        ((μ d : ℤ) : ℝ) * Λ e) = if n ≤ v then Λ n else 0 := by
  rw [vaughanDoubleSum_swap]
  rw [Finset.sum_congr rfl (by
    intro e he
    rw [moebiusDivisorSum_eq_ite, mul_ite, mul_one, mul_zero])]
  rw [← Finset.sum_filter (s := n.divisors.filter (fun e => e ≤ v))
    (p := fun e => n / e = 1)]
  have hfilt : (n.divisors.filter (fun e => e ≤ v)).filter (fun e => n / e = 1) =
      n.divisors.filter (fun e => e = n ∧ n ≤ v) := by
    ext e
    by_cases hn0 : n = 0
    · subst n
      simp
    · simp only [Finset.mem_filter, Nat.mem_divisors]
      constructor
      · rintro ⟨⟨⟨hed, hn0'⟩, hev⟩, hdiv⟩
        have heeq : e = n := (div_eq_one_iff_eq hed hn0').1 hdiv
        subst e
        simp [hn0', hev]
      · rintro ⟨⟨hed, hn0'⟩, ⟨heq, hnv⟩⟩
        subst e
        simp [hn0', hnv, Nat.div_self (Nat.pos_of_ne_zero hn0')]
  rw [hfilt]
  by_cases hn0 : n = 0
  · subst n
    simp
  · by_cases hnv : n ≤ v <;>
      simp [Finset.sum_filter, Nat.mem_divisors, hn0, hnv]

/-- **Vaughan's identity, classical three-term form**: for `n > v`,
`Λ n = vaughanFirst n u − vaughanMiddle n u v + vaughanThird n u v`.
This is the Type I/II form used in Bombieri--Vinogradov and weighted
Pan arguments. By `vaughanFullSecondSum`, the middle and second
terms cancel because
`Σ_{d|n} Σ_{e|n/d,e≤v} μ(d)Λ(e) = 0` when `n > v`. -/
theorem vaughanIdentity_threeTerm (n u v : ℕ) (hnv : v < n) :
    Λ n = vaughanFirst n u - vaughanMiddle n u v + vaughanThird n u v := by
  have hsplit : (∑ d ∈ n.divisors, ∑ e ∈ (n / d).divisors.filter (fun e => e ≤ v),
        ((μ d : ℤ) : ℝ) * Λ e) =
      (∑ d ∈ n.divisors.filter (fun d => u < d),
          ∑ e ∈ (n / d).divisors.filter (fun e => e ≤ v), ((μ d : ℤ) : ℝ) * Λ e) +
        (∑ d ∈ n.divisors.filter (fun d => d ≤ u),
          ∑ e ∈ (n / d).divisors.filter (fun e => e ≤ v), ((μ d : ℤ) : ℝ) * Λ e) := by
    rw [← Finset.sum_filter_add_sum_filter_not (s := n.divisors) (p := fun d => u < d)]
    simp only [not_lt]
  have hsecond : vaughanSecond n u v = -vaughanMiddle n u v := by
    unfold vaughanSecond vaughanMiddle
    have hfull : (∑ d ∈ n.divisors, ∑ e ∈ (n / d).divisors.filter (fun e => e ≤ v),
        ((μ d : ℤ) : ℝ) * Λ e) = 0 := by
      rw [vaughanFullSecondSum]
      rw [if_neg (not_le_of_gt hnv)]
    linarith
  rw [vaughanIdentity, hsecond]
  abel

end

end AnalyticNumberTheory.Sieve
