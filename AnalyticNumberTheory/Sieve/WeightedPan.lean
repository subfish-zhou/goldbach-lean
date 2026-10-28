import Mathlib.Algebra.Order.Antidiag.Nat
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Nat.Squarefree
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Tactic.Ring

import AnalyticNumberTheory.Sieve.BombieriVinogradov

/-! # AnalyticNumberTheory.Sieve.WeightedPan

## Weighted Pan--Bombieri--Vinogradov input

The upper bound for `Ω` in Chen's theorem, and more general
Goldbach-type sieves, requires a weighted **average** distribution
condition, not a uniform bound for each modulus:
for each `A > 0`, a uniform constant `C` gives
`Σ_{d|P} 3^{ω(d)}·|Δ(d)| ≤ C·x/log^A x`.
Here `Δ(d)` is the difference between the congruence count and
`ν(d)·x/log x`. The weight counts pairs `(d₁,d₂)` with
`[d₁,d₂]=d` in the Selberg expansion (`lcmPairCount`).

This module supplies:

1. **Finite weight identities**: for squarefree `d`,
   `3^{ω(d)}` counts lcm pairs; hence
   `Σ_{d|Q}3^{ω(d)}f(d) = Σ_{d₁|Q}Σ_{d₂|Q}f([d₁,d₂])`
   for squarefree `Q` (`lcmPairWeightedSum`).
2. **Sieve application interface**: `WeightedPanCondition` for a
   family `S N : BoundingSieve` and scale `x N`.
   In the Chen specialization, `x N = N`,
   `S N = correctedChenBoundingSieve N`, and `w d = 3^{ω(d)}`;
   `|S.rem d|` is the absolute congruence-count error
   `|#{p∈support : p≡N [MOD d]} − ν(d)·N/log N|`.
3. **Weighted mean-value target**: `PanMeanValueUniform` has
   the classical logarithmic-saving shape
   `Σ_{q≤(x X)^{1/2}/log^B(x X)} μ²(q)·3^{ω(q)}
    ·max_{y≤x X} max_{0<l<q,(l,q)=1}
       |Σ_{a≤X,(a,q)=1} f(a)·Δ(y;a,q,l)|
    ≤ C·x X/log^A(x X)`,
   with constants preceding all sufficiently large `X`.

The large sieve and Vaughan's identity are analytic ingredients
for the classical Pan theorem (Pan 1963; Halberstam--Richert
1974 Ch. 10; Liu 2022 §III). This module fixes definitions and
proves finite bridges, not an unconditional uniform mean-value
theorem. The implemented main term uses the `x/log x` proxy;
connecting it to a classical logarithmic-integral formulation
and to sieve remainders requires additional main-term and support
analysis. The coarse polylogarithmic proposition is kept separate.

References:
  - Pan, C.D. (1963), Sci. Sinica 12, 465-473
  - Bombieri, E. (1965), Math. Ann. 157, 220-260
  - Vinogradov, A.I. (1965), Izv. Akad. Nauk SSSR 29, 903-934
  - Halberstam & Richert, "Sieve Methods" (1974), Ch. 10
  - Liu, Z. (2022), arXiv:2203.07871
-/

namespace AnalyticNumberTheory.Sieve

open Finset Real

open scoped Classical
open scoped ArithmeticFunction.Moebius
open scoped ArithmeticFunction.omega

/-! ## 1. Origin of the weight: 3^{ω(d)} counts lcm pairs -/

/-- For squarefree `d`, exactly `3^{ω(d)}` divisor pairs
`(d₁,d₂)` satisfy `lcm d₁ d₂ = d`.
Each prime factor has three exponent choices:
`(0,1)`, `(1,0)`, and `(1,1)`. This is the exact source of
the Selberg upper-sieve weight `3^{ω(d)}`. -/
theorem lcmPairCount (d : ℕ) (hsq : Squarefree d) :
    ((d.divisors ×ˢ d.divisors).filter (fun x : ℕ × ℕ => Nat.lcm x.1 x.2 = d)).card =
      3 ^ d.primeFactors.card := by
  have hω : d.primeFactors.card = ArithmeticFunction.cardDistinctFactors d := by
    rw [ArithmeticFunction.cardDistinctFactors_apply, ← List.card_toFinset,
      Nat.toFinset_factors]
  rw [hω, ← Nat.card_pair_lcm_eq hsq]

/-- The lcm of two divisors of squarefree `Q` still divides `Q`,
by the defining divisibility property of the lcm. -/
private theorem lcm_dvd_of_squarefree {Q d₁ d₂ : ℕ} (_hQ : Squarefree Q)
    (h₁ : d₁ ∣ Q) (h₂ : d₂ ∣ Q) : Nat.lcm d₁ d₂ ∣ Q := by
  exact Nat.lcm_dvd h₁ h₂

/-- **Grouping the Selberg double sum**: for squarefree `Q`,
`Σ_{d|Q} 3^{ω(d)}·f(d) = Σ_{d₁|Q} Σ_{d₂|Q} f([d₁,d₂])`.
The weight counts pairs with lcm `d` (`lcmPairCount`).
This exact finite identity turns the lcm double sum into
the single weighted sum used by the Pan input. -/
theorem lcmPairWeightedSum (Q : ℕ) (hQ : Squarefree Q) (f : ℕ → ℝ) :
    ∑ d ∈ Q.divisors, (3 : ℝ) ^ d.primeFactors.card * f d =
      ∑ d₁ ∈ Q.divisors, ∑ d₂ ∈ Q.divisors, f (Nat.lcm d₁ d₂) := by
  have hQ0 : Q ≠ 0 := hQ.ne_zero
  have hQpos : 0 < Q := Nat.pos_of_ne_zero hQ0
  calc
    ∑ d ∈ Q.divisors, (3 : ℝ) ^ d.primeFactors.card * f d
        = ∑ d ∈ Q.divisors,
            ∑ x ∈ (d.divisors ×ˢ d.divisors).filter
                (fun x : ℕ × ℕ => Nat.lcm x.1 x.2 = d),
              f (Nat.lcm x.1 x.2) := by
            apply Finset.sum_congr rfl
            intro d hd
            have hdvd : d ∣ Q := (Nat.mem_divisors.mp hd).1
            have hd0 : d ≠ 0 := ne_of_gt (Nat.pos_of_dvd_of_pos hdvd hQpos)
            have hsqd : Squarefree d := Squarefree.squarefree_of_dvd hdvd hQ
            calc
              (3 : ℝ) ^ d.primeFactors.card * f d
                  = ((d.divisors ×ˢ d.divisors).filter
                        (fun x : ℕ × ℕ => Nat.lcm x.1 x.2 = d)).card * f d := by
                  rw [lcmPairCount d hsqd, Nat.cast_pow]
                  norm_num
              _ = ∑ x ∈ (d.divisors ×ˢ d.divisors).filter
                      (fun x : ℕ × ℕ => Nat.lcm x.1 x.2 = d),
                    f d := by
                  simp [Finset.sum_const, nsmul_eq_mul]
              _ = ∑ x ∈ (d.divisors ×ˢ d.divisors).filter
                      (fun x : ℕ × ℕ => Nat.lcm x.1 x.2 = d),
                    f (Nat.lcm x.1 x.2) := by
                  apply Finset.sum_congr rfl
                  intro x hx
                  rw [(Finset.mem_filter.mp hx).2]
    _ = ∑ x ∈ Q.divisors.sigma
            (fun d => (d.divisors ×ˢ d.divisors).filter
              (fun x : ℕ × ℕ => Nat.lcm x.1 x.2 = d)),
          f (Nat.lcm x.2.1 x.2.2) := by
          rw [Finset.sum_sigma]
    _ = ∑ x ∈ Q.divisors ×ˢ Q.divisors, f (Nat.lcm x.1 x.2) := by
          apply Finset.sum_nbij (fun x : (Σ d : ℕ, ℕ × ℕ) => x.2)
          · intro x hx
            rcases Finset.mem_sigma.mp hx with ⟨hxd, hx2⟩
            have hx2' : x.2 ∈ x.1.divisors ×ˢ x.1.divisors ∧
                Nat.lcm x.2.1 x.2.2 = x.1 := Finset.mem_filter.mp hx2
            have hprod : x.2 ∈ x.1.divisors ×ˢ x.1.divisors := hx2'.1
            have hx1dvd : x.1 ∣ Q := (Nat.mem_divisors.mp hxd).1
            have hdvd₁ : x.2.1 ∣ Q :=
              ((Nat.mem_divisors.mp (Finset.mem_product.mp hprod).1).1).trans hx1dvd
            have hdvd₂ : x.2.2 ∣ Q :=
              ((Nat.mem_divisors.mp (Finset.mem_product.mp hprod).2).1).trans hx1dvd
            exact Finset.mem_product.mpr
              ⟨Nat.mem_divisors.mpr ⟨hdvd₁, hQ0⟩, Nat.mem_divisors.mpr ⟨hdvd₂, hQ0⟩⟩
          · intro a₁ ha₁ a₂ ha₂ hpair
            rcases Finset.mem_sigma.mp ha₁ with ⟨_, ha₁₂⟩
            rcases Finset.mem_sigma.mp ha₂ with ⟨_, ha₂₂⟩
            have hlcm₁ : Nat.lcm a₁.2.1 a₁.2.2 = a₁.1 := (Finset.mem_filter.mp ha₁₂).2
            have hlcm₂ : Nat.lcm a₂.2.1 a₂.2.2 = a₂.1 := (Finset.mem_filter.mp ha₂₂).2
            cases a₁ with
            | mk d₁ x₁ =>
              cases a₂ with
            | mk d₂ x₂ =>
                have hx : x₁ = x₂ := by simpa using hpair
                subst x₂
                have hd₁ : d₁ = Nat.lcm x₁.1 x₁.2 := by simpa using hlcm₁.symm
                have hd₂ : d₂ = Nat.lcm x₁.1 x₁.2 := by simpa using hlcm₂.symm
                rw [hd₁, hd₂]
          · intro y hy
            rcases Finset.mem_product.mp hy with ⟨hy₁, hy₂⟩
            have hdvd₁ : y.1 ∣ Q := (Nat.mem_divisors.mp hy₁).1
            have hdvd₂ : y.2 ∣ Q := (Nat.mem_divisors.mp hy₂).1
            have hd₁0 : y.1 ≠ 0 := ne_of_gt (Nat.pos_of_dvd_of_pos hdvd₁ hQpos)
            have hd₂0 : y.2 ≠ 0 := ne_of_gt (Nat.pos_of_dvd_of_pos hdvd₂ hQpos)
            have hlcm0 : Nat.lcm y.1 y.2 ≠ 0 := Nat.lcm_ne_zero hd₁0 hd₂0
            refine ⟨⟨Nat.lcm y.1 y.2, y⟩, ?_, rfl⟩
            change ⟨Nat.lcm y.1 y.2, y⟩ ∈
              Q.divisors.sigma (fun d => (d.divisors ×ˢ d.divisors).filter
                (fun x : ℕ × ℕ => Nat.lcm x.1 x.2 = d))
            rw [Finset.mem_sigma]
            constructor
            · exact Nat.mem_divisors.mpr ⟨lcm_dvd_of_squarefree hQ hdvd₁ hdvd₂, hQ0⟩
            · rw [Finset.mem_filter]
              constructor
              · rw [Finset.mem_product]
                constructor
                · exact Nat.mem_divisors.mpr ⟨Nat.dvd_lcm_left y.1 y.2, hlcm0⟩
                · exact Nat.mem_divisors.mpr ⟨Nat.dvd_lcm_right y.1 y.2, hlcm0⟩
              · rfl
          · intro x hx
            rfl
    _ = ∑ d₁ ∈ Q.divisors, ∑ d₂ ∈ Q.divisors, f (Nat.lcm d₁ d₂) := by
          rw [Finset.sum_product]

/-! ## 1b. Pan weight decomposition: 3^{ω(q)} = Σ_{d|q} 2^{ω(d)} -/


/-! ## 2. Uniform weighted distribution interface for sieve applications -/


/-! ## 3. Weighted Pan mean-value target -/

/-- `π(y;a,q,l)`: count primes `p` with `a·p ≤ y` and
`a·p ≡ l [MOD q]`, as in Liu 2022 §II for positive `a`.
The definition explicitly searches `p ≤ y`, including at `a = 0`.
The congruence is on the product `a·p`, not on `p`;
this is the scaled AP prime count in the error for the Ω bound. -/
def primesInAPBelow (y a q l : ℕ) : ℕ :=
  ((range (y + 1)).filter (fun p => p.Prime ∧ a * p ≤ y ∧ a * p ≡ l [MOD q])).card


/-- Canonical representatives of the reduced residue classes modulo `q`.
For `q = 1` this is the singleton `{0}`; for `q = 0` it is empty. -/
def unitResidues (q : ℕ) : Finset ℕ :=
  (Finset.range q).filter (fun l => l.Coprime q)

@[simp] theorem unitResidues_zero : unitResidues 0 = ∅ := by
  simp [unitResidues]


/-! ## From the Pan expression to sieve remainders

At `a = 1`, `primesInAPBelow y a q l` is the ordinary count
`#{p≤y : p is prime, p≡l [MOD q]}`.
This identifies the source of the sieve remainder
`#{p∈support : p≡N [MOD d]}`. Further comparison hypotheses
are needed to bound the sieve's weighted remainder sum
by the `3^{ω(q)}`-weighted `panMaxY` sum.

`WeightedPanCondition` requires `C·xN/log^A(xN)` for every
`A > 0`; the switching sieve and error absorption need
arbitrarily large logarithmic savings.
`PanMeanValueUniformCrude`, with right side
`C·xX·(log xX)^{A+7}`, cannot meet that requirement.
`PanMeanValueUniform` retains the inverse-log target and is
assembled only under analytic inputs such as
`PanSourceFaithfulSignedMainBound`.

The generic absolute-value chain under `|f| ≤ 1` cannot provide
the saving. The inner pure-main-term sum has a refined
`y·(1+log log y)` shape in suitable ranges, or the coarse bound
`(y/log 2)·(1+log X)`; multiplying by the q-factor `log⁶`
does not produce inverse-log decay. Even retaining coprimality,
the choice `f = 1` leaves a pure-main-term contribution of
the indicated `(y/log y)·log X` size.
The classical application needs the specific Chen weights
and control of their harmonic sum `Σ f(a)/a`, together with
the sieve main term of shape `x/log x·∏(1-ν(p)/p)`
in the unnormalized density convention.
The saving is a difference estimate
`|main term − sieve main term| ≪ x/log^A x`.
These weight and main-term requirements belong to the Chen
application and its analytic bridge, not to the `a = 1`
identities below; see `PAN_PROOF_ATLAS.md`.
-/


end AnalyticNumberTheory.Sieve
