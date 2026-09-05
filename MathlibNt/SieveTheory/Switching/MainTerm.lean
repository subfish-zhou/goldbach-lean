import MathlibNt.SieveTheory.Switching.CorrectedSievePanBridge

/-!
# Mertens products and the corrected main term

The exact Möbius lower sieve, Selberg divisor products, and truncated singular
series yield uniform lower bounds and the asymptotic order of the main term.

All declarations retain the `MathlibNt.SieveTheory.SwitchingPrinciple` namespace.
-/

open scoped ArithmeticFunction.Moebius
open scoped ArithmeticFunction.zeta

set_option maxHeartbeats 6000000

namespace MathlibNt.SieveTheory.SwitchingPrinciple

open Real Finset
open MeasureTheory intervalIntegral

open scoped Classical
open scoped Asymptotics

namespace Internal
end Internal

open Internal

/-! ## Fundamental-lemma-level lower bound for the corrected sieve -/

/-- Key observation for the corrected-candidate lower bound: the ordinary Möbius function is a lower Möbius sequence, with equality.

`∑_{d | n} μ(d) = [n = 1]` (Möbius inversion, mathlib
`ArithmeticFunction.coe_zeta_mul_coe_moebius` + `coe_zeta_smul_apply`),
Thus `μ : ℕ → ℝ` satisfies `IsLowerMoebius`. -/
theorem moebius_real_isLowerMoebius :
    AnalyticNumberTheory.Sieve.IsLowerMoebius
      (fun d => ((ArithmeticFunction.moebius d : ℤ) : ℝ)) := by
  intro n
  have hz : (ArithmeticFunction.zeta * ArithmeticFunction.moebius :
      ArithmeticFunction ℝ) = (1 : ArithmeticFunction ℝ) := by
    simp
  have hzn : (ArithmeticFunction.zeta * ArithmeticFunction.moebius :
      ArithmeticFunction ℝ) n = (1 : ArithmeticFunction ℝ) n := by
    rw [hz]
  have hsum : (∑ i ∈ n.divisors,
      ((ArithmeticFunction.moebius i : ℤ) : ℝ)) =
      if n = 1 then (1 : ℝ) else 0 := by
    have hsmul : (ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
        (ArithmeticFunction.moebius : ArithmeticFunction ℝ) =
      (ArithmeticFunction.zeta : ArithmeticFunction ℝ) •
        (ArithmeticFunction.moebius : ArithmeticFunction ℝ) := by
      rfl
    rw [hsmul, ArithmeticFunction.coe_zeta_smul_apply (R := ℝ)
      (f := (ArithmeticFunction.moebius : ArithmeticFunction ℝ))] at hzn
    rw [ArithmeticFunction.one_apply] at hzn
    exact hzn
  exact le_of_eq hsum

/-- |μ(d)| ≤ 1, in the real-valued version. -/
theorem abs_moebius_real_le_one (d : ℕ) :
    |((ArithmeticFunction.moebius d : ℤ) : ℝ)| ≤ 1 := by
  exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := d))

/-- Corrected sieve product: `V(N) = ∏_{p | corrected sifting product} (1 - ν(p))`,
where `ν(p) = 1/(p-1)`. This is the same product as
`sieveProductPrimeFactors` in AnalyticNumberTheory. -/
noncomputable def correctedChenSieveProduct (N : ℕ) : ℝ :=
  ∏ p ∈ (correctedChenSiftingProduct N).primeFactors, (1 - correctedChenNu p)

/-- The Selberg main term for the ordinary Möbius function equals the corrected sieve product, exactly.

`∑_{d | P} μ(d)·ν(d) = ∏_{p | P} (1 - ν(p))`, the "one-minus" factorization for multiplicative functions
(mathlib `prodPrimeFactors_one_sub_of_squarefree`). This is the exact form of the JR main term
for corrected candidates: the main term is `V(N)`, without sieve-function asymptotics. -/
theorem mainSum_moebius_eq_correctedChenSieveProduct (N : ℕ) :
    (correctedChenBoundingSieve N).mainSum
        (fun d => ((ArithmeticFunction.moebius d : ℤ) : ℝ)) =
      correctedChenSieveProduct N := by
  rw [BoundingSieve.mainSum, correctedChenSieveProduct]
  change (∑ d ∈ (correctedChenSiftingProduct N).divisors,
      ((ArithmeticFunction.moebius d : ℤ) : ℝ) * correctedChenNu d) =
    ∏ p ∈ (correctedChenSiftingProduct N).primeFactors, (1 - correctedChenNu p)
  rw [← ArithmeticFunction.IsMultiplicative.prodPrimeFactors_one_sub_of_squarefree
    correctedChenNu (AnalyticNumberTheory.Sieve.goldbachNu_isMultiplicative)
    (correctedChenSiftingProduct_squarefree N)]

/-- The Möbius error sum is bounded by the unit-coefficient error sum: |μ(d)| ≤ 1 ⇒ errSum(μ) ≤ errSum(1). -/
theorem correctedChenErrSum_moebius_le_errSum_one (N : ℕ) :
    (correctedChenBoundingSieve N).errSum
        (fun d => ((ArithmeticFunction.moebius d : ℤ) : ℝ)) ≤
      (correctedChenBoundingSieve N).errSum (fun _ => 1) := by
  unfold BoundingSieve.errSum
  apply Finset.sum_le_sum
  intro d hd
  have hmul : |((ArithmeticFunction.moebius d : ℤ) : ℝ)| *
        |(correctedChenBoundingSieve N).rem d| ≤
      (1 : ℝ) * |(correctedChenBoundingSieve N).rem d| :=
    mul_le_mul_of_nonneg_right (abs_moebius_real_le_one d) (abs_nonneg _)
  simpa using hmul

/-- **Fundamental-lemma-level lower bound for corrected candidates**.

  `card(correctedChenCandidates N) ≥ X·V(N) − errSum(1)`

This holds unconditionally for **all** `N`, with total mass `X = N/log N`, corrected sieve product `V(N)`,
and explicit divisor error sum `errSum(1) = Σ_{d | P} |rem d|`.

Classical counterpart: the fundamental-lemma/linear-sieve lower bound `S(A,z) ≥ X·V(z) - Σ_{d ≤ D} |R_d|`.
The proof uses only the ordinary Möbius function, which is itself an exact lower Möbius sequence,
so the main term is exactly `X·V(N)` and no asymptotic for `f(s)` is needed. This distinguishes
the corrected candidates, which require only that `N-p` have no prime factor below `z`,
from the historical W candidates, which impose an additional medium-prime condition. The remaining analytic inputs are:
  (1) a uniform Mertens-type lower bound for `V(N)`, giving a main term `≫ N/log²N`;
  (2) weighted Pan control of `errSum(1)`;
  (3) a uniform upper bound for `correctedChenOmega`. -/
theorem correctedChenCandidates_card_ge_X_mul_sieveProduct_sub_errSum (N : ℕ) :
    (correctedChenBoundingSieve N).totalMass * correctedChenSieveProduct N -
        (correctedChenBoundingSieve N).errSum (fun _ => 1) ≤
      (correctedChenCandidates N).card := by
  let mu : ℕ → ℝ := fun d => ((ArithmeticFunction.moebius d : ℤ) : ℝ)
  have hseam := correctedChenCandidates_card_ge_mainSum_sub_errSum N mu
    moebius_real_isLowerMoebius
  have hmain : (correctedChenBoundingSieve N).mainSum mu = correctedChenSieveProduct N := by
    simpa [mu] using mainSum_moebius_eq_correctedChenSieveProduct N
  have herr : (correctedChenBoundingSieve N).errSum mu ≤
      (correctedChenBoundingSieve N).errSum (fun _ => 1) := by
    simpa [mu] using correctedChenErrSum_moebius_le_errSum_one N
  calc
    (correctedChenBoundingSieve N).totalMass * correctedChenSieveProduct N -
        (correctedChenBoundingSieve N).errSum (fun _ => 1)
      ≤ (correctedChenBoundingSieve N).totalMass *
            (correctedChenBoundingSieve N).mainSum mu -
          (correctedChenBoundingSieve N).errSum mu := by
      rw [hmain]
      linarith
    _ ≤ (correctedChenCandidates N).card := hseam

/-- At a sieved prime `2 < p < z` with `p ∤ N`, the corrected Goldbach
density factor satisfies `(1 - ν(p))⁻¹ = (p-1)/(p-2)`. -/
theorem correctedChenNu_inv_prime {N p : ℕ} (hp : p.Prime) (hp2 : 2 < p) :
    (1 - correctedChenNu p)⁻¹ = ((p : ℝ) - 1) / ((p : ℝ) - 2) := by
  rw [AnalyticNumberTheory.Sieve.goldbachNu_apply_prime hp]
  have hp2r : (2 : ℝ) < p := by exact_mod_cast hp2
  have hpm1 : (p : ℝ) - 1 ≠ 0 := by linarith
  have hpm2 : (p : ℝ) - 2 ≠ 0 := by linarith
  field_simp [hpm1, hpm2]
  have hcancel : ((-2 : ℝ) + p) * ((-2 : ℝ) + p)⁻¹ = 1 := by
    convert mul_inv_cancel₀ hpm2 using 1
    ring
  ring_nf at hcancel ⊢
  exact hcancel

/-- At a sieved prime, the corrected density factor splits into the
Mertens-type `p/(p-1)` and the reciprocal singular-series local factor. -/
theorem correctedChenNu_inv_prime_localFactor {N p : ℕ} (hp : p.Prime)
    (hp2 : 2 < p) (hpn : ¬ p ∣ N) :
    (1 - correctedChenNu p)⁻¹ =
      (p : ℝ) / (p - 1) * (AnalyticNumberTheory.Sieve.localFactor p N)⁻¹ := by
  rw [AnalyticNumberTheory.Sieve.localFactor_of_not_dvd hp hp2 hpn]
  have hp2r : (2 : ℝ) < p := by exact_mod_cast hp2
  have hpm1 : (p : ℝ) - 1 ≠ 0 := by linarith
  have hpm2 : (p : ℝ) - 2 ≠ 0 := by linarith
  have hrhs : (p : ℝ) / (p - 1) * ((p : ℝ) * (p - 2) / (p - 1) ^ 2)⁻¹ =
      (p - 1) / (p - 2) := by
    field_simp [hpm1, hpm2]
  rw [hrhs]
  exact correctedChenNu_inv_prime (N := N) hp hp2

/-- The corrected Selberg divisor sum splits into the Mertens-type prime
product over the sieved primes and the reciprocal of their singular-series
local-factor product.  This is the finite seam at which the exact Mertens
product formula and the singular series enter the main term. -/
theorem correctedChenSelbergSum_eq_mertens_mul_localFactor_inv (N : ℕ) :
    ∑ d ∈ (correctedChenBoundingSieve N).prodPrimes.divisors,
      (correctedChenBoundingSieve N).selbergTerms d =
      (∏ p ∈ (correctedChenSiftingProduct N).primeFactors, (p : ℝ) / (p - 1)) *
      (∏ p ∈ (correctedChenSiftingProduct N).primeFactors,
          AnalyticNumberTheory.Sieve.localFactor p N)⁻¹ := by
  rw [AnalyticNumberTheory.Sieve.selbergSum_eq_prod_inv]
  rw [← Finset.prod_inv_distrib]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hpcond := (prime_dvd_correctedChenSiftingProduct hp_prime).mp
    (Nat.dvd_of_mem_primeFactors hp)
  exact correctedChenNu_inv_prime_localFactor hp_prime hpcond.2.1 hpcond.2.2

/-! ## Main-term asymptotics: Mertens products and the singular series -/

/-- The corrected Selberg divisor sum factors as the product over the sieved
primes of `(1 - ν(p))⁻¹ = (p-1)/(p-2)`. -/
private theorem correctedChenSelbergSum_eq_prod_ratio (N : ℕ) :
    (∑ d ∈ (correctedChenBoundingSieve N).prodPrimes.divisors,
      (correctedChenBoundingSieve N).selbergTerms d) =
      ∏ p ∈ ((Finset.range (correctedChenZ N)).filter
        (fun p => p.Prime ∧ 2 < p ∧ ¬ p ∣ N)), ((p : ℝ) - 1) / ((p : ℝ) - 2) := by
  rw [AnalyticNumberTheory.Sieve.selbergSum_eq_prod_inv]
  simp only [correctedChenBoundingSieve]
  rw [correctedChenSiftingProduct_primeFactors]
  apply Finset.prod_congr rfl
  intro p hp
  rcases Finset.mem_filter.mp hp with ⟨hpz, hpP, hp2, hpn⟩
  exact correctedChenNu_inv_prime (N := N) hpP hp2

/-- The Mertens-type factor `p/(p-1)` (real subtraction). -/
private noncomputable def mertensTypeFactor (p : ℕ) : ℝ :=
  (p : ℝ) / ((p : ℝ) - 1)

/-- Partition of the primes `< z` into `p = 2`, `2 < p ∧ p | N`, and
`2 < p ∧ ¬ p | N`. -/
private theorem sievedPrimePartition (N : ℕ) :
    ((Finset.range (correctedChenZ N)).filter Nat.Prime) =
      ((Finset.range (correctedChenZ N)).filter (fun p => p.Prime ∧ p = 2)) ∪
      ((Finset.range (correctedChenZ N)).filter (fun p => p.Prime ∧ 2 < p ∧ p ∣ N)) ∪
      ((Finset.range (correctedChenZ N)).filter (fun p => p.Prime ∧ 2 < p ∧ ¬ p ∣ N)) := by
  ext p
  simp only [mem_filter, mem_union, mem_range]
  constructor
  · intro hp
    rcases hp with ⟨hpz, hpp⟩
    rcases eq_or_lt_of_le hpp.two_le with hpeq | hplt
    · exact Or.inl (Or.inl ⟨hpz, hpp, hpeq.symm⟩)
    · by_cases hpd : p ∣ N
      · exact Or.inl (Or.inr ⟨hpz, hpp, hplt, hpd⟩)
      · exact Or.inr ⟨hpz, hpp, hplt, hpd⟩
  · intro hp
    rcases hp with hpA | hpBC
    · rcases hpA with ⟨hpz, hpp, _⟩ | ⟨hpz, hpp, _, _⟩ <;> exact ⟨hpz, hpp⟩
    · rcases hpBC with ⟨hpz, hpp, _, _⟩
      exact ⟨hpz, hpp⟩

/-- The `p = 2` slice and the `p | N` slice are disjoint. -/
private theorem sievedPrimeDisjoint_a_b (N : ℕ) :
    Disjoint ((Finset.range (correctedChenZ N)).filter (fun p => p.Prime ∧ p = 2))
      ((Finset.range (correctedChenZ N)).filter (fun p => p.Prime ∧ 2 < p ∧ p ∣ N)) := by
  rw [Finset.disjoint_left]
  intro p hp1 hp2
  rcases Finset.mem_filter.mp hp1 with ⟨_, _, hpeq⟩
  rcases Finset.mem_filter.mp hp2 with ⟨_, _, hplt, _⟩
  omega

/-- The `p = 2` slice and the `¬ p | N` slice are disjoint. -/
private theorem sievedPrimeDisjoint_a_c (N : ℕ) :
    Disjoint ((Finset.range (correctedChenZ N)).filter (fun p => p.Prime ∧ p = 2))
      ((Finset.range (correctedChenZ N)).filter (fun p => p.Prime ∧ 2 < p ∧ ¬ p ∣ N)) := by
  rw [Finset.disjoint_left]
  intro p hp1 hp2
  rcases Finset.mem_filter.mp hp1 with ⟨_, _, hpeq⟩
  rcases Finset.mem_filter.mp hp2 with ⟨_, _, hplt, _⟩
  omega

/-- The `p | N` slice and the `¬ p | N` slice are disjoint. -/
private theorem sievedPrimeDisjoint_b_c (N : ℕ) :
    Disjoint ((Finset.range (correctedChenZ N)).filter (fun p => p.Prime ∧ 2 < p ∧ p ∣ N))
      ((Finset.range (correctedChenZ N)).filter (fun p => p.Prime ∧ 2 < p ∧ ¬ p ∣ N)) := by
  rw [Finset.disjoint_left]
  intro p hp1 hp2
  rcases Finset.mem_filter.mp hp1 with ⟨_, _, _, hpd⟩
  rcases Finset.mem_filter.mp hp2 with ⟨_, _, _, hpn⟩
  exact hpn hpd

/-- The union of the first two slices is disjoint from the `¬ p | N` slice. -/
private theorem sievedPrimeDisjoint_ab_c (N : ℕ) :
    Disjoint (((Finset.range (correctedChenZ N)).filter (fun p => p.Prime ∧ p = 2)) ∪
      ((Finset.range (correctedChenZ N)).filter (fun p => p.Prime ∧ 2 < p ∧ p ∣ N)))
      ((Finset.range (correctedChenZ N)).filter (fun p => p.Prime ∧ 2 < p ∧ ¬ p ∣ N)) := by
  rw [Finset.disjoint_left]
  intro p hp1 hp2
  rcases Finset.mem_union.mp hp1 with hpa | hpb
  · rcases Finset.mem_filter.mp hpa with ⟨_, _, hpeq⟩
    rcases Finset.mem_filter.mp hp2 with ⟨_, _, hplt, _⟩
    omega
  · rcases Finset.mem_filter.mp hpb with ⟨_, _, _, hpd⟩
    rcases Finset.mem_filter.mp hp2 with ⟨_, _, _, hpn⟩
    exact hpn hpd

/-- Local factor at `p = 2` equals `p/(p-1)` for even `N`. -/
private theorem localFactor_eq_mertensTypeFactor_p2 (N : ℕ) (hN : Even N) :
    AnalyticNumberTheory.Sieve.localFactor 2 N = mertensTypeFactor 2 := by
  rw [AnalyticNumberTheory.Sieve.localFactor_two hN]
  norm_num [mertensTypeFactor]

/-- Local factor at a dividing odd prime equals `p/(p-1)`. -/
private theorem localFactor_eq_mertensTypeFactor_dvd {N p : ℕ} (hp : p.Prime)
    (hlt : 2 < p) (hpd : p ∣ N) :
    AnalyticNumberTheory.Sieve.localFactor p N = mertensTypeFactor p := by
  rw [AnalyticNumberTheory.Sieve.localFactor_of_dvd hp hlt hpd]
  rfl

/-- At a non-dividing odd prime, `(p-1)/(p-2)` times the local factor equals
`p/(p-1)`. -/
private theorem localFactor_ratio_not_dvd {N p : ℕ} (hp : p.Prime) (hlt : 2 < p)
    (hpn : ¬ p ∣ N) :
    ((p : ℝ) - 1) / ((p : ℝ) - 2) * AnalyticNumberTheory.Sieve.localFactor p N =
      mertensTypeFactor p := by
  rw [AnalyticNumberTheory.Sieve.localFactor_of_not_dvd hp hlt hpn]
  have hp1 : (2 : ℝ) < p := by exact_mod_cast hlt
  have hpm1 : (p : ℝ) - 1 ≠ 0 := by linarith
  have hpm2 : (p : ℝ) - 2 ≠ 0 := by linarith
  unfold mertensTypeFactor
  field_simp [hpm1, hpm2]

/-- The corrected Selberg divisor sum times the truncated singular series at
`z - 1` is exactly the full Mertens-type prime product `∏_{p<z} p/(p-1)`.
This is the exact seam that restores the excluded `p = 2` and `p | N` local
factors back into `singularSeriesTruncated`. -/
private theorem correctedChenSelbergSum_mul_singularSeries_eq_mertensProd
    (N : ℕ) (hN : Even N) :
    (∑ d ∈ (correctedChenBoundingSieve N).prodPrimes.divisors,
      (correctedChenBoundingSieve N).selbergTerms d) *
      AnalyticNumberTheory.Sieve.singularSeriesTruncated N (correctedChenZ N - 1) =
      ∏ p ∈ ((Finset.range (correctedChenZ N)).filter Nat.Prime), mertensTypeFactor p := by
  let z := correctedChenZ N
  let R : Finset ℕ := (Finset.range z).filter Nat.Prime
  let A : Finset ℕ := (Finset.range z).filter (fun p => p.Prime ∧ p = 2)
  let B : Finset ℕ := (Finset.range z).filter (fun p => p.Prime ∧ 2 < p ∧ p ∣ N)
  let C : Finset ℕ := (Finset.range z).filter (fun p => p.Prime ∧ 2 < p ∧ ¬ p ∣ N)
  have hz : 1 ≤ correctedChenZ N := by
    unfold correctedChenZ
    omega
  have hrange : (Finset.range ((correctedChenZ N - 1) + 1)).filter Nat.Prime =
      (Finset.range (correctedChenZ N)).filter Nat.Prime := by
    rw [Nat.sub_add_cancel hz]
  have hR : R = A ∪ B ∪ C := by
    dsimp [R, A, B, C, z]
    exact sievedPrimePartition N
  have hS : (∑ d ∈ (correctedChenBoundingSieve N).prodPrimes.divisors,
      (correctedChenBoundingSieve N).selbergTerms d) =
      ∏ p ∈ C, ((p : ℝ) - 1) / ((p : ℝ) - 2) := by
    dsimp [C, z]
    exact correctedChenSelbergSum_eq_prod_ratio N
  have hSplit : (∏ p ∈ R, AnalyticNumberTheory.Sieve.localFactor p N) =
      (∏ p ∈ A, AnalyticNumberTheory.Sieve.localFactor p N) *
      (∏ p ∈ B, AnalyticNumberTheory.Sieve.localFactor p N) *
      (∏ p ∈ C, AnalyticNumberTheory.Sieve.localFactor p N) := by
    rw [hR]
    rw [Finset.prod_union (sievedPrimeDisjoint_ab_c N)]
    rw [Finset.prod_union (sievedPrimeDisjoint_a_b N)]
  have h𝔖 : AnalyticNumberTheory.Sieve.singularSeriesTruncated N (correctedChenZ N - 1) =
      ∏ p ∈ R, AnalyticNumberTheory.Sieve.localFactor p N := by
    simp [AnalyticNumberTheory.Sieve.singularSeriesTruncated, R, z, hrange]
  have hSplitMf : (∏ p ∈ R, mertensTypeFactor p) =
      (∏ p ∈ A, mertensTypeFactor p) * (∏ p ∈ B, mertensTypeFactor p) *
      (∏ p ∈ C, mertensTypeFactor p) := by
    rw [hR]
    rw [Finset.prod_union (sievedPrimeDisjoint_ab_c N)]
    rw [Finset.prod_union (sievedPrimeDisjoint_a_b N)]
  have hA : (∏ p ∈ A, AnalyticNumberTheory.Sieve.localFactor p N) = (∏ p ∈ A, mertensTypeFactor p) := by
    apply Finset.prod_congr rfl
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨_, _, hpeq⟩
    subst p
    exact localFactor_eq_mertensTypeFactor_p2 N hN
  have hB : (∏ p ∈ B, AnalyticNumberTheory.Sieve.localFactor p N) = (∏ p ∈ B, mertensTypeFactor p) := by
    apply Finset.prod_congr rfl
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨_, hpP, hlt, hpd⟩
    exact localFactor_eq_mertensTypeFactor_dvd hpP hlt hpd
  have hC : (∏ p ∈ C, ((p : ℝ) - 1) / ((p : ℝ) - 2) * AnalyticNumberTheory.Sieve.localFactor p N) =
      (∏ p ∈ C, mertensTypeFactor p) := by
    apply Finset.prod_congr rfl
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨_, hpP, hlt, hpn⟩
    exact localFactor_ratio_not_dvd hpP hlt hpn
  calc
    (∑ d ∈ (correctedChenBoundingSieve N).prodPrimes.divisors,
      (correctedChenBoundingSieve N).selbergTerms d) *
      AnalyticNumberTheory.Sieve.singularSeriesTruncated N (correctedChenZ N - 1)
        = (∏ p ∈ C, ((p : ℝ) - 1) / ((p : ℝ) - 2)) *
          (∏ p ∈ A, AnalyticNumberTheory.Sieve.localFactor p N) *
          (∏ p ∈ B, AnalyticNumberTheory.Sieve.localFactor p N) *
          (∏ p ∈ C, AnalyticNumberTheory.Sieve.localFactor p N) := by
          rw [hS, h𝔖, hSplit]
          ring
    _ = (∏ p ∈ A, AnalyticNumberTheory.Sieve.localFactor p N) *
        (∏ p ∈ B, AnalyticNumberTheory.Sieve.localFactor p N) *
        ((∏ p ∈ C, ((p : ℝ) - 1) / ((p : ℝ) - 2)) *
          (∏ p ∈ C, AnalyticNumberTheory.Sieve.localFactor p N)) := by ring
    _ = (∏ p ∈ A, AnalyticNumberTheory.Sieve.localFactor p N) *
        (∏ p ∈ B, AnalyticNumberTheory.Sieve.localFactor p N) *
        (∏ p ∈ C, ((p : ℝ) - 1) / ((p : ℝ) - 2) * AnalyticNumberTheory.Sieve.localFactor p N) := by
        rw [← Finset.prod_mul_distrib]
    _ = (∏ p ∈ A, mertensTypeFactor p) * (∏ p ∈ B, mertensTypeFactor p) *
        (∏ p ∈ C, mertensTypeFactor p) := by
        rw [hA, hB, hC]
    _ = ∏ p ∈ R, mertensTypeFactor p := by
        rw [← hSplitMf]

/-- The full Mertens-type product `∏_{p<z} p/(p-1)` equals the reciprocal of
the exact Mertens `primeProduct (z - 1)`. -/
private theorem mertensProd_eq_primeProduct_inv (N : ℕ) :
    (∏ p ∈ ((Finset.range (correctedChenZ N)).filter Nat.Prime), mertensTypeFactor p) =
      (MertensTheorem.primeProduct (correctedChenZ N - 1))⁻¹ := by
  have hz : 1 ≤ correctedChenZ N := by
    unfold correctedChenZ
    omega
  have hrange : (Finset.range ((correctedChenZ N - 1) + 1)).filter Nat.Prime =
      (Finset.range (correctedChenZ N)).filter Nat.Prime := by
    rw [Nat.sub_add_cancel hz]
  unfold mertensTypeFactor MertensTheorem.primeProduct
  rw [hrange]
  rw [← Finset.prod_inv_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  have hpP : p.Prime := (Finset.mem_filter.mp hp).2
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hpP.ne_zero
  have hp1 : (p : ℝ) ≠ 1 := by
    have : (1 : ℝ) < p := by exact_mod_cast hpP.one_lt
    linarith
  field_simp [hp0, hp1]

/-- **Main-term identity linking Mertens products to the singular series**: the corrected Selberg divisor sum
times the truncated singular series at `z - 1` equals the reciprocal of the
exact Mertens `primeProduct (z - 1)`.

This is the exact seam at which the main term connects the Mertens product
formula to the singular series: it restores the excluded `p = 2` and `p | N`
local factors (back into `singularSeriesTruncated`) and reduces the sieved
Selberg product to the full Mertens-type prime product `∏_{p<z} p/(p-1)`. -/
theorem correctedChenSelbergSum_mul_singularSeriesTruncated (N : ℕ) (hN : Even N) :
    (∑ d ∈ (correctedChenBoundingSieve N).prodPrimes.divisors,
      (correctedChenBoundingSieve N).selbergTerms d) *
      AnalyticNumberTheory.Sieve.singularSeriesTruncated N (correctedChenZ N - 1) =
      (MertensTheorem.primeProduct (correctedChenZ N - 1))⁻¹ := by
  rw [correctedChenSelbergSum_mul_singularSeries_eq_mertensProd N hN]
  exact mertensProd_eq_primeProduct_inv N

/-! ## Main-term lower bounds and the singular-series identity -/

/-- Positivity of the Mertens prime product: `∏_{p ≤ x}(1 - 1/p) > 0`. -/
theorem primeProduct_pos (x : ℕ) : 0 < MertensTheorem.primeProduct x := by
  unfold MertensTheorem.primeProduct
  exact Finset.prod_pos (fun p hp => by
    have hpP : p.Prime := (Finset.mem_filter.mp hp).2
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hpP.pos
    have hle : (1 : ℝ) < p := by exact_mod_cast hpP.one_lt
    have hlt1 : 1 / (p : ℝ) < 1 := (div_lt_iff₀ hp0).mpr (by simpa using hle)
    linarith)

/-- `selbergSum = 1 / V(N)`: invert the "one-minus" factorization of the Selberg divisor sum. -/
theorem correctedChenSelbergSum_eq_sieveProduct_inv (N : ℕ) :
    (∑ d ∈ (correctedChenBoundingSieve N).prodPrimes.divisors,
      (correctedChenBoundingSieve N).selbergTerms d) =
      (correctedChenSieveProduct N)⁻¹ := by
  rw [AnalyticNumberTheory.Sieve.selbergSum_eq_prod_inv]
  change (∏ p ∈ (correctedChenSiftingProduct N).primeFactors,
      (1 - correctedChenNu p)⁻¹) = (correctedChenSieveProduct N)⁻¹
  rw [correctedChenSieveProduct]
  rw [← Finset.prod_inv_distrib]

/-- **Main-term identity through the singular series**: the corrected sieve product equals the truncated singular series
times the exact Mertens product:

  V(N) = 𝔖_trunc(N, z-1) · primeProduct(z-1)

This is the exact identity turning `X·V(N)` into a main term of the form `X·𝔖·primeProduct(z-1)`:
`correctedChenSelbergSum_mul_singularSeriesTruncated`
invert `selbergSum·𝔖 = primeProduct⁻¹` and `selbergSum = V⁻¹`. -/
theorem correctedChenSieveProduct_eq_singularSeries_mul_primeProduct (N : ℕ) (hN : Even N) :
    correctedChenSieveProduct N =
      AnalyticNumberTheory.Sieve.singularSeriesTruncated N (correctedChenZ N - 1) *
        MertensTheorem.primeProduct (correctedChenZ N - 1) := by
  have h1 := correctedChenSelbergSum_mul_singularSeriesTruncated N hN
  have hsel := correctedChenSelbergSum_eq_sieveProduct_inv N
  rw [hsel] at h1
  have hVnz : correctedChenSieveProduct N ≠ 0 := by
    unfold correctedChenSieveProduct
    exact ne_of_gt (Finset.prod_pos (fun p hp => by
      have hpP : p.Prime := Nat.prime_of_mem_primeFactors hp
      have hpcond := (prime_dvd_correctedChenSiftingProduct hpP).mp
        (Nat.dvd_of_mem_primeFactors hp)
      have hlt : correctedChenNu p < 1 :=
        AnalyticNumberTheory.Sieve.goldbachNu_lt_one_of_prime hpP hpcond.2.1
      linarith))
  have h𝔖nz : AnalyticNumberTheory.Sieve.singularSeriesTruncated N (correctedChenZ N - 1) ≠ 0 := by
    apply ne_of_gt
    apply AnalyticNumberTheory.Sieve.singularSeriesTruncated_pos
    unfold correctedChenZ
    have hmax : 2 ≤ max 2 (Nat.floor ((N : ℝ) ^ (1 / 10 : ℝ))) := le_max_left _ _
    omega
  have hppnz : MertensTheorem.primeProduct (correctedChenZ N - 1) ≠ 0 :=
    ne_of_gt (primeProduct_pos (correctedChenZ N - 1))
  have h3 : (correctedChenSieveProduct N)⁻¹ =
      (MertensTheorem.primeProduct (correctedChenZ N - 1) *
        AnalyticNumberTheory.Sieve.singularSeriesTruncated N (correctedChenZ N - 1))⁻¹ := by
    have h := congrArg (fun t : ℝ =>
        t * (AnalyticNumberTheory.Sieve.singularSeriesTruncated N (correctedChenZ N - 1))⁻¹) h1
    rw [mul_assoc, mul_inv_cancel₀ h𝔖nz, mul_one] at h
    -- h : V⁻¹ = primeProduct⁻¹ * 𝔖⁻¹; goal: V⁻¹ = (primeProduct * 𝔖)⁻¹.
    rw [mul_inv]
    ring_nf
    exact h
  calc
    correctedChenSieveProduct N
        = ((correctedChenSieveProduct N)⁻¹)⁻¹ := by simp
    _ = (MertensTheorem.primeProduct (correctedChenZ N - 1) *
          AnalyticNumberTheory.Sieve.singularSeriesTruncated N (correctedChenZ N - 1))⁻¹⁻¹ := by
          rw [h3]
    _ = MertensTheorem.primeProduct (correctedChenZ N - 1) *
        AnalyticNumberTheory.Sieve.singularSeriesTruncated N (correctedChenZ N - 1) := by
          simp
    _ = AnalyticNumberTheory.Sieve.singularSeriesTruncated N (correctedChenZ N - 1) *
        MertensTheorem.primeProduct (correctedChenZ N - 1) := by
          ring

/-- **Uniform main-term lower bound**: there exist `c > 0` and a threshold `N₀` such that
`X·V(N) ≥ c·N/log²N` for all even `N ≥ N₀`.

The quantifiers `c`, `N₀` precede `∀ N`: the constants must not depend on `N`.
`correctedChenMainTerm_lower_of_estimates` derives this from three standard analytic inputs:
(1) a uniform lower bound for `𝔖_trunc`; (2) a Mertens lower bound for `primeProduct`;
(3) the parameter estimate `log(z-1) ≤ C·log N`. -/
def CorrectedChenMainTermLower : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ,
    ∀ N : ℕ, N₀ ≤ N → Even N →
      c * (N : ℝ) / (log (N : ℝ)) ^ 2 ≤
        (correctedChenBoundingSieve N).totalMass * correctedChenSieveProduct N

/-- **Pointwise assembly of the main-term lower bound**: given (1) `c𝔖 ≤ 𝔖_trunc`,
(2) the Mertens lower bound `cpp/log(z-1) ≤ primeProduct(z-1)`, and (3) the parameter estimate
`log(z-1) ≤ Clog·log N`, we obtain

  `c𝔖·cpp/Clog · N/log²N ≤ X·V(N)`.

The proof uses only `V = 𝔖_trunc·primeProduct(z-1)` and positivity/reciprocal arithmetic. -/
theorem correctedChenMainTerm_lower_of_estimates (N : ℕ) (hN : Even N) (hN2 : 2 ≤ N)
    (hz : 2 ≤ correctedChenZ N - 1)
    {c𝔖 cpp Clog : ℝ} (hc𝔖 : 0 < c𝔖) (hcpp : 0 < cpp) (hClog : 0 < Clog)
    (h𝔖 : c𝔖 ≤ AnalyticNumberTheory.Sieve.singularSeriesTruncated N (correctedChenZ N - 1))
    (hpp : cpp / log ((correctedChenZ N - 1 : ℕ) : ℝ) ≤
      MertensTheorem.primeProduct (correctedChenZ N - 1))
    (hlog : log ((correctedChenZ N - 1 : ℕ) : ℝ) ≤ Clog * log (N : ℝ)) :
    c𝔖 * cpp / Clog * (N : ℝ) / (log (N : ℝ)) ^ 2 ≤
      (correctedChenBoundingSieve N).totalMass * correctedChenSieveProduct N := by
  have hV : correctedChenSieveProduct N =
      AnalyticNumberTheory.Sieve.singularSeriesTruncated N (correctedChenZ N - 1) *
        MertensTheorem.primeProduct (correctedChenZ N - 1) :=
    correctedChenSieveProduct_eq_singularSeries_mul_primeProduct N hN
  have hlogN : 0 < log (N : ℝ) := by
    have : (1 : ℝ) < N := by exact_mod_cast (by omega : 1 < N)
    exact Real.log_pos this
  have hlogz : 0 < log ((correctedChenZ N - 1 : ℕ) : ℝ) := by
    have : (1 : ℝ) < (correctedChenZ N - 1 : ℕ) := by exact_mod_cast (by omega : 1 < correctedChenZ N - 1)
    exact Real.log_pos this
  have h𝔖pos : 0 < AnalyticNumberTheory.Sieve.singularSeriesTruncated N (correctedChenZ N - 1) :=
    AnalyticNumberTheory.Sieve.singularSeriesTruncated_pos N (correctedChenZ N - 1) (by omega)
  have hX : (correctedChenBoundingSieve N).totalMass = (N : ℝ) / log (N : ℝ) := rfl
  have h𝔖pp : c𝔖 * (cpp / log ((correctedChenZ N - 1 : ℕ) : ℝ)) ≤
      AnalyticNumberTheory.Sieve.singularSeriesTruncated N (correctedChenZ N - 1) *
        MertensTheorem.primeProduct (correctedChenZ N - 1) := by
    exact mul_le_mul h𝔖 hpp (le_of_lt (div_pos hcpp hlogz)) (le_of_lt h𝔖pos)
  have hle : c𝔖 * cpp / (Clog * log (N : ℝ)) ≤
      c𝔖 * (cpp / log ((correctedChenZ N - 1 : ℕ) : ℝ)) := by
    have hone : (Clog * log (N : ℝ))⁻¹ ≤ (log ((correctedChenZ N - 1 : ℕ) : ℝ))⁻¹ :=
      (inv_le_inv₀ (mul_pos hClog hlogN) hlogz).mpr hlog
    have hnonneg : 0 ≤ c𝔖 * cpp := mul_nonneg (le_of_lt hc𝔖) (le_of_lt hcpp)
    calc
      c𝔖 * cpp / (Clog * log (N : ℝ)) =
          c𝔖 * cpp * (Clog * log (N : ℝ))⁻¹ := by
            field_simp [ne_of_gt (mul_pos hClog hlogN)]
      _ ≤ c𝔖 * cpp * (log ((correctedChenZ N - 1 : ℕ) : ℝ))⁻¹ := by
            exact mul_le_mul_of_nonneg_left hone hnonneg
      _ = c𝔖 * (cpp / log ((correctedChenZ N - 1 : ℕ) : ℝ)) := by
            field_simp [hlogz.ne']
  calc
    c𝔖 * cpp / Clog * (N : ℝ) / (log (N : ℝ)) ^ 2
        = (N : ℝ) / log (N : ℝ) * (c𝔖 * cpp / (Clog * log (N : ℝ))) := by
          field_simp [hlogN.ne']
    _ ≤ (N : ℝ) / log (N : ℝ) * (c𝔖 * (cpp / log ((correctedChenZ N - 1 : ℕ) : ℝ))) := by
          exact mul_le_mul_of_nonneg_left hle (div_nonneg (by positivity) (le_of_lt hlogN))
    _ ≤ (correctedChenBoundingSieve N).totalMass *
          (AnalyticNumberTheory.Sieve.singularSeriesTruncated N (correctedChenZ N - 1) *
            MertensTheorem.primeProduct (correctedChenZ N - 1)) := by
          rw [hX]
          exact mul_le_mul_of_nonneg_left h𝔖pp (div_nonneg (by positivity) (le_of_lt hlogN))
    _ = (correctedChenBoundingSieve N).totalMass * correctedChenSieveProduct N := by
          rw [hV]

/-- Package three uniform analytic inputs into `CorrectedChenMainTermLower`:
(1) a uniform lower bound for `𝔖_trunc`; (2) a uniform Mertens lower bound for `primeProduct`;
(3) the parameter estimate `log(z-1) ≤ Clog·log N`; also assume (4) the parameter condition
(`2 ≤ N`、`2 ≤ z-1`、`M₀ ≤ z-1`). -/
theorem CorrectedChenMainTermLower_of_uniform_estimates
    {c𝔖 cpp Clog : ℝ} {M₀ N₀'' : ℕ}
    (hc𝔖 : 0 < c𝔖) (hcpp : 0 < cpp) (hClog : 0 < Clog)
    (h𝔖 : ∀ N : ℕ, ∀ z : ℕ, 2 ≤ z →
      c𝔖 ≤ AnalyticNumberTheory.Sieve.singularSeriesTruncated N z)
    (hpp : ∀ m : ℕ, M₀ ≤ m → 2 ≤ m →
      cpp / log (m : ℝ) ≤ MertensTheorem.primeProduct m)
    (hlog : ∀ N : ℕ, 2 ≤ N →
      log ((correctedChenZ N - 1 : ℕ) : ℝ) ≤ Clog * log (N : ℝ))
    (hparams : ∀ N : ℕ, N₀'' ≤ N →
      2 ≤ N ∧ 2 ≤ correctedChenZ N - 1 ∧ M₀ ≤ correctedChenZ N - 1) :
    CorrectedChenMainTermLower := by
  refine ⟨c𝔖 * cpp / Clog, ?_, ⟨N₀'', ?_⟩⟩
  · positivity
  · intro N hN hEven
    rcases hparams N hN with ⟨hN2, hz, hM⟩
    exact correctedChenMainTerm_lower_of_estimates N hEven hN2 hz hc𝔖 hcpp hClog
      (h𝔖 N (correctedChenZ N - 1) hz)
      (hpp (correctedChenZ N - 1) hM hz)
      (hlog N hN2)

/-! ## Parameter estimates linking Mertens products and the singular series -/

/-- Parameter estimate 1: the corrected sieve level satisfies `z - 1 ≤ N` in ℝ. -/
theorem correctedChenZ_sub_one_le_N {N : ℕ} (hN : 1 ≤ N) :
    ((correctedChenZ N - 1 : ℕ) : ℝ) ≤ N := by
  let x : ℝ := (N : ℝ) ^ (1 / 10 : ℝ)
  have hx0 : 0 ≤ x := by
    dsimp [x]
    exact Real.rpow_nonneg (by exact_mod_cast (Nat.zero_le N)) _
  by_cases hf : 2 ≤ Nat.floor x
  · have hz : correctedChenZ N = Nat.floor x := by
      unfold correctedChenZ
      exact max_eq_right hf
    have hxle : x ≤ (N : ℝ) := by
      have hx1 : 1 ≤ (N : ℝ) := by exact_mod_cast hN
      have hpow := Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num : (1 / 10 : ℝ) ≤ 1)
      -- hpow : N^(1/10) ≤ N^1
      simpa [x] using hpow
    calc
      ((correctedChenZ N - 1 : ℕ) : ℝ) ≤ (correctedChenZ N : ℝ) := by
        exact_mod_cast (Nat.sub_le (correctedChenZ N) 1)
      _ = (Nat.floor x : ℝ) := by rw [hz]
      _ ≤ x := Nat.floor_le hx0
      _ ≤ (N : ℝ) := hxle
  · have hz : correctedChenZ N = 2 := by
      unfold correctedChenZ
      change max 2 (Nat.floor x) = 2
      exact max_eq_left (by omega)
    rw [hz]
    norm_num
    exact_mod_cast hN

/-- Parameter estimate 2: for `N ≥ 3^10 = 59049`, the corrected sieve level satisfies `2 ≤ z - 1`. -/
theorem correctedChenZ_sub_one_ge_two_of_large {N : ℕ} (hN : 59049 ≤ N) :
    2 ≤ correctedChenZ N - 1 := by
  let x : ℝ := (N : ℝ) ^ (1 / 10 : ℝ)
  have h3le : (3 : ℝ) ≤ x := by
    dsimp [x]
    -- 3 = (3^10)^(1/10) ≤ N^(1/10)
    have h310 : (3 : ℝ) ^ (10 : ℝ) ≤ (N : ℝ) := by
      have hnat : (3 : ℝ) ^ 10 ≤ (N : ℝ) := by
        norm_num at hN ⊢
        exact_mod_cast hN
      simpa [Real.rpow_natCast] using hnat
    have hstep := Real.rpow_le_rpow (by positivity : 0 ≤ (3 : ℝ) ^ (10 : ℝ)) h310
      (by norm_num : 0 ≤ (1 / 10 : ℝ))
    -- hstep : ((3:ℝ)^(10:ℝ))^(1/10:ℝ) ≤ x; the left-hand side simplifies to 3.
    have hrew : ((3 : ℝ) ^ (10 : ℝ)) ^ (1 / 10 : ℝ) = (3 : ℝ) := by
      rw [← Real.rpow_mul (by norm_num : 0 ≤ (3 : ℝ))]
      norm_num
    rwa [hrew] at hstep
  have hfloor : 3 ≤ Nat.floor x := Nat.le_floor h3le
  have hz : correctedChenZ N = Nat.floor x := by
    unfold correctedChenZ
    change max 2 (Nat.floor x) = Nat.floor x
    exact max_eq_right (le_trans (by norm_num : (2 : ℕ) ≤ 3) hfloor)
  rw [hz]
  omega

/-- Parameter estimate 3: `log(z - 1) ≤ log N`, the estimate with `Clog = 1`. -/
theorem correctedChenZ_log_le_logN {N : ℕ} (hN : 2 ≤ N) :
    log ((correctedChenZ N - 1 : ℕ) : ℝ) ≤ log (N : ℝ) := by
  have hle := correctedChenZ_sub_one_le_N (by omega : 1 ≤ N)
  have hpos : 0 < (correctedChenZ N - 1 : ℕ) := by
    have hz2 : 2 ≤ correctedChenZ N := by
      unfold correctedChenZ
      exact le_max_left _ _
    omega
  exact Real.log_le_log (by exact_mod_cast hpos) hle

/-- The uniform main-term lower bound follows from (1) the uniform singular-series lower bound `h𝔖`
(at the scale of C₂) and (2) the proved Mertens product estimate `primeProduct_asymptotic_order`,
together with the proved parameter estimates. The only analytic input to this implication is `h𝔖`. -/
theorem CorrectedChenMainTermLower_of_singularSeries_bound
    {c𝔖 : ℝ} (hc𝔖 : 0 < c𝔖)
    (h𝔖 : ∀ N : ℕ, ∀ z : ℕ, 2 ≤ z →
      c𝔖 ≤ AnalyticNumberTheory.Sieve.singularSeriesTruncated N z) :
    CorrectedChenMainTermLower := by
  obtain ⟨c₁₀, c₂₀, hc₁₀, hPP⟩ := MertensTheorem.primeProduct_asymptotic_order
  exact CorrectedChenMainTermLower_of_uniform_estimates
    (c𝔖 := c𝔖) (cpp := c₁₀) (Clog := 1) (M₀ := 2) (N₀'' := 59049)
    hc𝔖 hc₁₀ (by norm_num)
    h𝔖
    (fun m _hm h2 => (hPP m h2).1)
    (fun N hN => by
      have hlog := correctedChenZ_log_le_logN hN
      simpa using hlog)
    (fun N hN => by
      refine ⟨by omega, ?_, ?_⟩
      · exact correctedChenZ_sub_one_ge_two_of_large hN
      · exact correctedChenZ_sub_one_ge_two_of_large hN)

/-- **Uniform lower bound for the truncated singular series**.

For any `N` and `z ≥ 2`, `1/2 ≤ 𝔖_trunc(N, z)`. The classical proof, at the scale
of the twin-prime constant `C₂ ≈ 0.66`, is:

  𝔖_trunc(N,z) ≥ ∏_{2<p≤z}(1 − 1/(p−1)²) ≥ 1 − Σ_{p>2} 1/(p−1)²
                  ≥ 1 − (1/4)·Σ_{k≥1} 1/k² ≥ 1/2,

The second line uses `∏(1-x_i) ≥ 1-Σx_i`; the third uses that `p-1` lies in the even numbers
for primes p > 2; the last uses the telescoping bound `Σ_{k≥1}1/k² ≤ 2`. The proof is purely
finite combinatorics and real arithmetic. This precisely stated proposition, through
`CorrectedChenMainTermLower_of_singularSeries_lower`, directly yields the main-term lower bound. -/
def SingularSeriesTruncatedLowerBound : Prop :=
  ∀ N z : ℕ, 2 ≤ z → (1 / 2 : ℝ) ≤
    AnalyticNumberTheory.Sieve.singularSeriesTruncated N z

/-- The uniform truncated singular-series lower bound with `c𝔖 = 1/2` implies `CorrectedChenMainTermLower`. -/
theorem CorrectedChenMainTermLower_of_singularSeries_lower
    (h𝔖 : SingularSeriesTruncatedLowerBound) :
    CorrectedChenMainTermLower := by
  exact CorrectedChenMainTermLower_of_singularSeries_bound (c𝔖 := 1 / 2) (by norm_num)
    (fun N z hz => h𝔖 N z hz)

/-! ## Uniform lower bound for the truncated singular series

The following are general analytic facts, independent of the particular sieve problem.
They concern the finite singular-series products used in
`AnalyticNumberTheory/Sieve/SingularSeries.lean`. -/

/-- For a finite set, `∏(1 - x_i) ≥ 1 - Σ x_i` when `0 ≤ x_i ≤ 1`. -/
theorem prod_one_sub_ge_one_sub_sum {s : Finset ℕ} {x : ℕ → ℝ}
    (hx0 : ∀ i ∈ s, 0 ≤ x i) (hx1 : ∀ i ∈ s, x i ≤ 1) :
    1 - ∑ i ∈ s, x i ≤ ∏ i ∈ s, (1 - x i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      have hx0s : ∀ i ∈ s, 0 ≤ x i := fun i hi => hx0 i (Finset.mem_insert_of_mem hi)
      have hx1s : ∀ i ∈ s, x i ≤ 1 := fun i hi => hx1 i (Finset.mem_insert_of_mem hi)
      have hx0a : 0 ≤ x a := hx0 a (by simp)
      have hx1a : x a ≤ 1 := hx1 a (by simp)
      have hS : 0 ≤ ∑ i ∈ s, x i := Finset.sum_nonneg hx0s
      rw [Finset.sum_insert ha]
      calc
        1 - (x a + ∑ i ∈ s, x i) ≤ (1 - x a) * (1 - ∑ i ∈ s, x i) := by
          nlinarith [mul_nonneg hx0a hS]
        _ ≤ (1 - x a) * ∏ i ∈ s, (1 - x i) := by
          exact mul_le_mul_of_nonneg_left (ih hx0s hx1s) (sub_nonneg.mpr hx1a)
        _ = ∏ i ∈ insert a s, (1 - x i) := by
          rw [Finset.prod_insert ha]

/-- `Σ_{p prime, 2 < p ≤ z} 1/(p-1)² ≤ 1/2`.

Primes > 2 are odd, so `p-1 = 2k` is even. The injection `p ↦ (p-1)/2` reduces the sum to
`Σ_k 1/(2k)² = (1/4)Σ_k 1/k²`; then use the telescoping estimate
`Σ_{k≥1} 1/k² ≤ 1 + Σ_{k≥2} 1/((k−1)k) ≤ 2`. -/
theorem sum_sq_recip_primes_ge_three_le_half (z : ℕ) :
    (∑ p ∈ (Finset.range (z + 1)).filter (fun p => p.Prime ∧ 2 < p),
      1 / ((p - 1 : ℕ) : ℝ) ^ 2) ≤ (1 / 2 : ℝ) := by
  let S : Finset ℕ := (Finset.range (z + 1)).filter (fun p => p.Prime ∧ 2 < p)
  have hinj : Set.InjOn (fun p : ℕ => (p - 1) / 2) ↑S := by
    intro a ha b hb hab
    rcases Finset.mem_filter.mp ha with ⟨ha1, ha2⟩
    rcases Finset.mem_filter.mp hb with ⟨hb1, hb2⟩
    have hodd_a : Odd a := ha2.1.odd_of_ne_two (by omega : a ≠ 2)
    have hodd_b : Odd b := hb2.1.odd_of_ne_two (by omega : b ≠ 2)
    rcases hodd_a with ⟨ka, hka⟩
    rcases hodd_b with ⟨kb, hkb⟩
    have ha' : a - 1 = 2 * ka := by omega
    have hb' : b - 1 = 2 * kb := by omega
    have hka' : (a - 1) / 2 = ka := by
      rw [ha']
      exact Nat.mul_div_right ka (by norm_num : 0 < 2)
    have hkb' : (b - 1) / 2 = kb := by
      rw [hb']
      exact Nat.mul_div_right kb (by norm_num : 0 < 2)
    change (a - 1) / 2 = (b - 1) / 2 at hab
    have hk : ka = kb := by rwa [hka', hkb'] at hab
    omega
  have himg := Finset.sum_image (f := fun k : ℕ => 1 / ((2 * k : ℕ) : ℝ) ^ 2)
    (g := fun p : ℕ => (p - 1) / 2) (s := S) hinj
  have hcong : (∑ p ∈ S, 1 / ((2 * ((p - 1) / 2) : ℕ) : ℝ) ^ 2) =
      ∑ p ∈ S, 1 / ((p - 1 : ℕ) : ℝ) ^ 2 := by
    apply Finset.sum_congr rfl
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hp1, hp2⟩
    have hodd : Odd p := hp2.1.odd_of_ne_two (by omega : p ≠ 2)
    rcases hodd with ⟨k, hk⟩
    have hsub : p - 1 = 2 * k := by omega
    have hdiv : 2 ∣ p - 1 := ⟨k, by rw [hsub]⟩
    have hmul : (p - 1) / 2 * 2 = p - 1 := Nat.div_mul_cancel hdiv
    rw [show (2 * ((p - 1) / 2) : ℕ) = p - 1 by rw [mul_comm, hmul]]
  have hsubset : S.image (fun p : ℕ => (p - 1) / 2) ⊆ Finset.range (z + 1) := by
    intro k hk
    rcases Finset.mem_image.mp hk with ⟨p, hp, rfl⟩
    rcases Finset.mem_filter.mp hp with ⟨hp1, hp2⟩
    rw [Finset.mem_range]
    have hple : p ≤ z := by
      rcases Finset.mem_range.mp hp1 with h
      omega
    omega
  have hle1 : (∑ p ∈ S, 1 / ((p - 1 : ℕ) : ℝ) ^ 2) ≤
      ∑ k ∈ Finset.range (z + 1), 1 / ((2 * k : ℕ) : ℝ) ^ 2 := by
    calc
      (∑ p ∈ S, 1 / ((p - 1 : ℕ) : ℝ) ^ 2)
          = ∑ k ∈ S.image (fun p : ℕ => (p - 1) / 2), 1 / ((2 * k : ℕ) : ℝ) ^ 2 := by
            rw [← hcong]
            exact himg.symm
      _ ≤ ∑ k ∈ Finset.range (z + 1), 1 / ((2 * k : ℕ) : ℝ) ^ 2 := by
            exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
              (fun k hk hknot => by positivity)
  have hfour : (∑ k ∈ Finset.range (z + 1), 1 / ((2 * k : ℕ) : ℝ) ^ 2) =
      (1 / 4 : ℝ) * ∑ k ∈ Finset.range (z + 1), 1 / (k : ℝ) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have h2k : ((2 * k : ℕ) : ℝ) = 2 * (k : ℝ) := by norm_num
    rw [h2k]
    field_simp
    ring
  have htel : (∑ i ∈ Finset.range z, 1 / (((i + 1 : ℕ) : ℝ) * ((i + 2 : ℕ) : ℝ))) ≤ 1 := by
    have h := Finset.sum_range_sub' (f := fun i : ℕ => 1 / ((i : ℝ) + 1)) (n := z)
    -- h : Σ_{i ∈ range z} (1/((i:ℝ)+1) − 1/((i:ℝ)+2)) = 1 − 1/((z:ℝ)+1)
    have hrew : (∑ i ∈ Finset.range z,
        1 / (((i + 1 : ℕ) : ℝ) * ((i + 2 : ℕ) : ℝ))) =
        ∑ i ∈ Finset.range z, (1 / ((i : ℝ) + 1) - 1 / ((i : ℝ) + 2)) := by
      apply Finset.sum_congr rfl
      intro i hi
      have h1 : ((i + 1 : ℕ) : ℝ) = (i : ℝ) + 1 := by norm_num
      have h2 : ((i + 2 : ℕ) : ℝ) = (i : ℝ) + 2 := by norm_num
      rw [h1, h2]
      field_simp
      ring
    rw [hrew]
    have hval : (∑ i ∈ Finset.range z, (1 / ((i : ℝ) + 1) - 1 / ((i : ℝ) + 2))) =
        ∑ i ∈ Finset.range z, (1 / ((i : ℝ) + 1) - 1 / (((i + 1 : ℕ) : ℝ) + 1)) := by
      apply Finset.sum_congr rfl
      intro i hi
      norm_num [Nat.cast_add, Nat.cast_one]
      ring
    rw [hval, h]
    have hc : 1 / ((0 : ℝ) + 1) = 1 := by norm_num
    have hpos : 0 ≤ 1 / ((z : ℝ) + 1) := by positivity
    linarith
  -- Reciprocal-square upper bound: Σ_{k=0}^{z} 1/k² ≤ 2.
  have hsq : (∑ k ∈ Finset.range (z + 1), 1 / (k : ℝ) ^ 2) ≤ 2 := by
    let A : Finset ℕ := (Finset.range (z + 1)).filter (fun k => k ≤ 1)
    let B : Finset ℕ := (Finset.range (z + 1)).filter (fun k => 2 ≤ k)
    have hpart : A ∪ B = Finset.range (z + 1) := by
      ext k
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_range, A, B]
      omega
    have hdisj : Disjoint A B := by
      rw [Finset.disjoint_filter]
      intro k hk1 hk2
      omega
    have hA : (∑ k ∈ A, 1 / (k : ℝ) ^ 2) ≤ 1 := by
      have hsub : A ⊆ ({0, 1} : Finset ℕ) := by
        intro k hk
        rcases Finset.mem_filter.mp hk with ⟨hk1, hk2⟩
        simp only [Finset.mem_insert, Finset.mem_singleton]
        omega
      calc
        (∑ k ∈ A, 1 / (k : ℝ) ^ 2) ≤ ∑ k ∈ ({0, 1} : Finset ℕ), 1 / (k : ℝ) ^ 2 := by
          exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k hk hknot => by positivity)
        _ = 1 := by norm_num
    have hB : (∑ k ∈ B, 1 / (k : ℝ) ^ 2) ≤
        ∑ i ∈ Finset.range z, 1 / (((i + 1 : ℕ) : ℝ) * ((i + 2 : ℕ) : ℝ)) := by
      have hle : (∑ k ∈ B, 1 / (k : ℝ) ^ 2) ≤
          ∑ k ∈ B, 1 / (((k - 1 : ℕ) : ℝ) * (k : ℝ)) := by
        apply Finset.sum_le_sum
        intro k hk
        rcases Finset.mem_filter.mp hk with ⟨hk1, hk2⟩
        have hpos1 : 0 < ((k - 1 : ℕ) : ℝ) := by
          have hkm1 : (1 : ℕ) ≤ k - 1 := by omega
          exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 1) hkm1)
        have hpos2 : 0 < (k : ℝ) := by
          have : (1 : ℝ) < k := by exact_mod_cast (by omega : 1 < k)
          linarith
        have hleprod : ((k - 1 : ℕ) : ℝ) * (k : ℝ) ≤ (k : ℝ) ^ 2 := by
          have hsub : (k - 1 : ℕ) ≤ k := Nat.sub_le _ _
          nlinarith [show ((k - 1 : ℕ) : ℝ) ≤ k by exact_mod_cast hsub]
        exact one_div_le_one_div_of_le (mul_pos hpos1 hpos2) hleprod
      have hinj2 : Set.InjOn (fun k : ℕ => k - 2) ↑B := by
        intro a ha b hb hab
        change a ∈ B at ha
        rcases Finset.mem_filter.mp ha with ⟨_, ha2⟩
        change b ∈ B at hb
        rcases Finset.mem_filter.mp hb with ⟨_, hb2⟩
        have ha' : a = (a - 2) + 2 := by omega
        have hb' : b = (b - 2) + 2 := by omega
        change a - 2 = b - 2 at hab
        rw [ha', hb', hab]
      have himg2 := Finset.sum_image
        (f := fun i : ℕ => 1 / (((i + 1 : ℕ) : ℝ) * ((i + 2 : ℕ) : ℝ)))
        (g := fun k : ℕ => k - 2) (s := B) hinj2
      have hcong2 : (∑ k ∈ B, 1 / (((k - 1 : ℕ) : ℝ) * (k : ℝ))) =
          ∑ i ∈ B.image (fun k : ℕ => k - 2),
            1 / (((i + 1 : ℕ) : ℝ) * ((i + 2 : ℕ) : ℝ)) := by
        rw [himg2]
        apply Finset.sum_congr rfl
        intro k hk
        have hk2 : 2 ≤ k := (Finset.mem_filter.mp hk).2
        have hshift : (k - 2 : ℕ) + 1 = k - 1 := by omega
        have hshift2 : (k - 2 : ℕ) + 2 = k := by omega
        rw [hshift, hshift2]
      have hsub2 : B.image (fun k : ℕ => k - 2) ⊆ Finset.range z := by
        intro i hi
        rcases Finset.mem_image.mp hi with ⟨k, hk, rfl⟩
        rw [Finset.mem_range]
        rcases Finset.mem_filter.mp hk with ⟨hk1, hk2⟩
        rcases Finset.mem_range.mp hk1 with h
        omega
      calc
        (∑ k ∈ B, 1 / (k : ℝ) ^ 2) ≤ ∑ k ∈ B, 1 / (((k - 1 : ℕ) : ℝ) * (k : ℝ)) := hle
        _ = ∑ i ∈ B.image (fun k : ℕ => k - 2),
            1 / (((i + 1 : ℕ) : ℝ) * ((i + 2 : ℕ) : ℝ)) := hcong2
        _ ≤ ∑ i ∈ Finset.range z, 1 / (((i + 1 : ℕ) : ℝ) * ((i + 2 : ℕ) : ℝ)) := by
              exact Finset.sum_le_sum_of_subset_of_nonneg hsub2
                (fun i hi hnot => by positivity)
    calc
      (∑ k ∈ Finset.range (z + 1), 1 / (k : ℝ) ^ 2)
          = (∑ k ∈ A, 1 / (k : ℝ) ^ 2) + (∑ k ∈ B, 1 / (k : ℝ) ^ 2) := by
            rw [← hpart, Finset.sum_union hdisj]
      _ ≤ 1 + (∑ i ∈ Finset.range z, 1 / (((i + 1 : ℕ) : ℝ) * ((i + 2 : ℕ) : ℝ))) := by
            exact add_le_add hA hB
      _ ≤ 1 + 1 := by
            exact add_le_add (le_refl (1 : ℝ)) htel
      _ = 2 := by norm_num
  calc
    (∑ p ∈ S, 1 / ((p - 1 : ℕ) : ℝ) ^ 2)
        ≤ (1 / 4 : ℝ) * ∑ k ∈ Finset.range (z + 1), 1 / (k : ℝ) ^ 2 := by
          calc
            (∑ p ∈ S, 1 / ((p - 1 : ℕ) : ℝ) ^ 2)
                ≤ ∑ k ∈ Finset.range (z + 1), 1 / ((2 * k : ℕ) : ℝ) ^ 2 := hle1
            _ = (1 / 4 : ℝ) * ∑ k ∈ Finset.range (z + 1), 1 / (k : ℝ) ^ 2 := hfour
    _ ≤ (1 / 4 : ℝ) * 2 := by
          exact mul_le_mul_of_nonneg_left hsq (by norm_num)
    _ = 1 / 2 := by norm_num

/-- **Uniform truncated singular-series lower bound**: for all `N` and `z ≥ 2`, `1/2 ≤ 𝔖_trunc(N, z)`.

Classical argument at the scale of the twin-prime constant C₂: separate the local factors into `p=2`, `p|N`, and `p∤N`.
Then `𝔖_trunc ≥ ∏_{2<p≤z}(1 - 1/(p-1)²)`, and combine
`∏(1-x_i) ≥ 1-Σx_i` with `Σ_{p>2}1/(p-1)² ≤ 1/2`. -/
theorem singularSeriesTruncated_ge_half {N z : ℕ} (hz : 2 ≤ z) :
    (1 / 2 : ℝ) ≤ AnalyticNumberTheory.Sieve.singularSeriesTruncated N z := by
  let S : Finset ℕ := (Finset.range (z + 1)).filter (fun p => p.Prime ∧ 2 < p)
  have hsplit : (Finset.range (z + 1)).filter Nat.Prime = insert 2 S := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert, S]
    constructor
    · intro hp
      rcases hp with ⟨hpz, hpp⟩
      by_cases hp2 : p = 2
      · exact Or.inl hp2
      · exact Or.inr ⟨hpz, hpp, lt_of_le_of_ne hpp.two_le (Ne.symm hp2)⟩
    · intro hp
      rcases hp with hpeq | hpS
      · subst p
        exact ⟨by omega, Nat.prime_two⟩
      · rcases hpS with ⟨hpz, hpp, hp2⟩
        exact ⟨hpz, hpp⟩
  have hlf2 : (1 : ℝ) ≤ AnalyticNumberTheory.Sieve.localFactor 2 N := by
    unfold AnalyticNumberTheory.Sieve.localFactor
    by_cases h2dvd : 2 ∣ N
    · simp [h2dvd]
    · simp [h2dvd]
  have hprod_le : (∏ p ∈ S, (1 - 1 / ((p - 1 : ℕ) : ℝ) ^ 2)) ≤
      ∏ p ∈ S, AnalyticNumberTheory.Sieve.localFactor p N := by
    apply Finset.prod_le_prod
    · intro p hp
      rcases Finset.mem_filter.mp hp with ⟨hp1, hp2⟩
      have hpm1 : (2 : ℝ) ≤ ((p - 1 : ℕ) : ℝ) := by
        have hp3n : (2 : ℕ) ≤ p - 1 := by omega
        exact_mod_cast hp3n
      have hx2 : (4 : ℝ) ≤ ((p - 1 : ℕ) : ℝ) ^ 2 := by
        nlinarith [sq_nonneg (((p - 1 : ℕ) : ℝ) - 2)]
      have h14 : 1 / ((p - 1 : ℕ) : ℝ) ^ 2 ≤ 1 / 4 := by
        exact one_div_le_one_div_of_le (by norm_num : 0 < (4 : ℝ)) hx2
      -- 0 ≤ 1 − 1/(p−1)²
      have hpos : 0 ≤ 1 / ((p - 1 : ℕ) : ℝ) ^ 2 := by positivity
      linarith
    · intro p hp
      rcases Finset.mem_filter.mp hp with ⟨hp1, hp2⟩
      have hpp : p.Prime := hp2.1
      have hp2p : 2 < p := hp2.2
      by_cases hpdvd : p ∣ N
      · rw [AnalyticNumberTheory.Sieve.localFactor_of_dvd hpp hp2p hpdvd]
        have hle1 : 1 - 1 / ((p - 1 : ℕ) : ℝ) ^ 2 ≤ 1 := by
          have hpos : 0 ≤ 1 / ((p - 1 : ℕ) : ℝ) ^ 2 := by positivity
          linarith
        have hle2 : (1 : ℝ) ≤ (p : ℝ) / (p - 1) := by
          have hp1 : 0 < (p : ℝ) - 1 := by
            have : (2 : ℝ) < p := by exact_mod_cast hp2p
            linarith
          rw [le_div_iff₀ hp1]
          linarith
        linarith
      · rw [AnalyticNumberTheory.Sieve.localFactor_of_not_dvd hpp hp2p hpdvd]
        have hcast : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
          simpa using (Nat.cast_sub (R := ℝ) (by omega : 1 ≤ p))
        have hp1 : (p : ℝ) - 1 ≠ 0 := by
          have : (2 : ℝ) < p := by exact_mod_cast hp2p
          linarith
        have heq : 1 - 1 / ((p - 1 : ℕ) : ℝ) ^ 2 =
            (p : ℝ) * (p - 2) / ((p - 1 : ℕ) : ℝ) ^ 2 := by
          rw [hcast]
          field_simp [hp1]
          ring
        rw [heq, hcast]
  have h𝔖 : AnalyticNumberTheory.Sieve.singularSeriesTruncated N z =
      AnalyticNumberTheory.Sieve.localFactor 2 N *
        ∏ p ∈ S, AnalyticNumberTheory.Sieve.localFactor p N := by
    unfold AnalyticNumberTheory.Sieve.singularSeriesTruncated
    rw [hsplit]
    rw [Finset.prod_insert]
    · intro h2S
      rcases Finset.mem_filter.mp h2S with ⟨h1, h2⟩
      omega
  have hprod_ge : (1 / 2 : ℝ) ≤ ∏ p ∈ S, (1 - 1 / ((p - 1 : ℕ) : ℝ) ^ 2) := by
    have hx0 : ∀ p ∈ S, 0 ≤ 1 / ((p - 1 : ℕ) : ℝ) ^ 2 := by
      intro p hp
      positivity
    have hx1 : ∀ p ∈ S, 1 / ((p - 1 : ℕ) : ℝ) ^ 2 ≤ 1 := by
      intro p hp
      rcases Finset.mem_filter.mp hp with ⟨hp1, hp2⟩
      have hpm1 : (2 : ℝ) ≤ ((p - 1 : ℕ) : ℝ) := by
        have hp3n : (2 : ℕ) ≤ p - 1 := by omega
        exact_mod_cast hp3n
      have hx2 : (4 : ℝ) ≤ ((p - 1 : ℕ) : ℝ) ^ 2 := by
        nlinarith [sq_nonneg (((p - 1 : ℕ) : ℝ) - 2)]
      have h14 : 1 / ((p - 1 : ℕ) : ℝ) ^ 2 ≤ 1 / 4 := by
        exact one_div_le_one_div_of_le (by norm_num : 0 < (4 : ℝ)) hx2
      calc
        1 / ((p - 1 : ℕ) : ℝ) ^ 2 ≤ 1 / 4 := h14
        _ ≤ 1 := by norm_num
    calc
      (1 / 2 : ℝ) ≤ 1 - ∑ p ∈ S, 1 / ((p - 1 : ℕ) : ℝ) ^ 2 := by
        have hle := sum_sq_recip_primes_ge_three_le_half z
        have hleS : (∑ p ∈ S, 1 / ((p - 1 : ℕ) : ℝ) ^ 2) ≤ 1 / 2 := by
          simpa [S] using hle
        linarith
      _ ≤ ∏ p ∈ S, (1 - 1 / ((p - 1 : ℕ) : ℝ) ^ 2) := by
            exact prod_one_sub_ge_one_sub_sum hx0 hx1
  calc
    (1 / 2 : ℝ) ≤ ∏ p ∈ S, (1 - 1 / ((p - 1 : ℕ) : ℝ) ^ 2) := hprod_ge
    _ ≤ ∏ p ∈ S, AnalyticNumberTheory.Sieve.localFactor p N := hprod_le
    _ ≤ AnalyticNumberTheory.Sieve.localFactor 2 N *
        ∏ p ∈ S, AnalyticNumberTheory.Sieve.localFactor p N := by
          have hnonneg : 0 ≤ ∏ p ∈ S, AnalyticNumberTheory.Sieve.localFactor p N := by
            apply Finset.prod_nonneg
            intro p hp
            rcases Finset.mem_filter.mp hp with ⟨hp1, hp2⟩
            exact le_of_lt (AnalyticNumberTheory.Sieve.localFactor_pos hp2.1)
          exact le_mul_of_one_le_left hnonneg hlf2
    _ = AnalyticNumberTheory.Sieve.singularSeriesTruncated N z := h𝔖.symm

/-- Instance of `SingularSeriesTruncatedLowerBound`. -/
theorem singularSeriesTruncatedLowerBound_ge_half : SingularSeriesTruncatedLowerBound := by
  intro N z hz
  exact singularSeriesTruncated_ge_half hz

/-- The uniform singular-series lower bound gives the uniform main-term lower bound without further analytic inputs. -/
theorem CorrectedChenMainTermLower_of_singularSeries_lower_bound :
    CorrectedChenMainTermLower := by
  exact CorrectedChenMainTermLower_of_singularSeries_lower singularSeriesTruncatedLowerBound_ge_half

/-- **Asymptotic order of the main term**: the corrected Selberg divisor sum for the corrected sieve
is `Θ(log (z-1) / 𝔖(N, z-1))`.

This applies the exact Mertens product formula
(`primeProduct_asymptotic_order`) to the seam
`SelbergSum · 𝔖 = 1 / primeProduct (z-1)`. -/
theorem correctedChenSelbergSum_asymptotic_order :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ ∀ N : ℕ, Even N → 4 ≤ N → 3 ≤ correctedChenZ N →
      c₁ * log ((correctedChenZ N - 1 : ℕ) : ℝ) /
        AnalyticNumberTheory.Sieve.singularSeriesTruncated N (correctedChenZ N - 1) ≤
        (∑ d ∈ (correctedChenBoundingSieve N).prodPrimes.divisors,
          (correctedChenBoundingSieve N).selbergTerms d) ∧
      (∑ d ∈ (correctedChenBoundingSieve N).prodPrimes.divisors,
          (correctedChenBoundingSieve N).selbergTerms d) ≤
        c₂ * log ((correctedChenZ N - 1 : ℕ) : ℝ) /
        AnalyticNumberTheory.Sieve.singularSeriesTruncated N (correctedChenZ N - 1) := by
  obtain ⟨c₁₀, c₂₀, hc₁₀, hPP⟩ := MertensTheorem.primeProduct_asymptotic_order
  have hP2 : MertensTheorem.primeProduct 2 = (1 / 2 : ℝ) := by
    unfold MertensTheorem.primeProduct
    have hf : (Finset.range 3).filter Nat.Prime = {2} := by
      ext p
      simp only [mem_filter, mem_range, mem_singleton]
      constructor
      · intro hp
        rcases hp with ⟨hp3, hpp⟩
        interval_cases p
        · exact absurd hpp Nat.not_prime_zero
        · exact absurd hpp Nat.not_prime_one
        · rfl
      · intro hp
        subst p
        simp [Nat.prime_two]
    rw [hf]
    norm_num
  have hc₂₀ : 0 < c₂₀ := by
    have hb := hPP 2 (by norm_num)
    have hP2pos : 0 < MertensTheorem.primeProduct 2 := by
      rw [hP2]
      norm_num
    have hlog2 : 0 < log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    have hpos : 0 < c₂₀ / log 2 := lt_of_lt_of_le hP2pos hb.2
    have hmul : 0 < (c₂₀ / log 2) * log 2 := mul_pos hpos hlog2
    have hcancel : (c₂₀ / log 2) * log 2 = c₂₀ := by field_simp [hlog2.ne']
    rwa [hcancel] at hmul
  refine ⟨1 / c₂₀, 1 / c₁₀, one_div_pos.mpr hc₂₀, ?_⟩
  intro N hN _hN4 hz3
  let z := correctedChenZ N
  let x := z - 1
  have hz1 : 1 ≤ z := by omega
  have hx1 : 1 ≤ x := by omega
  have hx2 : 2 ≤ x := by omega
  have hlog : 0 < log (x : ℝ) := by
    have : (1 : ℝ) < x := by exact_mod_cast (show 1 < x by omega)
    exact Real.log_pos this
  have hSpos : 0 < AnalyticNumberTheory.Sieve.singularSeriesTruncated N x :=
    AnalyticNumberTheory.Sieve.singularSeriesTruncated_pos N x hx1
  have hSne : AnalyticNumberTheory.Sieve.singularSeriesTruncated N x ≠ 0 := ne_of_gt hSpos
  have hP := hPP x hx2
  have hPpos : 0 < MertensTheorem.primeProduct x := by
    unfold MertensTheorem.primeProduct
    exact Finset.prod_pos (fun p hp => by
      have hpP : p.Prime := (Finset.mem_filter.mp hp).2
      have hp0 : (0 : ℝ) < p := by exact_mod_cast hpP.pos
      have hle : (1 : ℝ) < p := by exact_mod_cast hpP.one_lt
      have hlt1 : 1 / (p : ℝ) < 1 := (div_lt_iff₀ hp0).mpr (by simpa using hle)
      linarith)
  have hid := correctedChenSelbergSum_mul_singularSeriesTruncated N hN
  have hSel : (∑ d ∈ (correctedChenBoundingSieve N).prodPrimes.divisors,
        (correctedChenBoundingSieve N).selbergTerms d) =
      (MertensTheorem.primeProduct x)⁻¹ *
        (AnalyticNumberTheory.Sieve.singularSeriesTruncated N x)⁻¹ := by
    have h := congrArg (fun t : ℝ => t * (AnalyticNumberTheory.Sieve.singularSeriesTruncated N x)⁻¹) hid
    rw [mul_assoc, mul_inv_cancel₀ hSne, mul_one] at h
    exact h
  have hrec_lo : log (x : ℝ) / c₂₀ ≤ (MertensTheorem.primeProduct x)⁻¹ := by
    have h1 : (c₂₀ / log (x : ℝ))⁻¹ ≤ (MertensTheorem.primeProduct x)⁻¹ :=
      (inv_le_inv₀ (div_pos hc₂₀ hlog) hPpos).mpr hP.2
    have hrew : (c₂₀ / log (x : ℝ))⁻¹ = log (x : ℝ) / c₂₀ := by
      field_simp [hc₂₀.ne', hlog.ne']
    rwa [hrew] at h1
  have hrec_up : (MertensTheorem.primeProduct x)⁻¹ ≤ log (x : ℝ) / c₁₀ := by
    have h1 : (MertensTheorem.primeProduct x)⁻¹ ≤ (c₁₀ / log (x : ℝ))⁻¹ :=
      (inv_le_inv₀ hPpos (div_pos hc₁₀ hlog)).mpr hP.1
    have hrew : (c₁₀ / log (x : ℝ))⁻¹ = log (x : ℝ) / c₁₀ := by
      field_simp [hc₁₀.ne', hlog.ne']
    rwa [hrew] at h1
  have hA : log (x : ℝ) / c₂₀ * (AnalyticNumberTheory.Sieve.singularSeriesTruncated N x)⁻¹ ≤
      (∑ d ∈ (correctedChenBoundingSieve N).prodPrimes.divisors,
        (correctedChenBoundingSieve N).selbergTerms d) := by
    rw [hSel]
    exact mul_le_mul_of_nonneg_right hrec_lo (inv_nonneg.mpr (le_of_lt hSpos))
  have hB : (∑ d ∈ (correctedChenBoundingSieve N).prodPrimes.divisors,
        (correctedChenBoundingSieve N).selbergTerms d) ≤
      log (x : ℝ) / c₁₀ * (AnalyticNumberTheory.Sieve.singularSeriesTruncated N x)⁻¹ := by
    rw [hSel]
    exact mul_le_mul_of_nonneg_right hrec_up (inv_nonneg.mpr (le_of_lt hSpos))
  have hnormA : log (x : ℝ) / c₂₀ * (AnalyticNumberTheory.Sieve.singularSeriesTruncated N x)⁻¹ =
      (1 / c₂₀) * log (x : ℝ) / AnalyticNumberTheory.Sieve.singularSeriesTruncated N x := by
    field_simp [hSne, hc₂₀.ne']
  have hnormB : log (x : ℝ) / c₁₀ * (AnalyticNumberTheory.Sieve.singularSeriesTruncated N x)⁻¹ =
      (1 / c₁₀) * log (x : ℝ) / AnalyticNumberTheory.Sieve.singularSeriesTruncated N x := by
    field_simp [hSne, hc₁₀.ne']
  constructor
  · rw [← hnormA]
    exact hA
  · rw [← hnormB]
    exact hB

end MathlibNt.SieveTheory.SwitchingPrinciple
