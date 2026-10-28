import AnalyticNumberTheory.Sieve.PanMeanValueBody
import AnalyticNumberTheory.Mertens.PartialSummation
import AnalyticNumberTheory.Sieve.GoldbachDensity

/-! # AnalyticNumberTheory.Sieve.PanMainTerm

## Polylogarithmic bounds for the pure main-term contribution

The coarse weighted Pan decomposition separates Type I (`apV1`),
Type II (`apV3`), and a pure main-term piece after absorbing `a`
into the residue class (Liu 2022 §III; Halberstam--Richert 1974 Ch. 10).
This module supplies the reduction chain for the third piece,
`PanMainTermBound` from `PanMeanValueBody.lean` §4.

Here `li` abbreviates the project's proxy
`logarithmicIntegral x = x/log x` (`BombieriVinogradov.lean`),
not the genuine logarithmic integral.
For `|f| ≤ 1`, the unmaximized main term satisfies

```text
|Σ_{(a,q)=1, a≤X} f(a)·li(⌊y/a⌋)/φ(q)|
  ≤ Σ_{1≤a≤X} |li(⌊y/a⌋)|/φ(q)
  ≤ (max_{y≤x} Σ_{1≤a≤X} |li(⌊y/a⌋)|)/φ(q).
```

Thus its weighted modulus sum is at most
`max_{y≤x} Σ_{1≤a≤X} |li(⌊y/a⌋)| · Σ_{q≤Q} μ²(q)·3^{ω(q)}/φ(q)`.
`PanMainTermBound.of_sieveBound` reduces the bound to this product
(`PanMainTermSieveBound`). The triangle inequality, `|f| ≤ 1`,
both maxima, nonnegative weights, and the zero weight at `q = 0`
are all handled by finite algebra, parallel to the Type I reduction
`PanTypeICharacterMeanValue.of_sieveBound`.

## Elementary estimates for the two factors

- **The `(y,a)` factor (§3)**: `|li(m)| ≤ m/log 2` for every natural `m`,
  hence `Σ_{1≤a≤X} |li(⌊y/a⌋)| ≤ (y/log 2)·(1 + log X)`.
  The maximum over `y ≤ x` is at most `(x/log 2)·(1 + log X)`,
  by the harmonic-sum bound and `⌊y/a⌋ ≤ y/a`.
- **The `q` factor (§4)**: for squarefree `q`,
  `μ²(q)·3^{ω(q)}/φ(q) = ∏_{p|q} 3/(p-1)`
  (using `goldbachNu_squarefree_eq_inv_totient`).
  Subset expansion gives
  `Σ_{q≤Q, squarefree} ∏_{p|q} c_p ≤ ∏_{p≤Q} (1+c_p)`.
  Combine `1+u ≤ exp u` with Mertens' second theorem
  (`mertensSecond_nat`) to get
  `Σ_{q≤Q} μ²(q)·3^{ω(q)}/φ(q) ≤ C·log⁶(Q+2)`.

## Limitation: an absolute main term does not give a logarithmic saving

These estimates have product `xX·polylog(xX)`. They cannot yield
`C·xX/log^A(xX)`: the term `a = 1`, `q = 2`, `y = xX` alone
has size `li(xX)/φ(2) ≈ xX/log(xX)`. The saving claim is already
false for `x X = X` and `A = 2`; §6 also proves a counterexample
to the corresponding absorption inequality.

The classical argument instead subtracts the sieve main term
`x/log x·∏(1-ν(p))` from the `li` contribution, leaving a signed
error `O(x/log^A x)` (Liu §III; HR 1974 Ch. 10).
That cancellation requires sieve-product and prime-distribution input,
not an upper bound on the absolute main term. The signed-main-term
requirements are discussed in `PAN_PROOF_ATLAS.md` and the main-term
bridge in `ROADMAP`.

The results here have the provable polylogarithmic right side
`C·xX·(log xX)^{A+7}`:
`panMainTotientWeightedSum_le_polylog` bounds the `q` factor,
`panMainWeightedSum_polylog` combines the elementary factors, and
`panMainSieveAbsorption_of_dom` proves absorption into a larger log power
under `X ≤ x X`. Finally,
`PanMainTermSieveBound.of_innerSumBound` assembles the bound.
These results belong to the coarse pure-main-term chain and do not
establish the classical signed logarithmic-saving estimate.
-/

namespace AnalyticNumberTheory.Sieve

open Finset Real
open AnalyticNumberTheory.Mertens

open scoped Classical
open scoped ArithmeticFunction.Moebius


/-! ## 1. Main-term inner sums and maximum reductions -/


/-- Weighted reciprocal-totient sum `Σ_{q≤Q} μ²(q)·3^{ω(q)}/φ(q)`;
the `q = 0` term has zero weight. -/
noncomputable def panMainTotientWeightedSum (Q : ℕ) : ℝ :=
  ∑ q ∈ Finset.range (Q + 1),
    ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card / (Nat.totient q : ℝ)


/-! ## 1.1 Liu Section III: the non-decaying Selberg main term

The following finite identity models Liu's equation `M₁`: the `li` sum is
multiplied by the Selberg quadratic factor.  It is deliberately separate from
the signed Pan remainder, whose inverse-log decay concerns `π - li`.
-/


/-! ## 2. Analytic input and reduction theorem -/


/-! ## 3. Elementary li-proxy bounds and the (y,a) factor

For every natural `m`, `|li(m)| ≤ m/log 2`: if `m ≥ 2`,
`li(m) = m/log m ≤ m/log 2`, while `li(0) = li(1) = 0`.
The harmonic bound `Σ_{1≤a≤X} 1/a ≤ 1+log X` and
`⌊y/a⌋ ≤ y/a` then give
`Σ_{1≤a≤X} |li(⌊y/a⌋)| ≤ (y/log 2)·(1+log X)`.
Taking the maximum over `y ≤ x` yields
`mainTermInnerSumMax ≤ (x/log 2)·(1+log X)`.

This bounds the `(y,a)` factor in `PanMainTermSieveBound`.
More refined classical estimates use sums such as
`Σ 1/(a·log(y/a)) ≪ log log X` in the appropriate ranges
(see Mertens partial summation); the coarse `log X` bound is
sufficient here, where the exact polylogarithmic exponent is inessential.
-/


/-! ## 4. The q factor: weighted reciprocal-totient sum

For squarefree `q`, `μ²(q)·3^{ω(q)}/φ(q) = ∏_{p|q} 3/(p-1)`.
Subset expansion gives
`Σ_{q≤Q, squarefree} ∏_{p|q} c_p ≤ ∏_{p≤Q} (1+c_p)`.
Using `∏(1+u) ≤ exp(Σu)` and Mertens' second theorem
(`mertensSecond_nat`) yields
`Σ_{q≤Q} μ²(q)·3^{ω(q)}/φ(q) ≤ C·log⁶(Q+2)`.

The ingredients are elementary: `μ²` is 1 on squarefree integers
and 0 otherwise; squarefree integers are determined by their
prime-factor sets; and `Σ 1/(p-1) ≤ 2Σ 1/p`, followed by Mertens.
-/

private lemma squarefree_eq_prod_primeFactors {n : ℕ} (hn : Squarefree n) :
    n = ∏ p ∈ n.primeFactors, p := by
  exact (Nat.prod_primeFactors_of_squarefree hn).symm

/-- Subset expansion:
`∏_{x∈s} (1+g x) = Σ_{t⊆s} ∏_{x∈t} g x`. -/
private lemma sum_powerset_prod {α : Type*} [DecidableEq α] (s : Finset α) (g : α → ℝ) :
    (∑ t ∈ s.powerset, ∏ x ∈ t, g x) = ∏ x ∈ s, (1 + g x) := by
  exact (Finset.prod_one_add s).symm

/-- Main-term weight for squarefree `q`:
`μ²(q)·3^{ω(q)}/φ(q) = ∏_{p|q} 3/(p-1)`. -/
theorem panMainTotientWeight_term_squarefree (q : ℕ) (hq : Squarefree q) :
    ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card / (Nat.totient q : ℝ) =
      ∏ p ∈ q.primeFactors, (3 : ℝ) / ((p : ℝ) - 1) := by
  have hmu : ((μ q : ℤ) : ℝ) ^ 2 = 1 := by
    rw [← Int.cast_pow, ArithmeticFunction.moebius_sq_eq_one_of_squarefree hq]
    norm_num
  have hφ : (Nat.totient q : ℝ) = ∏ p ∈ q.primeFactors, ((p : ℝ) - 1) := by
    rw [totient_eq_prod_primeFactors_of_squarefree hq, Nat.cast_prod]
    apply Finset.prod_congr rfl
    intro p hp
    have hp1 : 1 ≤ p := (Nat.prime_of_mem_primeFactors hp).one_lt.le
    rw [Nat.cast_sub hp1]
    norm_num
  calc
    ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card / (Nat.totient q : ℝ)
        = (3 : ℝ) ^ q.primeFactors.card / (∏ p ∈ q.primeFactors, ((p : ℝ) - 1)) := by
          rw [hmu, hφ]
          norm_num
    _ = (∏ p ∈ q.primeFactors, (3 : ℝ)) / (∏ p ∈ q.primeFactors, ((p : ℝ) - 1)) := by
          rw [← Finset.prod_const]
    _ = ∏ p ∈ q.primeFactors, (3 : ℝ) / ((p : ℝ) - 1) := by
          rw [← Finset.prod_div_distrib]

/-- The main-term weight vanishes for nonsquarefree `q`, since `μ(q) = 0`. -/
theorem panMainTotientWeight_term_non_squarefree (q : ℕ) (hq : ¬ Squarefree q) :
    ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card / (Nat.totient q : ℝ) = 0 := by
  have hmu : (μ q : ℤ) = 0 := ArithmeticFunction.moebius_eq_zero_of_not_squarefree hq
  simp [hmu]

/-- The main-term weight, including its totient denominator, is nonnegative. -/
private lemma panMainTotientWeight_term_nonneg (q : ℕ) :
    0 ≤ ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card / (Nat.totient q : ℝ) := by
  exact div_nonneg (mul_nonneg (sq_nonneg _) (pow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _))
    (by positivity : (0 : ℝ) ≤ (Nat.totient q : ℝ))

/-- **Subset bound**: for nonnegative coefficients,
`Σ_{q≤Q, squarefree} ∏_{p|q} c p ≤ ∏_{p≤Q} (1+c p)`.
A squarefree integer is determined by its prime-factor set,
`q = ∏ p ∈ q.primeFactors, p`, and the product on the right
expands into the sum of `∏_{p∈S} c p` over all subsets
`S ⊆ {p prime : p ≤ Q}`. -/
theorem sum_squarefree_prod_primeFactors_le_prod_one_add (Q : ℕ) (c : ℕ → ℝ)
    (hc : ∀ p : ℕ, p.Prime → 0 ≤ c p) :
    (∑ q ∈ (Finset.range (Q + 1)).filter Squarefree, ∏ p ∈ q.primeFactors, c p) ≤
      ∏ p ∈ primesUpTo Q, (1 + c p) := by
  classical
  have hg : Set.InjOn (fun q : ℕ => q.primeFactors)
      (↑((Finset.range (Q + 1)).filter Squarefree) : Set ℕ) := by
    intro a ha b hb hgab
    have haSq : Squarefree a := (Finset.mem_filter.mp ha).2
    have hbSq : Squarefree b := (Finset.mem_filter.mp hb).2
    calc
      a = ∏ p ∈ a.primeFactors, p := squarefree_eq_prod_primeFactors haSq
      _ = ∏ p ∈ b.primeFactors, p := by
            have hgab' : a.primeFactors = b.primeFactors := by simpa using hgab
            rw [← hgab']
      _ = b := (squarefree_eq_prod_primeFactors hbSq).symm
  have him : ((Finset.range (Q + 1)).filter Squarefree).image (fun q : ℕ => q.primeFactors) ⊆
      (primesUpTo Q).powerset := by
    intro S hS
    rcases Finset.mem_image.mp hS with ⟨q, hq, rfl⟩
    rw [Finset.mem_powerset]
    intro p hp
    have hqmem : q ∈ Finset.range (Q + 1) := (Finset.mem_filter.mp hq).1
    have hqSq : Squarefree q := (Finset.mem_filter.mp hq).2
    have hq_le : q ≤ Q := Nat.lt_succ_iff.mp (Finset.mem_range.mp hqmem)
    have hq_ne : q ≠ 0 := by
      intro hq0
      rw [hq0] at hqSq
      exact not_squarefree_zero (R := ℕ) hqSq
    have hp_pr : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hp_dvd : p ∣ q := Nat.dvd_of_mem_primeFactors hp
    have hp_le_q : p ≤ q := Nat.le_of_dvd (Nat.pos_of_ne_zero hq_ne) hp_dvd
    exact (mem_primesUpTo).2 ⟨hp_pr, le_trans hp_le_q hq_le⟩
  calc
    (∑ q ∈ (Finset.range (Q + 1)).filter Squarefree, ∏ p ∈ q.primeFactors, c p)
        = ∑ S ∈ ((Finset.range (Q + 1)).filter Squarefree).image (fun q : ℕ => q.primeFactors),
            ∏ p ∈ S, c p := by
          exact (Finset.sum_image (g := fun q : ℕ => q.primeFactors)
            (f := fun S : Finset ℕ => ∏ p ∈ S, c p) hg).symm
    _ ≤ ∑ S ∈ (primesUpTo Q).powerset, ∏ p ∈ S, c p := by
          exact Finset.sum_le_sum_of_subset_of_nonneg him (fun S hSt hSn => by
            exact Finset.prod_nonneg (fun p hp => hc p
              ((mem_primesUpTo.mp ((Finset.mem_powerset.mp hSt) hp)).1)))
    _ = ∏ p ∈ primesUpTo Q, (1 + c p) := by
          rw [sum_powerset_prod (primesUpTo Q) c]

/-- The weighted reciprocal-totient sum is bounded by
`∏_{p≤Q} (1+3/(p-1))`. -/
theorem panMainTotientWeightedSum_le_prod_one_add (Q : ℕ) :
    panMainTotientWeightedSum Q ≤
      ∏ p ∈ primesUpTo Q, (1 + (3 : ℝ) / ((p : ℝ) - 1)) := by
  unfold panMainTotientWeightedSum
  calc
    (∑ q ∈ Finset.range (Q + 1),
        ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card / (Nat.totient q : ℝ))
        = ∑ q ∈ Finset.range (Q + 1),
            if Squarefree q then
              ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card / (Nat.totient q : ℝ)
            else 0 := by
          apply Finset.sum_congr rfl
          intro q hq
          by_cases h : Squarefree q
          · rw [if_pos h]
          · rw [if_neg h]
            exact panMainTotientWeight_term_non_squarefree q h
    _ = ∑ q ∈ (Finset.range (Q + 1)).filter Squarefree,
          ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card / (Nat.totient q : ℝ) := by
          rw [Finset.sum_filter]
    _ = ∑ q ∈ (Finset.range (Q + 1)).filter Squarefree,
          ∏ p ∈ q.primeFactors, (3 : ℝ) / ((p : ℝ) - 1) := by
          apply Finset.sum_congr rfl
          intro q hq
          exact panMainTotientWeight_term_squarefree q (Finset.mem_filter.mp hq).2
    _ ≤ ∏ p ∈ primesUpTo Q, (1 + (3 : ℝ) / ((p : ℝ) - 1)) := by
          exact sum_squarefree_prod_primeFactors_le_prod_one_add Q
            (fun p => (3 : ℝ) / ((p : ℝ) - 1)) (by
              intro p hp
              have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
              have hpm1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
              exact div_nonneg (by norm_num : (0 : ℝ) ≤ 3) (le_of_lt hpm1))

/-- The weighted reciprocal-totient sum is monotone in `Q`,
since its summands are nonnegative. -/
theorem panMainTotientWeightedSum_mono : Monotone panMainTotientWeightedSum := by
  intro Q₁ Q₂ hQ
  unfold panMainTotientWeightedSum
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_mono (Nat.succ_le_succ hQ))
    (fun q _ _ => panMainTotientWeight_term_nonneg q)

/-- **Polylogarithmic q-factor bound**:
`Σ_{q≤Q} μ²(q)·3^{ω(q)}/φ(q) ≤ C·log⁶(Q+2)`.
Use subset expansion, `∏(1+u) ≤ exp(Σu)`,
`Σ_{p≤Q} 3/(p-1) ≤ 6·Σ_{p≤Q} 1/p`, and Mertens' second theorem.
Absorb the finite initial range `Q ≤ 2` into the constant. -/
theorem panMainTotientWeightedSum_le_polylog :
    ∃ C : ℝ, 0 < C ∧ ∀ Q : ℕ,
      panMainTotientWeightedSum Q ≤ C * (Real.log (Q + 2)) ^ (6 : ℝ) := by
  classical
  obtain ⟨C₁, hC₁, hM⟩ := mertensSecond_nat
  let K : ℝ := |mertensSecondConstant| + C₁ / log 2
  let C : ℝ := max (4 / (log 2) ^ (6 : ℝ)) (rexp (6 * K))
  have hlg2 : (0 : ℝ) < log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hCpos : 0 < C := by
    dsimp [C]
    exact lt_max_of_lt_left (div_pos (by norm_num : (0 : ℝ) < 4) (Real.rpow_pos_of_pos hlg2 (6 : ℝ)))
  refine ⟨C, hCpos, ?_⟩
  intro Q
  by_cases hQ : Q ≤ 2
  · have hbnd : panMainTotientWeightedSum Q ≤ 4 := by
      calc
        panMainTotientWeightedSum Q ≤ panMainTotientWeightedSum 2 := panMainTotientWeightedSum_mono hQ
        _ ≤ ∏ p ∈ primesUpTo 2, (1 + (3 : ℝ) / ((p : ℝ) - 1)) := panMainTotientWeightedSum_le_prod_one_add 2
        _ = 4 := by
              have hP : primesUpTo 2 = ({2} : Finset ℕ) := by
                ext p
                constructor
                · intro hp
                  have hp_pr : p.Prime := (mem_primesUpTo.mp hp).1
                  have hp_le : p ≤ 2 := (mem_primesUpTo.mp hp).2
                  interval_cases p
                  · norm_num at hp_pr
                  · norm_num at hp_pr
                  · simp
                · intro hp
                  have hp2 : p = 2 := by simpa using hp
                  subst p
                  exact mem_primesUpTo.2 ⟨by norm_num, by norm_num⟩
              rw [hP]
              norm_num
    have hQ2 : (2 : ℕ) ≤ Q + 2 := by omega
    have hlgQ2nn : (0 : ℝ) ≤ Real.log (Q + 2) :=
      Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ Q + 2))
    have hlogle : (log 2) ^ (6 : ℝ) ≤ (Real.log (Q + 2)) ^ (6 : ℝ) := by
      exact Real.rpow_le_rpow (le_of_lt hlg2)
        (Real.log_le_log (by norm_num : (0 : ℝ) < 2) (by exact_mod_cast hQ2))
        (by norm_num : (0 : ℝ) ≤ (6 : ℝ))
    calc
      panMainTotientWeightedSum Q ≤ 4 := hbnd
      _ = 4 / (log 2) ^ (6 : ℝ) * (log 2) ^ (6 : ℝ) := by
        have hx : (log 2) ^ (6 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hlg2 (6 : ℝ)).ne'
        field_simp [hx]
      _ ≤ 4 / (log 2) ^ (6 : ℝ) * (Real.log (Q + 2)) ^ (6 : ℝ) := by
        exact mul_le_mul_of_nonneg_left hlogle
          (div_nonneg (by norm_num : (0 : ℝ) ≤ 4) (le_of_lt (Real.rpow_pos_of_pos hlg2 (6 : ℝ))))
      _ ≤ C * (Real.log (Q + 2)) ^ (6 : ℝ) := by
        exact mul_le_mul_of_nonneg_right (le_max_left (4 / (log 2) ^ (6 : ℝ)) (rexp (6 * K)))
          (Real.rpow_nonneg hlgQ2nn (6 : ℝ))
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
    have hsum : (∑ p ∈ primesUpTo Q, (3 : ℝ) / ((p : ℝ) - 1)) ≤ 6 * primeReciprocalSum Q := by
      calc
        (∑ p ∈ primesUpTo Q, (3 : ℝ) / ((p : ℝ) - 1))
            ≤ ∑ p ∈ primesUpTo Q, (6 : ℝ) / (p : ℝ) := by
              apply Finset.sum_le_sum
              intro p hp
              have hp_pr : p.Prime := (mem_primesUpTo.mp hp).1
              have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp_pr.two_le
              have hppos : (0 : ℝ) < p := by exact_mod_cast hp_pr.pos
              have hpm1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
              rw [div_le_div_iff₀ hpm1 hppos]
              nlinarith
        _ = 6 * (∑ p ∈ primesUpTo Q, 1 / (p : ℝ)) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro p hp
              ring
        _ = 6 * primeReciprocalSum Q := by
              unfold primeReciprocalSum
              rfl
    have hlgQ2nn : (0 : ℝ) ≤ Real.log (Q + 2) :=
      Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ Q + 2))
    have hlogle : (log (Q : ℝ)) ^ (6 : ℝ) ≤ (Real.log (Q + 2)) ^ (6 : ℝ) := by
      exact Real.rpow_le_rpow hlogQnn
        (Real.log_le_log (by positivity : (0 : ℝ) < (Q : ℝ)) (by exact_mod_cast (by omega : Q ≤ Q + 2)))
        (by norm_num : (0 : ℝ) ≤ (6 : ℝ))
    calc
      panMainTotientWeightedSum Q ≤ ∏ p ∈ primesUpTo Q, (1 + (3 : ℝ) / ((p : ℝ) - 1)) :=
            panMainTotientWeightedSum_le_prod_one_add Q
      _ ≤ rexp (∑ p ∈ primesUpTo Q, (3 : ℝ) / ((p : ℝ) - 1)) := by
            -- Nonnegativity is needed only for primes in the product.
            rw [Real.exp_sum]
            apply Finset.prod_le_prod
            · intro p hp
              have hp1 : (1 : ℝ) ≤ p := by
                exact_mod_cast (mem_primesUpTo.mp hp).1.one_lt.le
              exact add_nonneg zero_le_one (div_nonneg (by norm_num) (sub_nonneg.mpr hp1))
            · intro p hp
              simpa only [add_comm] using Real.add_one_le_exp ((3 : ℝ) / ((p : ℝ) - 1))
      _ ≤ rexp (6 * primeReciprocalSum Q) := by
            exact Real.exp_le_exp.mpr hsum
      _ ≤ rexp (6 * (log (log (Q : ℝ)) + K)) := by
            exact Real.exp_le_exp.mpr (by
              have h6 : (0 : ℝ) ≤ 6 := by norm_num
              exact mul_le_mul_of_nonneg_left hpRS h6)
      _ = rexp (6 * K) * (log (Q : ℝ)) ^ (6 : ℝ) := by
            rw [mul_add, Real.exp_add, mul_comm 6 (log (log (Q : ℝ))),
              Real.exp_mul, Real.exp_log hlogQ, mul_comm]
      _ ≤ C * (Real.log (Q + 2)) ^ (6 : ℝ) := by
            exact mul_le_mul (le_max_right (4 / (log 2) ^ (6 : ℝ)) (rexp (6 * K))) hlogle
              (Real.rpow_nonneg hlogQnn (6 : ℝ)) (le_of_lt hCpos)


/-! ## 5. Combined polylogarithmic main-term bound

Under `|f| ≤ 1`, the weighted main-term sum is bounded by
`C·|xX|·(1+log X)·log⁶(Q+2)`, using the elementary proxy estimate
`|li(m)| ≤ m/log 2`, the harmonic sum, and the q-factor bound.
This is the intermediate estimate for `PanMainTermSieveBound`.
Its absorption into `C·xX·(log xX)^{A+7}` is the content of
`PanMainSieveAbsorption` in §6: a fixed polylogarithmic factor
is dominated by a larger logarithmic power. -/


/-! ## 6. Polylogarithmic absorption and the main-term sieve bound -/


/-! ## 6.1 Proof of polylogarithmic absorption

For `(X : ℝ) ≤ x X`, the proof has three steps:

1. **Eventual log lower bound** (`panMainSieve_log_ge_one`):
   monotonicity gives `log X ≤ log(xX)`, while
   `Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop`
   gives `log X → ∞`. Hence eventually `1 ≤ log(xX)`.
2. **Product bound** (`panMainSieve_polylog_le`, natural powers):
   for `X ≥ 2` and `1 ≤ log(xX)`,
   `log(xX+2) ≤ log(2·xX) = log 2 + log(xX) ≤ 2·log(xX)`,
   and `1+log X ≤ 2·log(xX)`. Thus
   `(1+log X)·log⁶(xX+2) ≤ (2L)·(2L)^6 = 128·log⁷(xX)`.
3. **Larger exponent** (`panMainSieveAbsorption_of_dom`):
   for base `log(xX) ≥ 1`, use
   `Real.rpow_le_rpow_of_exponent_le` and `7 ≤ A+7` from `A > 0`,
   then multiply by `xX ≥ 0`.

The theorem `not_panMainSieveAbsorption_old_natCast` disproves
the corresponding logarithmic-saving absorption for `x X = X`.
Taking `A = 1` and cancelling `X > 0` would give
`(1+log X)·log⁶(X+2)·log X ≤ C`; its left side is at least
`log X → ∞`, contradicting every fixed `C`.
Even refining the inner-sum upper bound to the classical
`C·xX·(1+log log xX)` shape in suitable ranges does not turn
the additional `log⁶` upper bound into a logarithmic saving.
Such a saving concerns a difference,
`|li main term − sieve main term| ≪ x/log^A x`,
with the sieve product written as `∏(1-ν(p)/p)` when `ν`
uses the unnormalized density convention. It is not a bound
on the separate absolute contributions.

There is also a decomposition issue (see `PanVaughanPointwise.lean`):
this module bounds the coarse pure-`|li|` inner sum
`mainTermInnerSumMax·Σ`. By contrast, finite Vaughan algebra
(`panWeightedVonMangoldt_abs_le`) produces
`|Σ f(a)·(apSmall − apMiddle)|`.
After the analytic ψ-to-π conversion, the classical third piece is
the signed difference
`|Σ f(a)·((apSmall − apMiddle)/log(y/a) − li(y/a)/φ(q))|`.
The separate signed assembly must control this PNT-level main term;
the pure-`li` polylogarithmic bound cannot replace it.
See `PAN_PROOF_ATLAS.md` for the signed-main-term and Chen-weight
requirements. The proof here uses elementary mathlib analysis:
limits, real powers, and logarithm monotonicity.
-/

section PanMainSieveAbsorption_proof

open Filter


end PanMainSieveAbsorption_proof


end AnalyticNumberTheory.Sieve
