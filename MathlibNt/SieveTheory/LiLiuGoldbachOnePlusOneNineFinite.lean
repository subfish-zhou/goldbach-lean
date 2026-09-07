import Mathlib

/-!
# Li--Liu's literal `1 + 1.9` count and actual finite Goldbachbasic bridge

This module freezes the objects at labels `p+rq/r<`, `D1a`, and
`Goldbachbasic` of Li--Liu (2026).  The exponent condition for `a = 19/10` is
kept entirely in natural-number arithmetic:

`r ≤ q^(9/10)` is represented by `r^10 ≤ q^9`.

In particular, this is not an encoding by an unrestricted almost-prime
predicate.  The witnesses `r` and `q`, their primality conditions, and the
size relation all remain literal.
-/

open scoped BigOperators

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine

noncomputable local instance (P : Prop) : Decidable P := Classical.propDecidable P

open Finset

/-! ## The literal representation predicate and `D_{1,19/10}(N)` -/

/-- A literal Li--Liu `1 + 1.9` representation of `N`, with `p` retained as
the counted variable.  This is label `p+rq/r<` specialized to `a = 19/10`.
The rational-power inequality is cleared to `r^10 ≤ q^9`. -/
def IsOnePlusOneNineRepresentation (N p : ℕ) : Prop :=
  p.Prime ∧
    ∃ r q : ℕ,
      (r = 1 ∨ r.Prime) ∧ q.Prime ∧ N = p + r * q ∧ r ^ 10 ≤ q ^ 9

/-- The finite set of primes `p` counted by Li--Liu's `D_{1,19/10}(N)`.
The range cutoff is inclusive because `range (N + 1)` represents `p ≤ N`.
-/
noncomputable def onePlusOneNineRepresentedPrimes (N : ℕ) : Finset ℕ :=
  (range (N + 1)).filter (IsOnePlusOneNineRepresentation N)

/-- Literal finite representation count `D_{1,19/10}(N)` from label `D1a`.
It counts admissible values of `p`, exactly as the displayed set in the
source, rather than counting witness triples `(p,r,q)`. -/
noncomputable def D19 (N : ℕ) : ℕ :=
  (onePlusOneNineRepresentedPrimes N).card

theorem mem_onePlusOneNineRepresentedPrimes_iff {N p : ℕ} :
    p ∈ onePlusOneNineRepresentedPrimes N ↔
      p ≤ N ∧ IsOnePlusOneNineRepresentation N p := by
  simp [onePlusOneNineRepresentedPrimes]

/-- Positive literal count is equivalent to existence of a literal
`p + r*q` representation satisfying the cleared `1.9` constraint. -/
theorem D19_pos_iff (N : ℕ) :
    0 < D19 N ↔
      ∃ p r q : ℕ,
        p ≤ N ∧ p.Prime ∧ (r = 1 ∨ r.Prime) ∧ q.Prime ∧
          N = p + r * q ∧ r ^ 10 ≤ q ^ 9 := by
  classical
  constructor
  · intro h
    rw [D19, Finset.card_pos] at h
    obtain ⟨p, hp⟩ := h
    rw [mem_onePlusOneNineRepresentedPrimes_iff] at hp
    obtain ⟨hpN, hpPrime, r, q, hr, hq, hN, hrq⟩ := hp
    exact ⟨p, r, q, hpN, hpPrime, hr, hq, hN, hrq⟩
  · rintro ⟨p, r, q, hpN, hpPrime, hr, hq, hN, hrq⟩
    rw [D19, Finset.card_pos]
    exact ⟨p, mem_onePlusOneNineRepresentedPrimes_iff.mpr
      ⟨hpN, hpPrime, r, q, hr, hq, hN, hrq⟩⟩

theorem D19_ne_zero_iff (N : ℕ) :
    D19 N ≠ 0 ↔
      ∃ p r q : ℕ,
        p ≤ N ∧ p.Prime ∧ (r = 1 ∨ r.Prime) ∧ q.Prime ∧
          N = p + r * q ∧ r ^ 10 ≤ q ^ 9 := by
  rw [← D19_pos_iff]
  omega

/-! ## A literal finite form of the first `Goldbachbasic` weight -/

/-- `P⁻(n) ≥ z`, written without choosing a real-power cutoff: every prime
divisor of `n` is at least the natural cutoff `z`. -/
def LeastPrimeFactorAtLeast (z n : ℕ) : Prop :=
  ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ n → z ≤ ℓ

/-- The source's multiplicity-counting condition `Ω(n) ≥ k`. -/
def OmegaAtLeast (k n : ℕ) : Prop :=
  k ≤ n.primeFactorsList.length

/-- The four-term pointwise weight in `Goldbachbasic`, valued in `ℤ` so that
the displayed subtractions are literal. -/
noncomputable def goldbachBasicWeight (zAlpha zTau n : ℕ) : ℤ :=
  (if LeastPrimeFactorAtLeast zAlpha n then 1 else 0) -
    (if LeastPrimeFactorAtLeast zTau n ∧ OmegaAtLeast 2 n then 1 else 0) +
    (if LeastPrimeFactorAtLeast zTau n ∧ OmegaAtLeast 3 n then 1 else 0) -
    (if LeastPrimeFactorAtLeast zAlpha n ∧ OmegaAtLeast 3 n then 1 else 0)

/-- The four finite cardinalities on the right side of `Goldbachbasic`.
`A` is the finite Goldbach difference carrier; `zAlpha,zTau` are exact
natural cutoffs standing for the source's `N^α,N^τ`. -/
noncomputable def goldbachBasicFiniteRHS
    (A : Finset ℕ) (zAlpha zTau : ℕ) : ℤ :=
  ((A.filter (LeastPrimeFactorAtLeast zAlpha)).card : ℤ) -
    ((A.filter (fun n =>
      LeastPrimeFactorAtLeast zTau n ∧ OmegaAtLeast 2 n)).card : ℤ) +
    ((A.filter (fun n =>
      LeastPrimeFactorAtLeast zTau n ∧ OmegaAtLeast 3 n)).card : ℤ) -
    ((A.filter (fun n =>
      LeastPrimeFactorAtLeast zAlpha n ∧ OmegaAtLeast 3 n)).card : ℤ)

private theorem sum_indicator_eq_card_filter
    (A : Finset ℕ) (P : ℕ → Prop) :
    (∑ n ∈ A, if P n then (1 : ℤ) else 0) = ((A.filter P).card : ℤ) := by
  classical
  exact Finset.sum_boole P A

/-- Complete finite combinatorial identity behind the displayed four sums in
`Goldbachbasic`.  No asymptotic or analytic premise enters this theorem. -/
theorem sum_goldbachBasicWeight_eq_finiteRHS
    (A : Finset ℕ) (zAlpha zTau : ℕ) :
    (∑ n ∈ A, goldbachBasicWeight zAlpha zTau n) =
      goldbachBasicFiniteRHS A zAlpha zTau := by
  classical
  unfold goldbachBasicWeight goldbachBasicFiniteRHS
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.sum_sub_distrib]
  simp only [Finset.sum_boole]

/-! ## Actual pointwise producer

Source: `1+1.9v2.tex`, lines 845--900; PDF pp. 12--13.
The proposition's second indicator is Ω ≥ 2. The proof's opening display
locally prints Ω = 2, contrary to the proposition and its own Case 3.
We retain the proposition's four terms without changing the existing weight.
The final result is an eventual specialization, not the printed effective cutoff.
-/

open Filter

/-- The source's prime carrier uses the linear cutoff `(1-ε)N`. -/
noncomputable def goldbachPrimeCarrier (N : ℕ) (ε : ℝ) : Finset ℕ := by
  classical
  exact (range (N + 1)).filter (fun p => p.Prime ∧ (p : ℝ) < (1 - ε) * N)

/-- Exact natural cutoff, preserving the real weak inequality at integer primes. -/
noncomputable def goldbachPowerCutoff (N : ℕ) (β : ℝ) : ℕ := ⌈(N : ℝ) ^ β⌉₊

theorem leastPrimeFactorAtLeast_powerCutoff_iff (N n : ℕ) (β : ℝ) :
    LeastPrimeFactorAtLeast (goldbachPowerCutoff N β) n ↔
      ∀ r : ℕ, r.Prime → r ∣ n → (N : ℝ) ^ β ≤ r := by
  simp only [LeastPrimeFactorAtLeast, goldbachPowerCutoff, Nat.ceil_le]

/-- For actual differences n ≥ 2, the encoded cutoff is exactly the paper's
real inequality for the least prime factor P⁻(n). -/
theorem leastPrimeFactorAtLeast_powerCutoff_iff_minFac (N n : ℕ) (β : ℝ)
    (hn : 2 ≤ n) :
    LeastPrimeFactorAtLeast (goldbachPowerCutoff N β) n ↔
      (N : ℝ) ^ β ≤ (n.minFac : ℝ) := by
  rw [leastPrimeFactorAtLeast_powerCutoff_iff]
  constructor
  · intro h
    exact h n.minFac (Nat.minFac_prime (by omega)) (Nat.minFac_dvd n)
  · intro h r hr hd
    exact h.trans (by exact_mod_cast Nat.minFac_le_of_dvd hr.two_le hd)

/-- Every positive weight comes from a prime or a two-prime product with a
prime factor strictly below the upper cutoff. Multiplicity is retained. -/
theorem positive_goldbachBasicWeight_structure {zAlpha zTau n : ℕ}
    (hn : 2 ≤ n) (hw : 0 < goldbachBasicWeight zAlpha zTau n) :
    n.Prime ∨ ∃ r q : ℕ, r.Prime ∧ q.Prime ∧ n = r * q ∧ r < zTau := by
  classical
  have h3 : ¬ OmegaAtLeast 3 n := by
    intro h
    have h2 : OmegaAtLeast 2 n := by unfold OmegaAtLeast at *; omega
    simp [goldbachBasicWeight, h, h2] at hw
  have hlen : n.primeFactorsList.length < 3 := by
    simpa [OmegaAtLeast] using h3
  have hprod := Nat.prod_primeFactorsList (by omega : n ≠ 0)
  have hprimes := @Nat.prime_of_mem_primeFactorsList n
  cases heq : n.primeFactorsList with
  | nil => simp [heq] at hprod; omega
  | cons r rs =>
    cases rs with
    | nil =>
      left
      have hr : r.Prime := hprimes (by simp [heq])
      have hn' : r = n := by simpa [heq] using hprod
      exact hn' ▸ hr
    | cons q qs =>
      have hqs : qs = [] := by
        apply List.length_eq_zero_iff.mp
        simp only [heq, List.length_cons] at hlen
        omega
      subst qs
      have hr : r.Prime := hprimes (by simp [heq])
      have hq : q.Prime := hprimes (by simp [heq])
      have hnprod : n = r * q := by simpa [heq] using hprod.symm
      have h2 : OmegaAtLeast 2 n := by simp [OmegaAtLeast, heq]
      have ht : ¬ LeastPrimeFactorAtLeast zTau n := by
        intro h
        simp [goldbachBasicWeight, h3, h2, h] at hw
        split_ifs at hw <;> omega
      unfold LeastPrimeFactorAtLeast at ht
      push Not at ht
      obtain ⟨s, hs, hsd, hsz⟩ := ht
      have hsmem := (Nat.mem_primeFactorsList (by omega : n ≠ 0)).mpr ⟨hs, hsd⟩
      have hsrq : s = r ∨ s = q := by simpa [heq] using hsmem
      right
      rcases hsrq with rfl | rfl
      · exact ⟨s, q, hr, hq, hnprod, hsz⟩
      · exact ⟨s, r, hq, hr, hnprod.trans (Nat.mul_comm _ _), hsz⟩

theorem goldbachBasicWeight_le_one (zAlpha zTau n : ℕ) :
    goldbachBasicWeight zAlpha zTau n ≤ 1 := by
  classical
  by_cases h3 : OmegaAtLeast 3 n
  · have h2 : OmegaAtLeast 2 n := by unfold OmegaAtLeast at *; omega
    simp [goldbachBasicWeight, h3, h2]
  · simp only [goldbachBasicWeight, h3, and_false, if_false, add_zero, sub_zero]
    split_ifs <;> omega

/-- Uniform scalar absorption. The cutoff depends only on ε, and is chosen
before N and the prime variable p. No explicit bound is claimed. -/
theorem exists_goldbachBasic_growth_cutoff (ε : ℝ) (hε : 0 < ε) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      1 < ε * N ∧ ((N : ℝ) ^ ((9 : ℝ) / 19 - ε)) ^ (19 : ℕ) ≤
        (ε * N) ^ (9 : ℕ) := by
  have ht : Tendsto (fun N : ℕ => (N : ℝ) ^ (-(19 * ε))) atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop (by positivity : 0 < 19 * ε)).comp
      tendsto_natCast_atTop_atTop
  have he : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-(19 * ε)) < ε ^ (9 : ℕ) :=
    ht.eventually_lt_const (by positivity)
  have hlarge : ∀ᶠ N : ℕ in atTop, 1 < ε * (N : ℝ) :=
    ((tendsto_natCast_atTop_atTop :
      Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop).const_mul_atTop hε).eventually
        (eventually_gt_atTop 1)
  apply Filter.Eventually.exists_forall_of_atTop
  filter_upwards [he, hlarge] with N he hlarge
  refine ⟨hlarge, ?_⟩
  have hN : (0 : ℝ) < N := by nlinarith
  calc
    ((N : ℝ) ^ ((9 : ℝ) / 19 - ε)) ^ (19 : ℕ) =
        (N : ℝ) ^ ((9 : ℝ) + -(19 * ε)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hN.le]
      congr 1
      norm_num
      ring
    _ = (N : ℝ) ^ (9 : ℕ) * (N : ℝ) ^ (-(19 * ε)) := by
      norm_num [Real.rpow_add hN]
    _ ≤ (N : ℝ) ^ (9 : ℕ) * ε ^ (9 : ℕ) :=
      mul_le_mul_of_nonneg_left he.le (by positivity)
    _ = (ε * N) ^ (9 : ℕ) := by ring

/-- The essential 1.9 inequality: the upper-cutoff prime obeys the literal
power imbalance after cancellation. Works also when r = q. -/
theorem oneNine_power_bound {N n r q : ℕ} {ε : ℝ}
    (hε : 0 < ε) (hn : ε * N < (n : ℝ))
    (hscale : ((N : ℝ) ^ ((9 : ℝ) / 19 - ε)) ^ (19 : ℕ) ≤
      (ε * N) ^ (9 : ℕ))
    (hr : 0 < r) (hnprod : n = r * q)
    (hrcut : r < goldbachPowerCutoff N ((9 : ℝ) / 19 - ε)) :
    r ^ 10 ≤ q ^ 9 := by
  have hrreal : (r : ℝ) < (N : ℝ) ^ ((9 : ℝ) / 19 - ε) :=
    Nat.lt_ceil.mp hrcut
  have hreal : (r : ℝ) ^ (19 : ℕ) ≤ (n : ℝ) ^ (9 : ℕ) := calc
    (r : ℝ) ^ (19 : ℕ) ≤ ((N : ℝ) ^ ((9 : ℝ) / 19 - ε)) ^ (19 : ℕ) :=
      pow_le_pow_left₀ (by positivity) hrreal.le 19
    _ ≤ (ε * N) ^ (9 : ℕ) := hscale
    _ ≤ (n : ℝ) ^ (9 : ℕ) := pow_le_pow_left₀ (by positivity) hn.le 9
  have hnat : r ^ 19 ≤ n ^ 9 := by exact_mod_cast hreal
  have hcancel : r ^ 9 * r ^ 10 ≤ r ^ 9 * q ^ 9 := by
    calc
      r ^ 9 * r ^ 10 = r ^ 19 := by ring
      _ ≤ n ^ 9 := hnat
      _ = r ^ 9 * q ^ 9 := by rw [hnprod, mul_pow]
  exact Nat.le_of_mul_le_mul_left hcancel (by positivity)

/-- Pointwise arithmetic producer under explicit scalar bounds. These scalar
bounds are discharged uniformly in the eventual theorem below. -/
theorem goldbachBasic_pointwise_of_growth {N p : ℕ} {ε α : ℝ}
    (hε : 0 < ε) (hlarge : 1 < ε * N)
    (hscale : ((N : ℝ) ^ ((9 : ℝ) / 19 - ε)) ^ (19 : ℕ) ≤
      (ε * N) ^ (9 : ℕ))
    (hp : p ∈ goldbachPrimeCarrier N ε) :
    goldbachBasicWeight (goldbachPowerCutoff N α)
      (goldbachPowerCutoff N ((9 : ℝ) / 19 - ε)) (N - p) ≤
        if IsOnePlusOneNineRepresentation N p then (1 : ℤ) else 0 := by
  classical
  obtain ⟨hpN, hpPrime, hpcut⟩ := Finset.mem_filter.mp hp
  have hpN' : p ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp hpN)
  have hnreal : ε * N < ((N - p : ℕ) : ℝ) := by
    rw [Nat.cast_sub hpN']
    linarith
  have hn : 2 ≤ N - p := by
    have h : (1 : ℝ) < ((N - p : ℕ) : ℝ) := hlarge.trans hnreal
    have : 1 < N - p := by exact_mod_cast h
    omega
  by_cases hw : 0 < goldbachBasicWeight (goldbachPowerCutoff N α)
      (goldbachPowerCutoff N ((9 : ℝ) / 19 - ε)) (N - p)
  · have hrep : IsOnePlusOneNineRepresentation N p := by
      refine ⟨hpPrime, ?_⟩
      rcases positive_goldbachBasicWeight_structure hn hw with hprime | ⟨r, q, hr, hq, heq, hcut⟩
      · refine ⟨1, N - p, Or.inl rfl, hprime, ?_, ?_⟩
        · simp only [one_mul]
          omega
        · simp only [one_pow]
          exact Nat.one_le_iff_ne_zero.mpr (pow_ne_zero 9 hprime.ne_zero)
      · refine ⟨r, q, Or.inr hr, hq, ?_, ?_⟩
        · omega
        · exact oneNine_power_bound hε hnreal hscale hr.pos heq hcut
    simpa only [if_pos hrep] using
      goldbachBasicWeight_le_one (goldbachPowerCutoff N α)
        (goldbachPowerCutoff N ((9 : ℝ) / 19 - ε)) (N - p)
  · have hw' : goldbachBasicWeight (goldbachPowerCutoff N α)
        (goldbachPowerCutoff N ((9 : ℝ) / 19 - ε)) (N - p) ≤ 0 := le_of_not_gt hw
    split_ifs <;> omega

/-- Genuine pointwise domination, with one cutoff chosen before N, α and p.
In fact the first inequality needs no restriction on α: the paper's
`0 < α < τ < 1/2` is an immediate specialization. -/
theorem goldbachBasic_eventual_pointwise (ε : ℝ) (hε : 0 < ε) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → ∀ α : ℝ, ∀ p ∈ goldbachPrimeCarrier N ε,
      goldbachBasicWeight (goldbachPowerCutoff N α)
        (goldbachPowerCutoff N ((9 : ℝ) / 19 - ε)) (N - p) ≤
          if IsOnePlusOneNineRepresentation N p then (1 : ℤ) else 0 := by
  obtain ⟨N0, hN0⟩ := exists_goldbachBasic_growth_cutoff ε hε
  refine ⟨N0, ?_⟩
  intro N hN α p hp
  exact goldbachBasic_pointwise_of_growth hε (hN0 N hN).1 (hN0 N hN).2 hp

/-- The literal difference carrier A from equation (4.5). -/
noncomputable def goldbachDifferenceCarrier (N : ℕ) (ε : ℝ) : Finset ℕ :=
  (goldbachPrimeCarrier N ε).image (fun p => N - p)

/-- The redundant finite range does not change the paper's prime cutoff. -/
theorem mem_goldbachPrimeCarrier_iff {N p : ℕ} {ε : ℝ} (hε : 0 ≤ ε) :
    p ∈ goldbachPrimeCarrier N ε ↔ p.Prime ∧ (p : ℝ) < (1 - ε) * N := by
  classical
  constructor
  · intro hp
    exact (Finset.mem_filter.mp hp).2
  · rintro ⟨hprime, hcut⟩
    apply Finset.mem_filter.mpr
    refine ⟨?_, hprime, hcut⟩
    have hpN : (p : ℝ) < N := by nlinarith [mul_nonneg hε (Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
    have hpN' : p < N := by exact_mod_cast hpN
    exact Finset.mem_range.mpr (by omega)

/-- The actual finite Goldbachbasic inequality. No pointwise-domination
assumption remains: the preceding producer supplies it. The threshold is
uniform in α and is an eventual specialization, not the source's effective bound. -/
theorem goldbachBasic_finite_le_D19 (ε : ℝ) (hε : 0 < ε) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → ∀ α : ℝ,
      goldbachBasicFiniteRHS (goldbachDifferenceCarrier N ε)
        (goldbachPowerCutoff N α) (goldbachPowerCutoff N ((9 : ℝ) / 19 - ε)) ≤
          (D19 N : ℤ) := by
  classical
  obtain ⟨N0, hN0⟩ := goldbachBasic_eventual_pointwise ε hε
  refine ⟨N0, ?_⟩
  intro N hN α
  let P := goldbachPrimeCarrier N ε
  let zAlpha := goldbachPowerCutoff N α
  let zTau := goldbachPowerCutoff N ((9 : ℝ) / 19 - ε)
  have hP : P ⊆ range (N + 1) := Finset.filter_subset _ _
  change goldbachBasicFiniteRHS (P.image (fun p => N - p)) zAlpha zTau ≤ (D19 N : ℤ)
  rw [← sum_goldbachBasicWeight_eq_finiteRHS]
  have himage :
      (∑ n ∈ P.image (fun p => N - p), goldbachBasicWeight zAlpha zTau n) =
        ∑ p ∈ P, goldbachBasicWeight zAlpha zTau (N - p) := by
    rw [Finset.sum_image]
    intro p hp p' hp' heq
    have hpN : p ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp (hP hp))
    have hpN' : p' ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp (hP hp'))
    exact (tsub_right_inj hpN hpN').mp heq
  rw [himage]
  calc
    (∑ p ∈ P, goldbachBasicWeight zAlpha zTau (N - p))
        ≤ ∑ p ∈ P, if IsOnePlusOneNineRepresentation N p then (1 : ℤ) else 0 := by
      exact Finset.sum_le_sum fun p hp => hN0 N hN α p hp
    _ = (((P.filter (IsOnePlusOneNineRepresentation N)).card : ℕ) : ℤ) :=
      sum_indicator_eq_card_filter P (IsOnePlusOneNineRepresentation N)
    _ ≤ (((onePlusOneNineRepresentedPrimes N).card : ℕ) : ℤ) := by
      exact_mod_cast Finset.card_le_card (by
        intro p hp
        rw [Finset.mem_filter] at hp
        exact mem_onePlusOneNineRepresentedPrimes_iff.mpr
          ⟨Nat.le_of_lt_succ (Finset.mem_range.mp (hP hp.1)), hp.2⟩)
    _ = (D19 N : ℤ) := rfl

/-- A positive actual Goldbachbasic RHS yields a literal 1+1.9 representation.
Only positivity of the four finite counts remains, not a pointwise input. -/
theorem exists_representation_of_goldbachBasicFiniteRHS_pos (ε : ℝ) (hε : 0 < ε) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → ∀ α : ℝ,
      0 < goldbachBasicFiniteRHS (goldbachDifferenceCarrier N ε)
        (goldbachPowerCutoff N α) (goldbachPowerCutoff N ((9 : ℝ) / 19 - ε)) →
      ∃ p r q : ℕ,
        p ≤ N ∧ p.Prime ∧ (r = 1 ∨ r.Prime) ∧ q.Prime ∧
          N = p + r * q ∧ r ^ 10 ≤ q ^ 9 := by
  obtain ⟨N0, hN0⟩ := goldbachBasic_finite_le_D19 ε hε
  refine ⟨N0, ?_⟩
  intro N hN α hpos
  rw [← D19_pos_iff]
  have hle := hN0 N hN α
  omega

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine
