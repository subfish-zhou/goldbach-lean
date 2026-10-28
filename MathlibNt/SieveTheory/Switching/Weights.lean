import MathlibNt.SieveTheory.Chen.Representations
import Mathlib.Topology.MetricSpace.ThickenedIndicator
import MathlibNt.SieveTheory.Selberg.Liu.LiuSelbergDenominatorAsymptotic
import MathlibNt.SieveTheory.Distribution.LiuPan.LiuPanPrimePowerCharacters
import MathlibNt.SieveTheory.Distribution.BombieriVinogradov
import MathlibNt.SieveTheory.LinearSieve.UpperRosserDensity

/-!
# Chen weights and representation counts

Exact divisibility, prime-power and triple-factor weights, historical representation
counts, corrected lower cutoffs, and uniform control of the singular-series tail.

All declarations retain the `MathlibNt.SieveTheory.SwitchingPrinciple` namespace.
-/

/-
! # MathlibNt.SieveTheory.SwitchingPrinciple

## Switching Principle

The switching principle is a central technique in the proof of Chen's theorem. Chen Jingrun
introduces a weight function w(n) to turn the condition "N-p has at most two prime factors" into estimates accessible to sieve methods.

**Main idea** (Chen 1973, Liu 2022):

1. **W(N)**: the count of primes p satisfying the sieve conditions
   - N-p has no prime factor ≤ N^(1/10)
   - N-p has at most one prime factor in (N^(1/10), N^(1/3)]
   - The Jurkat-Richert lower bound gives W(N) ≥ 2.6408 𝔖(N) N/log²N

2. **Ω**: historical switched sum over admissible source pairs
   - Ω = Σ_a Σ_{ap₃ ≤ N, N-ap₃ prime} f(a)
   - f(a) is the indicator of a = p₁p₂ satisfying the range conditions
   - The Selberg sieve gives Ω ≤ 3.9404 𝔖(N) N/log²N

3. **Historical numerical inequality**: W(N) - Ω/2 > 0
   - W(N) - Ω/2 ≥ (2.6408 - 3.9404/2) 𝔖(N) N/log²N
   - = 0.6706 𝔖(N) N/log²N > 0
   - this implies Chen only with an additional multiplicity-correct counting
     theorem; the source-pair multiplicity is not uniformly two

References:
  - Chen, J.R. (1973), Sci. Sinica 16, 157-176
  - Liu, Z. (2022), arXiv:2203.07871
  - Nathanson, "Additive Number Theory", GTM 164, Ch. 10
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

/-! ## Weight function w(n) -/

/-- Exact prime-power divisibility: q^k ∥ n means q^k | n but q^(k+1) ∤ n. -/
def exactDiv (q k n : ℕ) : Prop :=
  q ^ k ∣ n ∧ ¬ q ^ (k + 1) ∣ n

/-- Sum of the multiplicities of prime powers exactly dividing n, with primes in [z, y):
  Σ_{z ≤ q < y, q prime, q^k ∥ n} k. -/
noncomputable def primePowerSum (n z y : ℕ) : ℝ :=
  ((range y).filter (fun q => q.Prime ∧ z ≤ q ∧
    ∃ k : ℕ, 1 ≤ k ∧ exactDiv q k n)).sum (fun q =>
      -- Take the largest k for which q^k | n, namely the multiplicity of q.
      (n.factorization q : ℝ))

/-- Triple-factorization count: Σ_{p₁p₂p₃ = n, z ≤ p₁ < y ≤ p₂ ≤ p₃} 1.

Note: the non-strict inequality p₂ ≤ p₃ correctly counts n = q * r²
(the case p₂ = p₃ = r). The original condition p₂ < p₃ would omit these factorizations. -/
noncomputable def tripleFactorCount (n z y : ℕ) : ℝ :=
  (Finset.card ((Finset.range (n + 1)).filter (fun p₁ =>
    p₁.Prime ∧ z ≤ p₁ ∧ p₁ < y ∧
    ∃ p₂ p₃, p₂.Prime ∧ p₃.Prime ∧ y ≤ p₂ ∧ p₂ ≤ p₃ ∧
      p₁ * p₂ * p₃ = n ∧ p₁ < p₂ ∧ p₂ ≤ p₃)) : ℝ)

/-- **Weight function w(n)** (Chen's switching weight):

  w(n) = 1 - (1/2) Σ_{z ≤ q < y, q^k ∥ n} k - (1/2) Σ_{p₁p₂p₃=n, z ≤ p₁ < y ≤ p₂ ≤ p₃} 1

If w(n) > 0 and n has no prime factor ≤ z, then n ∈ {1, p, p₁p₂ : p, p₁, p₂ ≥ z}. -/
noncomputable def chenWeight (n z y : ℕ) : ℝ :=
  1 - (1/2) * primePowerSum n z y - (1/2) * tripleFactorCount n z y

/-- Summation range for primePowerSum: primes in [z, y) with q^k ∥ n for some k ≥ 1. -/
private noncomputable def Sfilter (n z y : ℕ) : Finset ℕ :=
  (range y).filter (fun q => q.Prime ∧ z ≤ q ∧ ∃ k : ℕ, 1 ≤ k ∧ exactDiv q k n)

/-- Counting range for tripleFactorCount. -/
private noncomputable def Tfilter (n z y : ℕ) : Finset ℕ :=
  (Finset.range (n + 1)).filter (fun p₁ =>
    p₁.Prime ∧ z ≤ p₁ ∧ p₁ < y ∧
    ∃ p₂ p₃, p₂.Prime ∧ p₃.Prime ∧ y ≤ p₂ ∧ p₂ ≤ p₃ ∧
      p₁ * p₂ * p₃ = n ∧ p₁ < p₂ ∧ p₂ ≤ p₃)

/-- The factorization exponent gives exact divisibility, including exponent zero. -/
private lemma exactDiv_of_factorization {p n : ℕ} (hp : p.Prime) (hn : n ≠ 0) :
    exactDiv p (n.factorization p) n := by
  unfold exactDiv
  constructor
  · exact (hp.pow_dvd_iff_le_factorization hn).2 le_rfl
  · intro h
    have hle : n.factorization p + 1 ≤ n.factorization p :=
      (hp.pow_dvd_iff_le_factorization hn).1 h
    omega

/-- A prime p dividing n with z ≤ p < y belongs to the summation range of primePowerSum. -/
private lemma primePowerSum_mem_of_dvd {n z y p : ℕ} (hp : p.Prime) (hz : z ≤ p)
    (hp_lt : p < y) (hn : n ≠ 0) (hpdvd : p ∣ n) :
    p ∈ Sfilter n z y := by
  rw [Sfilter, mem_filter]
  exact ⟨by simpa using hp_lt, hp, hz, n.factorization p,
    (hp.dvd_iff_one_le_factorization hn).1 hpdvd, exactDiv_of_factorization hp hn⟩

/-- S = (Σ (n.factorization q : ℕ) : ℝ). -/
private lemma primePowerSum_eq_cast (n z y : ℕ) :
    primePowerSum n z y = ((Sfilter n z y).sum (fun q => n.factorization q) : ℝ) := by
  unfold primePowerSum Sfilter
  rw [← Nat.cast_sum]

/-- T = (card : ℝ). -/
private lemma tripleFactorCount_eq_cast (n z y : ℕ) :
    tripleFactorCount n z y = ((Tfilter n z y).card : ℝ) := by
  rfl

/-- q ∈ Sfilter implies 1 ≤ S, as a real-number inequality. -/
private lemma primePowerSum_ge_one_of_mem {n z y q : ℕ} (hn : 1 ≤ n)
    (hq : q ∈ Sfilter n z y) : (1 : ℝ) ≤ primePowerSum n z y := by
  have hq' : q ∈ (range y).filter (fun x => x.Prime ∧ z ≤ x ∧
      ∃ k : ℕ, 1 ≤ k ∧ exactDiv x k n) := by simpa [Sfilter] using hq
  rw [mem_filter] at hq'
  rcases hq' with ⟨_, hq_prime, _, k, hk, hex⟩
  have hn0 : n ≠ 0 := by omega
  have hk_le : k ≤ n.factorization q := (hq_prime.pow_dvd_iff_le_factorization hn0).1 hex.1
  have hfact_ge : (1 : ℕ) ≤ n.factorization q := by omega
  have hsum_ge : (1 : ℕ) ≤ (Sfilter n z y).sum (fun x => n.factorization x) := by
    exact le_trans hfact_ge
      (Finset.single_le_sum (s := Sfilter n z y) (f := fun x : ℕ => n.factorization x)
        (by intro x hx; exact Nat.zero_le _) hq)
  rw [primePowerSum_eq_cast n z y]
  exact_mod_cast hsum_ge

/-- Cases for a list of length at most two. -/
private lemma length_le_two_cases {l : List ℕ} (hl : l.length ≤ 2) :
    l = [] ∨ (∃ a, l = [a]) ∨ ∃ a b, l = [a, b] := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩ <;> simp_all

/-- If S = 0 and n has no prime factor < z, all prime factors of n are ≥ y. -/
private lemma all_prime_factors_ge_y_of_S_zero {n z y : ℕ}
    (hn : 1 ≤ n) (hS : primePowerSum n z y = 0)
    (hcop : ∀ p : ℕ, p.Prime → p < z → ¬ p ∣ n) :
    ∀ p : ℕ, p.Prime → p ∣ n → y ≤ p := by
  intro p hp hpdvd
  by_contra h
  have hp_lt_y : p < y := by omega
  by_cases hp_lt_z : p < z
  · exact absurd hpdvd (hcop p hp hp_lt_z)
  · have hz_le_p : z ≤ p := by omega
    have hpS : p ∈ Sfilter n z y :=
      primePowerSum_mem_of_dvd hp hz_le_p hp_lt_y (by omega : n ≠ 0) hpdvd
    have hS_ge : (1 : ℝ) ≤ primePowerSum n z y := primePowerSum_ge_one_of_mem hn hpS
    linarith

/-- If all prime factors are ≥ y and n < y³, then Ω(n) ≤ 2. -/
private lemma omega_le_two_of_lt_cube {n y : ℕ} (hy : 2 ≤ y) (hn : n ≠ 0)
    (hall : ∀ p : ℕ, p.Prime → p ∣ n → y ≤ p) (hn_lt : (n : ℝ) < (y : ℝ) ^ 3) :
    (n.primeFactorsList.length) ≤ 2 := by
  have hprod : y ^ n.primeFactorsList.length ≤ n.primeFactorsList.prod := by
    apply List.pow_card_le_prod
    intro p hp
    exact hall p (Nat.prime_of_mem_primeFactorsList hp) (Nat.dvd_of_mem_primeFactorsList hp)
  by_contra h
  have hlen_ge3 : 3 ≤ n.primeFactorsList.length := by omega
  have hpow_le : y ^ 3 ≤ y ^ n.primeFactorsList.length :=
    Nat.pow_le_pow_right (by omega : 1 ≤ y) hlen_ge3
  have hle_n : y ^ 3 ≤ n := by
    calc
      y ^ 3 ≤ y ^ n.primeFactorsList.length := hpow_le
      _ ≤ n.primeFactorsList.prod := hprod
      _ = n := Nat.prod_primeFactorsList hn
  have hcast : (y : ℝ) ^ 3 ≤ (n : ℝ) := by exact_mod_cast hle_n
  have : (y : ℝ) ^ 3 < (y : ℝ) ^ 3 := lt_of_le_of_lt hcast hn_lt
  linarith

/-- If n < y³ and all prime factors are ≥ y, n is 1, a prime, or a product of two primes, each ≥ y. -/
private lemma at_most_two_factors {n y : ℕ} (hy : 2 ≤ y) (hn : 1 ≤ n)
    (hall : ∀ p : ℕ, p.Prime → p ∣ n → y ≤ p) (hn_lt : (n : ℝ) < (y : ℝ) ^ 3) :
    n = 1 ∨ n.Prime ∨ ∃ p₁ p₂ : ℕ, p₁.Prime ∧ p₂.Prime ∧ y ≤ p₁ ∧ y ≤ p₂ ∧ n = p₁ * p₂ := by
  have hlen : n.primeFactorsList.length ≤ 2 :=
    omega_le_two_of_lt_cube hy (by omega : n ≠ 0) hall hn_lt
  rcases length_le_two_cases hlen with hnil | ⟨a, h1⟩ | ⟨a, b, h2⟩
  · left
    simpa [hnil] using (Nat.prod_primeFactorsList (by omega : n ≠ 0)).symm
  · right; left
    have hn_eq : n = a := by
      simpa [h1] using (Nat.prod_primeFactorsList (by omega : n ≠ 0)).symm
    rw [hn_eq]
    exact Nat.prime_of_mem_primeFactorsList (by rw [h1]; simp)
  · right; right
    have hn_eq : n = a * b := by
      simpa [h2] using (Nat.prod_primeFactorsList (by omega : n ≠ 0)).symm
    have ha : a.Prime := Nat.prime_of_mem_primeFactorsList (by rw [h2]; simp)
    have hb : b.Prime := Nat.prime_of_mem_primeFactorsList (by rw [h2]; simp)
    exact ⟨a, b, ha, hb,
      hall a ha (by rw [hn_eq]; exact dvd_mul_right a b),
      hall b hb (by rw [hn_eq]; exact dvd_mul_left b a), hn_eq⟩

/-- A triple factorization q·p₂·p₃ = n gives T ≥ 1. -/
private lemma tripleFactorCount_ge_one {n z y q p₂ p₃ : ℕ} (hq : q.Prime) (hzq : z ≤ q)
    (hqy : q < y) (hp2 : p₂.Prime) (hp3 : p₃.Prime) (hyp2 : y ≤ p₂)
    (hp2p3 : p₂ ≤ p₃) (hqlt : q < p₂) (hn : n = q * p₂ * p₃) :
    (1 : ℝ) ≤ tripleFactorCount n z y := by
  have hq_lt_n : q < n + 1 := by
    have : q ≤ n := by
      rw [hn]
      nlinarith [show (1 : ℕ) ≤ p₂ * p₃ by nlinarith [hp2.two_le, hp3.two_le]]
    omega
  have hq_mem : q ∈ Tfilter n z y := by
    rw [Tfilter, mem_filter]
    exact ⟨by simpa using hq_lt_n, hq, hzq, hqy,
      p₂, p₃, hp2, hp3, hyp2, hp2p3, hn.symm, hqlt, hp2p3⟩
  have hcard_ge : (1 : ℕ) ≤ (Tfilter n z y).card := by
    have hpos : 0 < (Tfilter n z y).card := Finset.card_pos.mpr ⟨q, hq_mem⟩
    omega
  have hT_cast : tripleFactorCount n z y = ((Tfilter n z y).card : ℝ) :=
    tripleFactorCount_eq_cast n z y
  rw [hT_cast]
  exact_mod_cast hcard_ge

/-- S = 1 gives a unique prime q ∈ [z,y), with n = q·m and all prime factors of m ≥ y. -/
private lemma S_one_structure {n z y : ℕ} (hn : 1 ≤ n)
    (hS : primePowerSum n z y = 1)
    (hcop : ∀ p : ℕ, p.Prime → p < z → ¬ p ∣ n) :
    ∃ q m : ℕ, q.Prime ∧ z ≤ q ∧ q < y ∧ n = q * m ∧
      (∀ p : ℕ, p.Prime → p ∣ m → y ≤ p) := by
  have hS_nat : (Sfilter n z y).sum (fun q => n.factorization q) = 1 := by
    rw [primePowerSum_eq_cast n z y] at hS
    exact_mod_cast hS
  have hfact_ge : ∀ q ∈ Sfilter n z y, (1 : ℕ) ≤ n.factorization q := by
    intro q hq
    rw [Sfilter, mem_filter] at hq
    rcases hq with ⟨_, hq_prime, _, k, hk, hex⟩
    have hn0 : n ≠ 0 := by omega
    have hk_le : k ≤ n.factorization q := (hq_prime.pow_dvd_iff_le_factorization hn0).1 hex.1
    omega
  have hcard : (Sfilter n z y).card = 1 := by
    have hle : (Sfilter n z y).card ≤ 1 := by
      have hcl : (Sfilter n z y).card ≤ (Sfilter n z y).sum (fun q => n.factorization q) := by
        rw [Finset.card_eq_sum_ones (Sfilter n z y)]
        exact Finset.sum_le_sum (by
          intro q hq
          exact hfact_ge q hq)
      omega
    have hge : 1 ≤ (Sfilter n z y).card := by
      have hnonempty : (Sfilter n z y).Nonempty := by
        by_contra hne
        have h_empty : Sfilter n z y = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
        simp [h_empty] at hS_nat
      have hpos : 0 < (Sfilter n z y).card := Finset.card_pos.mpr hnonempty
      omega
    omega
  rcases Finset.card_eq_one.mp hcard with ⟨q, hq_singleton⟩
  have hq_mem : q ∈ Sfilter n z y := by
    rw [hq_singleton]
    simp
  rw [Sfilter, mem_filter] at hq_mem
  rcases hq_mem with ⟨hq_range, hq_prime, hzq, k, hk, hex⟩
  have hq_lt_y : q < y := by simpa using hq_range
  have hfact1 : n.factorization q = 1 := by
    have : (Sfilter n z y).sum (fun x => n.factorization x) = n.factorization q := by
      rw [hq_singleton]
      simp
    omega
  have hn0 : n ≠ 0 := by omega
  have hdvd : q ∣ n := (hq_prime.dvd_iff_one_le_factorization hn0).2 (by omega)
  obtain ⟨m, hm⟩ := exists_eq_mul_right_of_dvd hdvd
  refine ⟨q, m, hq_prime, hzq, hq_lt_y, hm, ?_⟩
  intro p hp hpdvd_m
  have hpdvd_n : p ∣ n := by
    rw [hm]
    exact dvd_trans hpdvd_m (dvd_mul_left m q)
  by_contra h
  have hp_lt_y : p < y := by omega
  by_cases hp_lt_z : p < z
  · exact absurd hpdvd_n (hcop p hp hp_lt_z)
  · have hz_le_p : z ≤ p := by omega
    have hpS : p ∈ Sfilter n z y :=
      primePowerSum_mem_of_dvd hp hz_le_p hp_lt_y hn0 hpdvd_n
    have hp_eq : q = p := by
      rw [hq_singleton] at hpS
      simpa [eq_comm] using hpS
    have hq2_dvd : q ^ 2 ∣ n := by
      rw [hm, hp_eq]
      simpa [pow_two] using mul_dvd_mul_left p hpdvd_m
    have hexact1 : exactDiv q 1 n := by
      rw [← hfact1]
      exact exactDiv_of_factorization hq_prime hn0
    exact hexact1.2 (by simpa using hq2_dvd)

/-- w(n) > 0 implies that n is 1, a prime, or a product of two primes, provided n has no prime factor < z and n < y³.

The extra hypothesis `n < y³` is needed: if all prime factors of n are ≥ y, then w(n) = 1 > 0,
but n ≥ y³ can have three or more prime factors, each ≥ y. The hypothesis n < y³
excludes this case and ensures that n has at most two prime factors. -/
theorem chenWeight_pos_implies_semiprime
    (n z y : ℕ) (hz : 2 ≤ z) (hy : z < y) (hn : 1 ≤ n)
    (hn_lt : (n : ℝ) < (y : ℝ) ^ 3)
    (h_coprime : ∀ p : ℕ, p.Prime → p < z → ¬ p ∣ n)
    (hw : 0 < chenWeight n z y) :
    n = 1 ∨ n.Prime ∨ ∃ p₁ p₂ : ℕ, p₁.Prime ∧ p₂.Prime ∧ z ≤ p₁ ∧ z ≤ p₂ ∧ n = p₁ * p₂ := by
  have hy2 : 2 ≤ y := by omega
  have hS_cast : primePowerSum n z y =
      ((Sfilter n z y).sum (fun q => n.factorization q) : ℝ) := primePowerSum_eq_cast n z y
  have hT_cast : tripleFactorCount n z y = ((Tfilter n z y).card : ℝ) :=
    tripleFactorCount_eq_cast n z y
  have hST : primePowerSum n z y + tripleFactorCount n z y < 2 := by
    unfold chenWeight at hw
    nlinarith
  have hST_nat : (Sfilter n z y).sum (fun q => n.factorization q) + (Tfilter n z y).card < 2 := by
    rw [hS_cast, hT_cast] at hST
    exact_mod_cast hST
  have hSTle : (Sfilter n z y).sum (fun q => n.factorization q) + (Tfilter n z y).card ≤ 1 := by
    omega
  have hS_cases : (Sfilter n z y).sum (fun q => n.factorization q) = 0 ∨
      (Sfilter n z y).sum (fun q => n.factorization q) = 1 := by omega
  rcases hS_cases with hS0 | hS1
  · -- S = 0: all prime factors are ≥ y, and there are at most two.
    have hS0r : primePowerSum n z y = 0 := by
      rw [hS_cast]
      exact_mod_cast hS0
    have hall : ∀ p : ℕ, p.Prime → p ∣ n → y ≤ p :=
      all_prime_factors_ge_y_of_S_zero hn hS0r h_coprime
    rcases at_most_two_factors hy2 hn hall hn_lt with hn1 | hprime | ⟨p₁, p₂, hp₁, hp₂, hp₁y, hp₂y, hn_eq⟩
    · exact Or.inl hn1
    · exact Or.inr (Or.inl hprime)
    · exact Or.inr (Or.inr ⟨p₁, p₂, hp₁, hp₂,
        le_trans (le_of_lt hy) hp₁y, le_trans (le_of_lt hy) hp₂y, hn_eq⟩)
  · -- S = 1 forces T = 0 because S + T ≤ 1.
    have hT0 : (Tfilter n z y).card = 0 := by omega
    have hS1r : primePowerSum n z y = 1 := by
      rw [hS_cast]
      exact_mod_cast hS1
    have hT0r : tripleFactorCount n z y = 0 := by
      rw [hT_cast]
      exact_mod_cast hT0
    rcases S_one_structure hn hS1r h_coprime with
      ⟨q, m, hq_prime, hzq, hq_lt_y, hn_eq, hm_factors⟩
    have hm_pos : 0 < m := by
      by_contra h
      have hm0 : m = 0 := by omega
      rw [hm0, mul_zero] at hn_eq
      omega
    have hm_lt_n : m < n := by
      have hq_ge2 : 2 ≤ q := hq_prime.two_le
      have hmul : 2 * m ≤ n := by
        rw [hn_eq]
        exact Nat.mul_le_mul_right m hq_ge2
      nlinarith
    have hn_lt_nat : n < y ^ 3 := by exact_mod_cast hn_lt
    have hm_lt_cube : (m : ℝ) < (y : ℝ) ^ 3 := by
      exact_mod_cast (lt_trans hm_lt_n hn_lt_nat)
    rcases at_most_two_factors hy2 (by omega) hm_factors hm_lt_cube with
      hm1 | hmprime | ⟨a, b, ha, hb, hya, hyb, hm⟩
    · -- m = 1 implies n = q, a prime.
      right; left
      simpa [hn_eq, hm1] using hq_prime
    · -- A prime cofactor gives a semiprime directly.
      right; right
      exact ⟨q, m, hq_prime, hmprime, hzq,
        (le_of_lt hy).trans (hm_factors m hmprime (dvd_refl m)), hn_eq⟩
    · -- Two prime cofactors give T ≥ 1, contradicting T = 0.
      have hn_triple : n = q * a * b := by rw [hn_eq, hm, Nat.mul_assoc]
      rcases le_total a b with hab | hba
      · have hT_ge := tripleFactorCount_ge_one hq_prime hzq hq_lt_y ha hb hya hab
          (hq_lt_y.trans_le hya) hn_triple
        linarith
      · have hT_ge := tripleFactorCount_ge_one hq_prime hzq hq_lt_y hb ha hyb hba
          (hq_lt_y.trans_le hyb) (show n = q * b * a by rw [hn_triple]; ring)
        linarith

/-! ## Definition of W(N) -/

/-- The finite candidate set underlying the working W-count.  It is named so
that a corrected switching argument can partition its good, bad, and boundary
fibres without changing the analytic-facing count all at once. -/
noncomputable def chenWCandidates (N : ℕ) : Finset ℕ :=
  let z := Nat.floor ((N : ℝ) ^ (1/10 : ℝ))
  let y := Nat.floor ((N : ℝ) ^ (1/3 : ℝ))
  (Finset.range N).filter (fun p =>
    p.Prime ∧
    (∀ q : ℕ, q.Prime → q ≤ z → ¬ q ∣ (N - p)) ∧
    (Finset.card ((Finset.range (y + 1)).filter (fun q =>
      q.Prime ∧ z < q ∧ q ≤ y ∧ q ∣ (N - p))) ≤ 1))


/-! ## Definition of Ω (the switched sum) -/


/-! ## The key inequality -/


/-- Corrected lower sieve cutoff.  The `max 2` removes the small-`N`
degeneracy of the historical floor cutoff. -/
noncomputable def correctedChenZ (N : ℕ) : ℕ :=
  max 2 (Nat.floor ((N : ℝ) ^ (1 / 10 : ℝ)))

/-- The local compatibility copy and the imported analytic truncation are
definitionally the same finite Euler product. -/
theorem singularSeriesTruncated_eq_ant (N z : ℕ) :
    SingularSeries.singularSeriesTruncated N z =
      AnalyticNumberTheory.Sieve.singularSeriesTruncated N z := by
  rfl


namespace Internal

/-! ## Uniform lower bound for the truncated singular series: 𝔖_trunc ≥ c·𝔖 -/

/-- For `N > 2^110`, the corrected cutoff `z = max 2 ⌊N^{1/10}⌋` satisfies
`2^11 < N^{1/10}` (real exponent). -/
theorem chenZ_root_large (N : ℕ) (hNbig : 2 ^ 110 < N) :
    (2 ^ 11 : ℝ) < (N : ℝ) ^ (1 / 10 : ℝ) := by
  have hNcast : (2 ^ 110 : ℝ) < (N : ℝ) := by exact_mod_cast hNbig
  have hpow := Real.rpow_lt_rpow (by positivity : 0 ≤ (2 ^ 110 : ℝ)) hNcast
    (by norm_num : 0 < (1 / 10 : ℝ))
  have hval : (2 ^ 110 : ℝ) ^ (1 / 10 : ℝ) = (2 : ℝ) ^ 11 := by
    norm_num [Real.rpow_natCast, Real.rpow_mul, Real.rpow_one]
  rwa [hval] at hpow

end Internal

namespace Internal

/-- `z = max 2 ⌊N^{1/10}⌋` lies above `N^{1/10}/2` for `N > 2^110`. -/
theorem chenZ_ge_root_half (N : ℕ) (hNbig : 2 ^ 110 < N) :
    (N : ℝ) ^ (1 / 10 : ℝ) / 2 ≤ correctedChenZ N := by
  let x : ℝ := (N : ℝ) ^ (1 / 10 : ℝ)
  have hx2 : (2 : ℝ) ≤ x := by
    have h := chenZ_root_large N hNbig
    dsimp [x]
    linarith
  have hfloor : (Nat.floor x : ℝ) ≤ x := by
    dsimp [x]
    exact Nat.floor_le (by positivity : 0 ≤ (N : ℝ) ^ (1 / 10 : ℝ))
  have hfloor_ge : x - 1 ≤ (Nat.floor x : ℝ) := by
    dsimp [x]
    have hlt := Nat.lt_floor_add_one ((N : ℝ) ^ (1 / 10 : ℝ))
    linarith
  have hzhalf : x / 2 ≤ (correctedChenZ N : ℝ) := by
    have h1 : x / 2 ≤ x - 1 := by linarith
    have h2 : x - 1 ≤ (Nat.floor x : ℝ) := hfloor_ge
    have h3 : (Nat.floor x : ℝ) ≤ (correctedChenZ N : ℝ) := by
      unfold correctedChenZ
      exact_mod_cast (le_max_right 2 (Nat.floor x))
    linarith
  simpa [x] using hzhalf

end Internal

namespace Internal

/-- `z = max 2 ⌊N^{1/10}⌋ ≥ 3` for `N > 2^110`. -/
theorem chenZ_ge_three (N : ℕ) (hNbig : 2 ^ 110 < N) :
    3 ≤ correctedChenZ N := by
  have h := chenZ_ge_root_half N hNbig
  have hroot : (2 ^ 10 : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) / 2 := by
    have hl := chenZ_root_large N hNbig
    linarith
  have hz : (2 ^ 10 : ℝ) ≤ (correctedChenZ N : ℝ) := le_trans hroot h
  have hz3 : (3 : ℝ) ≤ (correctedChenZ N : ℝ) := by
    nlinarith [show (8 : ℝ) ≤ 2 ^ 10 by norm_num]
  exact_mod_cast hz3

end Internal

namespace Internal

/-- `z = max 2 ⌊N^{1/10}⌋ ≤ N + 1` for `2 ≤ N`. -/
theorem chenZ_le_N_add_one (N : ℕ) (hN2 : 2 ≤ N) :
    correctedChenZ N ≤ N + 1 := by
  unfold correctedChenZ
  apply max_le_iff.mpr
  constructor
  · omega
  · have hxle : (N : ℝ) ^ (1 / 10 : ℝ) ≤ (N : ℝ) := by
      have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
      have hp := Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num : (1 / 10 : ℝ) ≤ 1)
      simpa using hp
    have hf : (Nat.floor ((N : ℝ) ^ (1 / 10 : ℝ)) : ℝ) ≤ (N : ℝ) + 1 := by
      exact le_trans (Nat.floor_le (by positivity : 0 ≤ (N : ℝ) ^ (1 / 10 : ℝ)))
        (by linarith)
    exact_mod_cast hf

end Internal

/-- The product of pairwise coprime prime divisors of `N` divides `N`. -/
private theorem prod_dvd_of_prime_divisors {N : ℕ} {s : Finset ℕ} (hdiv : ∀ p ∈ s, p ∣ N)
    (hprime : ∀ p ∈ s, p.Prime) : (∏ p ∈ s, p) ∣ N := by
  apply s.prod_dvd_of_isRelPrime _ hdiv
  intro p hp q hq hpq
  exact Nat.coprime_iff_isRelPrime.mp
    ((Nat.coprime_primes (hprime p hp) (hprime q hq)).mpr hpq)

namespace Internal

/-- Every positive `n ≤ N` has at most ten prime divisors in
`[correctedChenZ N, N]` when `N > 2^110`. -/
theorem chenZ_tail_prime_count_le (N n : ℕ) (hNbig : 2 ^ 110 < N)
    (hnpos : 0 < n) (hnle : n ≤ N) :
    ((Finset.Ico (correctedChenZ N) (N + 1)).filter
      (fun p => p.Prime ∧ p ∣ n)).card ≤ 10 := by
  let s : Finset ℕ := (Finset.Ico (correctedChenZ N) (N + 1)).filter
    (fun p => p.Prime ∧ p ∣ n)
  by_contra hnot
  have hnot' : ¬ s.card ≤ 10 := by simpa [s] using hnot
  have hk : 11 ≤ s.card := by omega
  have hz3 : 3 ≤ correctedChenZ N := chenZ_ge_three N hNbig
  -- each element of s is ≥ z
  have hge : ∀ p ∈ s, correctedChenZ N ≤ p := by
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hpIco, _⟩
    exact (Finset.mem_Ico.mp hpIco).1
  have hdiv : ∀ p ∈ s, p ∣ n := by
    intro p hp
    exact (Finset.mem_filter.mp hp).2.2
  have hprime : ∀ p ∈ s, p.Prime := by
    intro p hp
    exact (Finset.mem_filter.mp hp).2.1
  -- product of elements of s divides n, hence is at most N
  have hprod_dvd : (∏ p ∈ s, p) ∣ n := prod_dvd_of_prime_divisors hdiv hprime
  have hNpos : 0 < N := by
    have h : 2 ^ 110 ≤ N := le_of_lt hNbig
    omega
  have hprod_le : (∏ p ∈ s, (p : ℝ)) ≤ (N : ℝ) := by
    have hnat : (∏ p ∈ s, p) ≤ N :=
      (Nat.le_of_dvd hnpos hprod_dvd).trans hnle
    have hcast : ((∏ p ∈ s, p : ℕ) : ℝ) = ∏ p ∈ s, (p : ℝ) := by
      rw [Nat.cast_prod]
    have hcast_le : ((∏ p ∈ s, p : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hnat
    simpa [hcast] using hcast_le
  -- product ≥ z^card ≥ z^11
  have hz_ge : (correctedChenZ N : ℝ) ≥ (N : ℝ) ^ (1 / 10 : ℝ) / 2 :=
    chenZ_ge_root_half N hNbig
  have hz_nonneg : (0 : ℝ) ≤ correctedChenZ N := by
    have : (3 : ℝ) ≤ correctedChenZ N := by exact_mod_cast hz3
    linarith
  have hz1r : (1 : ℝ) ≤ correctedChenZ N := by
    have : (3 : ℝ) ≤ correctedChenZ N := by exact_mod_cast hz3
    linarith
  have hprod_ge_zcard : (correctedChenZ N : ℝ) ^ s.card ≤ (∏ p ∈ s, (p : ℝ)) := by
    calc
      (correctedChenZ N : ℝ) ^ s.card = ∏ p ∈ s, (correctedChenZ N : ℝ) := by
        rw [Finset.prod_const]
      _ ≤ ∏ p ∈ s, (p : ℝ) := by
        apply Finset.prod_le_prod
        · intro p hp
          exact hz_nonneg
        · intro p hp
          exact_mod_cast hge p hp
  have hpow : (correctedChenZ N : ℝ) ^ 11 ≤ (correctedChenZ N : ℝ) ^ s.card :=
    pow_le_pow_right₀ hz1r hk
  have hprod_ge : (correctedChenZ N : ℝ) ^ 11 ≤ (∏ p ∈ s, (p : ℝ)) :=
    le_trans hpow hprod_ge_zcard
  -- z^11 > N
  let x : ℝ := (N : ℝ) ^ (1 / 10 : ℝ)
  have hx10 : x ^ 10 = (N : ℝ) := by
    dsimp [x]
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul (by exact_mod_cast (le_of_lt hNpos))]
    norm_num
  have hx11 : x ^ 11 = (N : ℝ) * x := by
    rw [pow_succ, hx10]
  have hxgt : (2 ^ 11 : ℝ) < x := chenZ_root_large N hNbig
  have hxpos : (0 : ℝ) < x := by
    dsimp [x]
    exact Real.rpow_pos_of_pos (by exact_mod_cast hNpos) _
  have hxdiv : (1 : ℝ) < x / 2 ^ 11 := by
    rw [one_lt_div (by positivity : (0 : ℝ) < 2 ^ 11)]
    exact hxgt
  have hgt : (N : ℝ) < x ^ 11 / 2 ^ 11 := by
    rw [hx11]
    have hmain : (N : ℝ) * (x / 2 ^ 11) > (N : ℝ) * 1 := by
      exact mul_lt_mul_of_pos_left hxdiv (by exact_mod_cast hNpos)
    simpa [mul_div_assoc, mul_one] using hmain
  have hz11_ge : (x / 2) ^ 11 ≤ (correctedChenZ N : ℝ) ^ 11 := by
    apply pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ x / 2)
    exact (by simpa [x] using hz_ge : x / 2 ≤ (correctedChenZ N : ℝ))
  have hdivpow : (x / 2) ^ 11 = x ^ 11 / 2 ^ 11 := by
    rw [div_pow]
  have hz11 : (N : ℝ) < (correctedChenZ N : ℝ) ^ 11 := by
    calc
      (N : ℝ) < x ^ 11 / 2 ^ 11 := hgt
      _ = (x / 2) ^ 11 := hdivpow.symm
      _ ≤ (correctedChenZ N : ℝ) ^ 11 := hz11_ge
  linarith

end Internal

namespace Internal

/-- 𝔖(N) = 𝔖_trunc(N, z−1) · ∏_{z ≤ p ≤ N} localFactor(p, N), the exact
tail split used to compare the truncated and full singular series. -/
theorem singularSeries_eq_trunc_mul_tail (N : ℕ) (_hN2 : 2 ≤ N)
    (hz1 : 1 ≤ correctedChenZ N) (hzleN : correctedChenZ N ≤ N + 1) :
    SingularSeries.singularSeries N =
      SingularSeries.singularSeriesTruncated N (correctedChenZ N - 1) *
        ((Finset.Ico (correctedChenZ N) (N + 1)).filter Nat.Prime).prod
          (fun p => SingularSeries.localFactor p N) := by
  unfold SingularSeries.singularSeries SingularSeries.singularSeriesTruncated
  rw [Nat.sub_add_cancel hz1]
  have hsplit : Finset.range (N + 1) =
      Finset.range (correctedChenZ N) ∪ Finset.Ico (correctedChenZ N) (N + 1) := by
    rw [Finset.range_eq_Ico, Finset.range_eq_Ico]
    rw [← Finset.Ico_union_Ico_eq_Ico (by omega : 0 ≤ correctedChenZ N) hzleN]
  have hfilter : (Finset.range (N + 1)).filter Nat.Prime =
      (Finset.range (correctedChenZ N)).filter Nat.Prime ∪
        (Finset.Ico (correctedChenZ N) (N + 1)).filter Nat.Prime := by
    rw [← Finset.filter_union]
    exact congrArg (fun t : Finset ℕ => t.filter Nat.Prime) hsplit
  have hdisj : Disjoint ((Finset.range (correctedChenZ N)).filter Nat.Prime)
      ((Finset.Ico (correctedChenZ N) (N + 1)).filter Nat.Prime) := by
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico] at hp1 hp2
    omega
  rw [hfilter, Finset.prod_union hdisj]

end Internal


namespace Internal

/-- The same tail product has a bound tending to one: only prime divisors of
`N` enlarge it, and each such factor is at most
`1 + 1 / (correctedChenZ N - 1)`. -/
theorem chenZ_tail_prod_le_vanishing (N : ℕ)
    (hz3 : 3 ≤ correctedChenZ N) :
    ((Finset.Ico (correctedChenZ N) (N + 1)).filter Nat.Prime).prod
        (fun p => SingularSeries.localFactor p N) ≤
      (1 + 1 / ((correctedChenZ N - 1 : ℕ) : ℝ)) ^
        ((Finset.Ico (correctedChenZ N) (N + 1)).filter
          (fun p => p.Prime ∧ p ∣ N)).card := by
  let B : ℝ := 1 + 1 / ((correctedChenZ N - 1 : ℕ) : ℝ)
  have hz1 : 1 ≤ correctedChenZ N := by omega
  have hzdenpos : 0 < ((correctedChenZ N - 1 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 0 < correctedChenZ N - 1)
  have hB1 : 1 ≤ B := by
    dsimp [B]
    have h : 0 ≤ 1 / ((correctedChenZ N - 1 : ℕ) : ℝ) := by positivity
    linarith
  have hfac : ∀ p ∈ (Finset.Ico (correctedChenZ N) (N + 1)).filter Nat.Prime,
      SingularSeries.localFactor p N ≤ if p ∣ N then B else 1 := by
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hpIco, hpPrime⟩
    have hpz : correctedChenZ N ≤ p := (Finset.mem_Ico.mp hpIco).1
    have hp2 : 2 < p := by omega
    by_cases hpd : p ∣ N
    · rw [if_pos hpd, SingularSeries.localFactor_of_dvd hpPrime hp2 hpd]
      have hp1R : (1 : ℝ) < p := by exact_mod_cast (show 1 < p by omega)
      have hp1pos : 0 < (p : ℝ) - 1 := by linarith
      have hpzR : (correctedChenZ N : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpz
      have hdenle :
          ((correctedChenZ N - 1 : ℕ) : ℝ) ≤ (p : ℝ) - 1 := by
        rw [Nat.cast_sub hz1]
        simpa only [Nat.cast_one] using sub_le_sub_right hpzR 1
      have hinv : 1 / ((p : ℝ) - 1) ≤
          1 / ((correctedChenZ N - 1 : ℕ) : ℝ) :=
        one_div_le_one_div_of_le hzdenpos hdenle
      calc
        (p : ℝ) / (p - 1) = 1 + 1 / ((p : ℝ) - 1) := by
          field_simp [ne_of_gt hp1pos]
          ring
        _ ≤ B := by simpa [B] using add_le_add_left hinv 1
    · rw [if_neg hpd]
      exact (SingularSeries.localFactor_not_dvd_lt_one hpPrime hp2 hpd).le
  have hle :
      ((Finset.Ico (correctedChenZ N) (N + 1)).filter Nat.Prime).prod
          (fun p => SingularSeries.localFactor p N) ≤
        ((Finset.Ico (correctedChenZ N) (N + 1)).filter Nat.Prime).prod
          (fun p => if p ∣ N then B else 1) := by
    apply Finset.prod_le_prod
    · intro p hp
      exact (SingularSeries.localFactor_pos
        ((Finset.mem_filter.mp hp).2)).le
    · intro p hp
      exact hfac p hp
  have hite :
      ((Finset.Ico (correctedChenZ N) (N + 1)).filter Nat.Prime).prod
          (fun p => if p ∣ N then B else 1) =
        B ^ ((Finset.Ico (correctedChenZ N) (N + 1)).filter
          (fun p => p.Prime ∧ p ∣ N)).card := by
    rw [Finset.prod_ite]
    rw [Finset.prod_const, Finset.prod_const]
    rw [Finset.filter_filter, Finset.filter_filter]
    rw [one_pow, mul_one]
  simpa [B] using le_trans hle (le_of_eq hite)

end Internal


end MathlibNt.SieveTheory.SwitchingPrinciple
