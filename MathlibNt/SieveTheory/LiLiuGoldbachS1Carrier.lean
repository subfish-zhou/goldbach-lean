import MathlibNt.SieveTheory.LiLiuGoldbachBasicToSieve
import MathlibNt.SieveTheory.LinearSieve
import MathlibNt.SieveTheory.BombieriVinogradov
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.ZMod.Basic

open scoped BigOperators

open Finset

open MathlibNt.SieveTheory.LiLiuOnePlusOneNine

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

noncomputable local instance instDecidableGoldbachS1Carrier (P : Prop) : Decidable P :=
  Classical.propDecidable P

/-- The literal integer endpoint attached to the strict carrier condition
`p < (1 - ε)N`. -/
noncomputable def goldbachS1Endpoint (N : ℕ) (ε : ℝ) : ℕ :=
  Nat.ceil ((1 - ε) * N) - 1

/-- The actual finite sifting-prime carrier for the literal strict cutoff
`ℓ < z`, with the exceptional primes dividing `N` removed. -/
noncomputable def goldbachS1SiftingPrimes (N : ℕ) (z : ℝ) : Finset ℕ :=
  (range (Nat.ceil z)).filter fun p => p.Prime ∧ ¬ p ∣ N

/-- The corresponding finite product `P_z`. -/
noncomputable def goldbachS1ProdPrimes (N : ℕ) (z : ℝ) : ℕ :=
  (goldbachS1SiftingPrimes N z).prod id

theorem mem_goldbachS1SiftingPrimes_iff
    {N : ℕ} {z : ℝ} {p : ℕ} :
    p ∈ goldbachS1SiftingPrimes N z ↔ p < Nat.ceil z ∧ p.Prime ∧ ¬ p ∣ N := by
  simp [goldbachS1SiftingPrimes]

theorem goldbachS1ProdPrimes_squarefree (N : ℕ) (z : ℝ) :
    Squarefree (goldbachS1ProdPrimes N z) := by
  unfold goldbachS1ProdPrimes goldbachS1SiftingPrimes
  refine Finset.squarefree_prod_of_pairwise_isCoprime ?_ ?_
  · rintro p hp q hq hpq
    have hpPrime : p.Prime := (Finset.mem_filter.mp hp).2.1
    have hqPrime : q.Prime := (Finset.mem_filter.mp hq).2.1
    exact Nat.coprime_iff_isRelPrime.mp ((Nat.coprime_primes hpPrime hqPrime).mpr hpq)
  · intro p hp
    exact ((Finset.mem_filter.mp hp).2.1).squarefree

theorem goldbachS1ProdPrimes_ne_zero (N : ℕ) (z : ℝ) :
    goldbachS1ProdPrimes N z ≠ 0 := by
  unfold goldbachS1ProdPrimes goldbachS1SiftingPrimes
  exact ne_of_gt <| Finset.prod_pos fun p hp => by
    exact (mem_goldbachS1SiftingPrimes_iff.mp hp).2.1.pos

private theorem S1Carrier_primeFactors_prod_eq_self {S : Finset ℕ}
    (hS : ∀ p ∈ S, p.Prime) : (S.prod id).primeFactors = S := by
  exact MathlibNt.SieveTheory.LiuWeight.primeFactors_prod_eq_self_paperQ hS

theorem goldbachS1ProdPrimes_primeFactors (N : ℕ) (z : ℝ) :
    (goldbachS1ProdPrimes N z).primeFactors = goldbachS1SiftingPrimes N z := by
  unfold goldbachS1ProdPrimes
  exact S1Carrier_primeFactors_prod_eq_self
    (fun p hp => (mem_goldbachS1SiftingPrimes_iff.mp hp).2.1)

theorem prime_dvd_goldbachS1ProdPrimes_iff
    {N : ℕ} {z : ℝ} {p : ℕ} (hp : p.Prime) :
    p ∣ goldbachS1ProdPrimes N z ↔ (p : ℝ) < z ∧ ¬ p ∣ N := by
  constructor
  · intro hpP
    have hmem : p ∈ (goldbachS1ProdPrimes N z).primeFactors := by
      exact (Nat.mem_primeFactors_of_ne_zero
        (goldbachS1ProdPrimes_ne_zero N z)).mpr ⟨hp, hpP⟩
    rw [goldbachS1ProdPrimes_primeFactors] at hmem
    rcases mem_goldbachS1SiftingPrimes_iff.mp hmem with ⟨hpz, _, hpN⟩
    exact ⟨Nat.lt_ceil.mp hpz, hpN⟩
  · rintro ⟨hpz, hpN⟩
    have hmem : p ∈ goldbachS1SiftingPrimes N z := by
      exact mem_goldbachS1SiftingPrimes_iff.mpr ⟨Nat.lt_ceil.mpr hpz, hp, hpN⟩
    exact Finset.dvd_prod_of_mem id hmem

theorem goldbachS1ProdPrimes_coprime_N (N : ℕ) (z : ℝ) :
    Nat.Coprime (goldbachS1ProdPrimes N z) N := by
  apply Nat.coprime_of_dvd'
  intro p hpPrime hpP hpN
  exact False.elim <| ((prime_dvd_goldbachS1ProdPrimes_iff hpPrime).mp hpP).2 hpN

theorem goldbachS1_dvd_prodPrimes_coprime_N
    {N d : ℕ} {z : ℝ} (hd : d ∣ goldbachS1ProdPrimes N z) :
    Nat.Coprime d N :=
  (goldbachS1ProdPrimes_coprime_N N z).coprime_dvd_left hd

theorem goldbachS1Endpoint_le (N : ℕ) {ε : ℝ} (hε : 0 ≤ ε) :
    goldbachS1Endpoint N ε ≤ N := by
  unfold goldbachS1Endpoint
  have hceil : Nat.ceil ((1 - ε) * N) ≤ N := by
    apply Nat.ceil_le.mpr
    have hN : (0 : ℝ) ≤ N := by positivity
    nlinarith
  omega

theorem goldbachS1Endpoint_add_one {N : ℕ} {ε : ℝ}
    (hm : 2 ≤ goldbachS1Endpoint N ε) :
    goldbachS1Endpoint N ε + 1 = Nat.ceil ((1 - ε) * N) := by
  unfold goldbachS1Endpoint at hm ⊢
  set c : ℕ := Nat.ceil ((1 - ε) * N) with hc
  have hc3 : 3 ≤ c := by
    have : 2 ≤ c - 1 := by simpa [hc] using hm
    omega
  omega

theorem mem_goldbachPrimeCarrier_iff_prime_le_goldbachS1Endpoint
    {N p : ℕ} {ε : ℝ} (hε : 0 ≤ ε) (hm : 2 ≤ goldbachS1Endpoint N ε) :
    p ∈ goldbachPrimeCarrier N ε ↔ p.Prime ∧ p ≤ goldbachS1Endpoint N ε := by
  constructor
  · intro hp
    rcases (mem_goldbachPrimeCarrier_iff (N := N) (p := p) (ε := ε) hε).mp hp with
      ⟨hpPrime, hpCut⟩
    have hpCeil : p < Nat.ceil ((1 - ε) * N) := Nat.lt_ceil.mpr hpCut
    constructor
    · exact hpPrime
    · rw [← goldbachS1Endpoint_add_one (N := N) (ε := ε) hm] at hpCeil
      exact Nat.lt_succ_iff.mp hpCeil
  · rintro ⟨hpPrime, hpLe⟩
    rw [mem_goldbachPrimeCarrier_iff (N := N) (p := p) (ε := ε) hε]
    constructor
    · exact hpPrime
    · have hpCeil : p < Nat.ceil ((1 - ε) * N) := by
        rw [← goldbachS1Endpoint_add_one (N := N) (ε := ε) hm]
        exact Nat.lt_succ_iff.mpr hpLe
      exact Nat.lt_ceil.mp hpCeil

theorem goldbachS1_coprime_prodPrimes_iff_literalHPoint
    (N : ℕ) (z : ℝ) (n : ℕ) :
    Nat.Coprime (goldbachS1ProdPrimes N z) n ↔ literalHPoint N 1 z n := by
  rw [literalHPoint_one_iff_survivesSieve]
  constructor
  · intro hcopr p hpPrime hpn hpN
    refine le_of_not_gt ?_
    intro hpz
    have hpP : p ∣ goldbachS1ProdPrimes N z :=
      (prime_dvd_goldbachS1ProdPrimes_iff hpPrime).mpr ⟨hpz, hpN⟩
    exact (prime_not_dvd_of_coprime hcopr.symm hpPrime hpn) hpP
  · intro hsieve
    apply Nat.coprime_of_dvd'
    intro p hpPrime hpP hpn
    have hpData := (prime_dvd_goldbachS1ProdPrimes_iff hpPrime).mp hpP
    exact False.elim <| (not_le_of_gt hpData.1) (hsieve p hpPrime hpn hpData.2)

theorem goldbachS1_mod_mem_unitResidues
    {N d : ℕ} {z : ℝ} (hd : d ∣ goldbachS1ProdPrimes N z) :
    N % d ∈ AnalyticNumberTheory.Sieve.unitResidues d := by
  have hd0 : d ≠ 0 := by
    intro hd0
    subst d
    have hP0 : goldbachS1ProdPrimes N z = 0 := by simpa using hd
    exact goldbachS1ProdPrimes_ne_zero N z hP0
  rw [AnalyticNumberTheory.Sieve.unitResidues]
  refine Finset.mem_filter.mpr ?_
  constructor
  · exact Finset.mem_range.mpr (Nat.mod_lt N (Nat.pos_of_ne_zero hd0))
  · exact (ZMod.coprime_mod_iff_coprime N d).2 (goldbachS1_dvd_prodPrimes_coprime_N hd).symm

/-- The actual finite `S1` sieve on the genuine difference carrier, with unit
weights, the genuine mass `Li(m)`, and the true Goldbach local density. -/
noncomputable def goldbachS1BoundingSieve
    (N : ℕ) (hEven : Even N) (ε z : ℝ) : BoundingSieve where
  support := goldbachDifferenceCarrier N ε
  weights := fun _ => 1
  weights_nonneg := by intro n; norm_num
  prodPrimes := goldbachS1ProdPrimes N z
  prodPrimes_squarefree := goldbachS1ProdPrimes_squarefree N z
  totalMass := MathlibNt.SieveTheory.BombieriVinogradov.trueLogarithmicIntegral
    (goldbachS1Endpoint N ε)
  nu := AnalyticNumberTheory.Sieve.goldbachNu
  nu_mult := AnalyticNumberTheory.Sieve.goldbachNu_isMultiplicative
  nu_pos_of_prime := by
    intro p hp hpP
    exact AnalyticNumberTheory.Sieve.goldbachNu_pos_of_prime hp
  nu_lt_one_of_prime := by
    intro p hp hpP
    have hpN : ¬ p ∣ N := (prime_dvd_goldbachS1ProdPrimes_iff hp).mp hpP |>.2
    have hp2 : 2 < p := by
      have hpne : p ≠ 2 := by
        intro hpEq
        apply hpN
        rw [hpEq]
        exact even_iff_two_dvd.mp hEven
      exact lt_of_le_of_ne hp.two_le (by simpa using hpne.symm)
    exact AnalyticNumberTheory.Sieve.goldbachNu_lt_one_of_prime hp hp2

private theorem S1Carrier_multiples_card_eq_primeCarrier_modEq
    {N d : ℕ} {ε : ℝ} (hε : 0 ≤ ε) :
    ((goldbachDifferenceCarrier N ε).filter (fun n => d ∣ n)).card =
      ((goldbachPrimeCarrier N ε).filter (fun p => p ≡ N [MOD d])).card := by
  calc
    ((goldbachDifferenceCarrier N ε).filter (fun n => d ∣ n)).card =
        ((goldbachPrimeCarrier N ε).filter (fun p => d ∣ N - p)).card := by
          unfold goldbachDifferenceCarrier
          rw [Finset.filter_image]
          apply Finset.card_image_of_injOn
          intro p hp q hq hpq
          have hp' : p ∈ goldbachPrimeCarrier N ε := (Finset.mem_filter.mp hp).1
          have hq' : q ∈ goldbachPrimeCarrier N ε := (Finset.mem_filter.mp hq).1
          have hpData := (mem_goldbachPrimeCarrier_iff
            (N := N) (p := p) (ε := ε) hε).mp hp'
          have hqData := (mem_goldbachPrimeCarrier_iff
            (N := N) (p := q) (ε := ε) hε).mp hq'
          have hpLtN : p < N := by
            have hN : (0 : ℝ) ≤ N := by positivity
            have : (p : ℝ) < N := by nlinarith
            exact_mod_cast this
          have hqLtN : q < N := by
            have hN : (0 : ℝ) ≤ N := by positivity
            have : (q : ℝ) < N := by nlinarith
            exact_mod_cast this
          change N - p = N - q at hpq
          omega
    _ = ((goldbachPrimeCarrier N ε).filter (fun p => p ≡ N [MOD d])).card := by
          apply congrArg Finset.card
          apply Finset.filter_congr
          intro p hp
          have hpData := (mem_goldbachPrimeCarrier_iff
            (N := N) (p := p) (ε := ε) hε).mp hp
          have hpLtN : p < N := by
            have hN : (0 : ℝ) ≤ N := by positivity
            have : (p : ℝ) < N := by nlinarith
            exact_mod_cast this
          exact AnalyticNumberTheory.Sieve.prime_dvd_complement_iff_modEq hpLtN

private theorem S1Carrier_primeCarrier_modEq_card_eq_primesInAP
    {N d : ℕ} {ε : ℝ} (hε : 0 ≤ ε) (hm : 2 ≤ goldbachS1Endpoint N ε) :
    ((goldbachPrimeCarrier N ε).filter (fun p => p ≡ N [MOD d])).card =
      MathlibNt.SieveTheory.BombieriVinogradov.primesInAP
        (goldbachS1Endpoint N ε) d (N % d) := by
  unfold MathlibNt.SieveTheory.BombieriVinogradov.primesInAP
  have hset :
      (goldbachPrimeCarrier N ε).filter (fun p => p ≡ N [MOD d]) =
        (range (goldbachS1Endpoint N ε + 1)).filter
          (fun p => p.Prime ∧ p ≡ N % d [MOD d]) := by
    ext p
    constructor
    · intro hp
      rcases Finset.mem_filter.mp hp with ⟨hpCarrier, hpMod⟩
      rcases (mem_goldbachPrimeCarrier_iff_prime_le_goldbachS1Endpoint
        (N := N) (p := p) (ε := ε) hε hm).mp hpCarrier with ⟨hpPrime, hpLe⟩
      refine Finset.mem_filter.mpr ?_
      refine ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hpLe), ?_⟩
      refine ⟨hpPrime, ?_⟩
      simpa [Nat.ModEq, Nat.mod_mod] using hpMod
    · intro hp
      rcases Finset.mem_filter.mp hp with ⟨hpRange, hpInner⟩
      rcases hpInner with ⟨hpPrime, hpMod⟩
      refine Finset.mem_filter.mpr ?_
      refine ⟨?_, ?_⟩
      · refine (mem_goldbachPrimeCarrier_iff_prime_le_goldbachS1Endpoint
          (N := N) (p := p) (ε := ε) hε hm).mpr ?_
        exact ⟨hpPrime, Nat.le_of_lt_succ (Finset.mem_range.mp hpRange)⟩
      · simpa [Nat.ModEq] using hpMod
  rw [hset]

theorem goldbachS1BoundingSieve_multSum_eq_primesInAP
    {N : ℕ} (hEven : Even N) {ε z : ℝ} {d : ℕ}
    (hε : 0 ≤ ε) (hm : 2 ≤ goldbachS1Endpoint N ε) :
    (goldbachS1BoundingSieve N hEven ε z).multSum d =
      (MathlibNt.SieveTheory.BombieriVinogradov.primesInAP
        (goldbachS1Endpoint N ε) d (N % d) : ℝ) := by
  unfold BoundingSieve.multSum
  change
    (∑ a ∈ goldbachDifferenceCarrier N ε, if d ∣ a then (1 : ℝ) else 0) =
      (MathlibNt.SieveTheory.BombieriVinogradov.primesInAP
        (goldbachS1Endpoint N ε) d (N % d) : ℝ)
  calc
    (∑ a ∈ goldbachDifferenceCarrier N ε, if d ∣ a then (1 : ℝ) else 0) =
        (((goldbachDifferenceCarrier N ε).filter (fun n => d ∣ n)).card : ℝ) := by
          rw [Finset.sum_boole]
    _ = (((goldbachPrimeCarrier N ε).filter (fun p => p ≡ N [MOD d])).card : ℝ) := by
          rw [S1Carrier_multiples_card_eq_primeCarrier_modEq (N := N) (d := d) (ε := ε) hε]
    _ = (MathlibNt.SieveTheory.BombieriVinogradov.primesInAP
          (goldbachS1Endpoint N ε) d (N % d) : ℝ) := by
          rw [S1Carrier_primeCarrier_modEq_card_eq_primesInAP
            (N := N) (d := d) (ε := ε) hε hm]

theorem goldbachS1BoundingSieve_siftedSum_eq
    {N : ℕ} (hEven : Even N) (ε z : ℝ) :
    (goldbachS1BoundingSieve N hEven ε z).siftedSum =
      (goldbachS1 (goldbachDifferenceCarrier N ε) N z : ℝ) := by
  let P := goldbachS1ProdPrimes N z
  calc
    (goldbachS1BoundingSieve N hEven ε z).siftedSum
        = (((goldbachDifferenceCarrier N ε).filter (fun n => Nat.Coprime P n)).card : ℝ) := by
            unfold goldbachS1BoundingSieve BoundingSieve.siftedSum
            rw [Finset.sum_boole]
    _ = (((goldbachDifferenceCarrier N ε).filter (literalHPoint N 1 z)).card : ℝ) := by
          have hset :
              (goldbachDifferenceCarrier N ε).filter (fun n => Nat.Coprime P n) =
                (goldbachDifferenceCarrier N ε).filter (literalHPoint N 1 z) := by
            ext n
            simp [P, goldbachS1_coprime_prodPrimes_iff_literalHPoint]
          rw [hset]
    _ = (goldbachS1 (goldbachDifferenceCarrier N ε) N z : ℝ) := by
          simp [goldbachS1, literalH]

theorem goldbachS1BoundingSieve_nu_eq_inv_totient
    {N : ℕ} (hEven : Even N) {ε z : ℝ} {d : ℕ}
    (hd : d ∣ goldbachS1ProdPrimes N z) :
    (goldbachS1BoundingSieve N hEven ε z).nu d =
      (1 : ℝ) / Nat.totient d := by
  have hd' : d ∣ (goldbachS1BoundingSieve N hEven ε z).prodPrimes := by
    simpa [goldbachS1BoundingSieve] using hd
  exact AnalyticNumberTheory.Sieve.goldbachNu_squarefree_eq_inv_totient
    (BoundingSieve.squarefree_of_dvd_prodPrimes
      (s := goldbachS1BoundingSieve N hEven ε z) hd')

theorem goldbachS1BoundingSieve_mainSum_eq_totientSum
    {N : ℕ} (hEven : Even N) (ε z : ℝ) (μ : ℕ → ℝ) :
    (goldbachS1BoundingSieve N hEven ε z).mainSum μ =
      ∑ d ∈ (goldbachS1ProdPrimes N z).divisors, μ d / Nat.totient d := by
  unfold BoundingSieve.mainSum
  apply Finset.sum_congr rfl
  intro d hd
  rw [goldbachS1BoundingSieve_nu_eq_inv_totient (N := N) (hEven := hEven)
    (ε := ε) (z := z) ((Nat.mem_divisors.mp hd).1)]
  ring

theorem goldbachS1BoundingSieve_rem_eq_standardPrimeAPError
    {N : ℕ} (hEven : Even N) {ε z : ℝ} (hε : 0 ≤ ε)
    (hm : 2 ≤ goldbachS1Endpoint N ε) {d : ℕ}
    (hd : d ∣ goldbachS1ProdPrimes N z) :
    (goldbachS1BoundingSieve N hEven ε z).rem d =
      MathlibNt.SieveTheory.BombieriVinogradov.standardPrimeAPError
        (goldbachS1Endpoint N ε) d (N % d) := by
  unfold BoundingSieve.rem
  rw [goldbachS1BoundingSieve_multSum_eq_primesInAP (N := N) (hEven := hEven)
    (ε := ε) (z := z) (d := d) hε hm]
  rw [goldbachS1BoundingSieve_nu_eq_inv_totient (N := N) (hEven := hEven)
    (ε := ε) (z := z) hd]
  simp [goldbachS1BoundingSieve,
    MathlibNt.SieveTheory.BombieriVinogradov.standardPrimeAPError,
    div_eq_mul_inv, mul_comm]

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig