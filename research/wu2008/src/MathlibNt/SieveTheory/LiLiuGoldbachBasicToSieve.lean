import MathlibNt.SieveTheory.LiLiuGoldbachOnePlusOneNineFinite

open scoped BigOperators

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

noncomputable local instance (P : Prop) : Decidable P := Classical.propDecidable P

open Finset

open MathlibNt.SieveTheory.LiLiuOnePlusOneNine

/-- The literal sieve condition used in Li--Liu: every prime divisor of `n`
which is not excluded by the modulus `M` lies at or above the real cutoff `x`.
The integer `n` is not divided by `d`; the original `n` is filtered directly. -/
def SurvivesSieve (M : ℕ) (x : ℝ) (n : ℕ) : Prop :=
  ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ n → ¬ℓ ∣ M → x ≤ (ℓ : ℝ)

/-- Pointwise membership in the literal Li--Liu fibre `H(A,M,d;x)`. -/
def literalHPoint (M d : ℕ) (x : ℝ) (n : ℕ) : Prop :=
  d ∣ n ∧ SurvivesSieve M x n

/-- Literal finite count `H(A,M,d;x)` on the original integers `n ∈ A`. -/
noncomputable def literalH (A : Finset ℕ) (M d : ℕ) (x : ℝ) : ℤ :=
  ((A.filter (literalHPoint M d x)).card : ℤ)

/-- The actual bad set `X(A,N) = #{n ∈ A : ¬Coprime n N}`. -/
noncomputable def goldbachBadCount (A : Finset ℕ) (N : ℕ) : ℤ :=
  ((A.filter fun n => ¬Nat.Coprime n N).card : ℤ)

/-- Pointwise indicator of the bad set. -/
noncomputable def goldbachBadPoint (N n : ℕ) : ℤ :=
  if Nat.Coprime n N then 0 else 1

/-- Literal `S1(A,N;u) = H(A,N,1;u)`. -/
noncomputable def goldbachS1 (A : Finset ℕ) (N : ℕ) (u : ℝ) : ℤ :=
  literalH A N 1 u

/-- The prime carrier of `S2(A,N;T)`. -/
noncomputable def goldbachS2Primes (N : ℕ) (T : ℝ) : Finset ℕ :=
  (range (N + 1)).filter fun r =>
    r.Prime ∧ Nat.Coprime r N ∧ T ≤ (r : ℝ) ∧ r ^ 2 ≤ N

/-- Literal `S2(A,N;T)`. -/
noncomputable def goldbachS2 (A : Finset ℕ) (N : ℕ) (T : ℝ) : ℤ :=
  ∑ r ∈ goldbachS2Primes N T, literalH A N r r

/-- The pair carrier of `S4(A,N;u)`. -/
noncomputable def goldbachS4Pairs (N : ℕ) (u : ℝ) : Finset (ℕ × ℕ) :=
  ((range (N + 1)).product (range (N + 1))).filter fun rs =>
    rs.1.Prime ∧ rs.2.Prime ∧ Nat.Coprime (rs.1 * rs.2) N ∧
      u ≤ (rs.1 : ℝ) ∧ rs.1 ≤ rs.2 ∧ rs.1 * rs.2 ^ 2 ≤ N

/-- Literal `S4(A,N;u)`. -/
noncomputable def goldbachS4 (A : Finset ℕ) (N : ℕ) (u : ℝ) : ℤ :=
  ∑ rs ∈ goldbachS4Pairs N u, literalH A (N * rs.1) (rs.1 * rs.2) rs.2

/-- Pointwise `S1` multiplicity at `n`. -/
noncomputable def goldbachS1Point (N : ℕ) (u : ℝ) (n : ℕ) : ℤ :=
  if literalHPoint N 1 u n then 1 else 0

/-- Pointwise `S2` multiplicity at `n`. -/
noncomputable def goldbachS2Point (N : ℕ) (T : ℝ) (n : ℕ) : ℤ :=
  (((goldbachS2Primes N T).filter fun r => literalHPoint N r r n).card : ℤ)

/-- Pointwise `S4` multiplicity at `n`. -/
noncomputable def goldbachS4Point (N : ℕ) (u : ℝ) (n : ℕ) : ℤ :=
  (((goldbachS4Pairs N u).filter fun rs =>
      literalHPoint (N * rs.1) (rs.1 * rs.2) rs.2 n).card : ℤ)

private theorem sum_indicator_eq_card_filter {α : Type*} [DecidableEq α]
    (A : Finset α) (P : α → Prop) :
    (∑ n ∈ A, if P n then (1 : ℤ) else 0) = ((A.filter P).card : ℤ) := by
  classical
  exact Finset.sum_boole P A

theorem literalH_eq_sum_indicator
    (A : Finset ℕ) (M d : ℕ) (x : ℝ) :
    literalH A M d x =
      ∑ n ∈ A, if literalHPoint M d x n then (1 : ℤ) else 0 := by
  rw [literalH, sum_indicator_eq_card_filter]

theorem goldbachBadCount_eq_sum_indicator
    (A : Finset ℕ) (N : ℕ) :
    goldbachBadCount A N = ∑ n ∈ A, goldbachBadPoint N n := by
  classical
  unfold goldbachBadCount
  rw [← Finset.sum_boole (fun n => ¬Nat.Coprime n N) A]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases h : Nat.Coprime n N <;> simp [goldbachBadPoint, h]

theorem goldbachS1_eq_sum_point
    (A : Finset ℕ) (N : ℕ) (u : ℝ) :
    goldbachS1 A N u = ∑ n ∈ A, goldbachS1Point N u n := by
  simp [goldbachS1, goldbachS1Point, literalH_eq_sum_indicator]

theorem survivesSieve_mono {M n : ℕ} {x y : ℝ}
    (hxy : x ≤ y) :
    SurvivesSieve M y n → SurvivesSieve M x n := by
  intro h ℓ hℓPrime hℓn hℓM
  exact hxy.trans (h ℓ hℓPrime hℓn hℓM)

theorem leastPrimeFactorAtLeast_mono {m n k : ℕ}
    (hmn : m ≤ n) :
    LeastPrimeFactorAtLeast n k → LeastPrimeFactorAtLeast m k := by
  intro h ℓ hℓPrime hℓn
  exact hmn.trans (h ℓ hℓPrime hℓn)

theorem goldbachBasicWeight_nonneg_of_le {zAlpha zTau n : ℕ}
    (hz : zAlpha ≤ zTau) :
    0 ≤ goldbachBasicWeight zAlpha zTau n := by
  classical
  by_cases h3 : OmegaAtLeast 3 n
  · have h2 : OmegaAtLeast 2 n := by
      unfold OmegaAtLeast at *
      omega
    have hLeast : LeastPrimeFactorAtLeast zTau n → LeastPrimeFactorAtLeast zAlpha n :=
      leastPrimeFactorAtLeast_mono hz
    by_cases hτ : LeastPrimeFactorAtLeast zTau n
    · simp [goldbachBasicWeight, h3, h2, hτ, hLeast hτ]
    · by_cases hα : LeastPrimeFactorAtLeast zAlpha n
      · simp [goldbachBasicWeight, h3, h2, hτ, hα]
      · simp [goldbachBasicWeight, h3, h2, hτ, hα]
  · by_cases h2 : OmegaAtLeast 2 n
    · have hLeast : LeastPrimeFactorAtLeast zTau n → LeastPrimeFactorAtLeast zAlpha n :=
        leastPrimeFactorAtLeast_mono hz
      by_cases hτ : LeastPrimeFactorAtLeast zTau n
      · simp [goldbachBasicWeight, h3, h2, hτ, hLeast hτ]
      · by_cases hα : LeastPrimeFactorAtLeast zAlpha n
        · simp [goldbachBasicWeight, h3, h2, hτ, hα]
        · simp [goldbachBasicWeight, h3, h2, hτ, hα]
    · by_cases hα : LeastPrimeFactorAtLeast zAlpha n
      · simp [goldbachBasicWeight, h3, h2, hα]
      · simp [goldbachBasicWeight, h3, h2, hα]

theorem prime_not_dvd_of_coprime {n M ℓ : ℕ}
    (hcop : Nat.Coprime n M) (hℓPrime : ℓ.Prime) (hℓn : ℓ ∣ n) :
    ¬ℓ ∣ M := by
  exact hℓPrime.coprime_iff_not_dvd.mp (hcop.coprime_dvd_left hℓn)

theorem survivesSieve_iff_leastPrimeFactorAtLeast_of_coprime
    {M n : ℕ} {u : ℝ} (hcop : Nat.Coprime n M) :
    SurvivesSieve M u n ↔ LeastPrimeFactorAtLeast ⌈u⌉₊ n := by
  constructor
  · intro h ℓ hℓPrime hℓn
    exact Nat.ceil_le.mpr (h ℓ hℓPrime hℓn (prime_not_dvd_of_coprime hcop hℓPrime hℓn))
  · intro h ℓ hℓPrime hℓn hℓM
    exact Nat.ceil_le.mp (h ℓ hℓPrime hℓn)

theorem literalHPoint_one_iff_survivesSieve
    {M n : ℕ} {u : ℝ} :
    literalHPoint M 1 u n ↔ SurvivesSieve M u n := by
  simp [literalHPoint]

theorem goldbachS1Point_eq_indicator_of_coprime
    {N n : ℕ} {u : ℝ} (hcop : Nat.Coprime n N) :
    goldbachS1Point N u n =
      if LeastPrimeFactorAtLeast ⌈u⌉₊ n then 1 else 0 := by
  by_cases hrough : SurvivesSieve N u n
  · have hrough' : LeastPrimeFactorAtLeast ⌈u⌉₊ n :=
      (survivesSieve_iff_leastPrimeFactorAtLeast_of_coprime hcop).mp hrough
    simp [goldbachS1Point, literalHPoint_one_iff_survivesSieve, hrough, hrough']
  · have hrough' : ¬LeastPrimeFactorAtLeast ⌈u⌉₊ n := by
      intro h
      exact hrough ((survivesSieve_iff_leastPrimeFactorAtLeast_of_coprime hcop).mpr h)
    simp [goldbachS1Point, literalHPoint_one_iff_survivesSieve, hrough, hrough']

theorem goldbachS1Point_le_one (N n : ℕ) (u : ℝ) :
    goldbachS1Point N u n ≤ 1 := by
  by_cases h : literalHPoint N 1 u n <;> simp [goldbachS1Point, h]

theorem goldbachS2Point_nonneg (N n : ℕ) (T : ℝ) :
    0 ≤ goldbachS2Point N T n := by
  unfold goldbachS2Point
  exact_mod_cast Nat.zero_le ((goldbachS2Primes N T).filter fun r => literalHPoint N r r n).card

theorem goldbachS4Point_nonneg (N n : ℕ) (u : ℝ) :
    0 ≤ goldbachS4Point N u n := by
  unfold goldbachS4Point
  exact_mod_cast Nat.zero_le ((goldbachS4Pairs N u).filter fun rs =>
    literalHPoint (N * rs.1) (rs.1 * rs.2) rs.2 n).card

theorem goldbachBadPoint_nonneg (N n : ℕ) :
    0 ≤ goldbachBadPoint N n := by
  unfold goldbachBadPoint
  split_ifs <;> omega

private theorem head_le_of_mem_tail :
    ∀ {a : ℕ} {l : List ℕ},
      List.IsChain (· ≤ ·) (a :: l) → ∀ {x : ℕ}, x ∈ l → a ≤ x
    := by
  intro a l hchain x hx
  exact List.IsChain.rel_cons hchain hx

private theorem head_le_of_mem {a : ℕ} {l : List ℕ}
    (hchain : List.IsChain (· ≤ ·) (a :: l)) :
    ∀ {x : ℕ}, x ∈ a :: l → a ≤ x := by
  intro x hx
  rw [List.mem_cons] at hx
  rcases hx with rfl | hx
  · exact le_rfl
  · exact head_le_of_mem_tail hchain hx

private theorem exists_first_two_prime_factors {n : ℕ}
    (h2 : OmegaAtLeast 2 n) :
    ∃ r s, ∃ rest : List ℕ,
      n.primeFactorsList = r :: s :: rest ∧ r.Prime ∧ s.Prime ∧ r ≤ s := by
  cases hpf : n.primeFactorsList with
  | nil =>
      simp [OmegaAtLeast, hpf] at h2
  | cons r tail =>
      cases tail with
      | nil =>
          simp [OmegaAtLeast, hpf] at h2
      | cons s rest =>
          have hrmem : r ∈ n.primeFactorsList := by rw [hpf]; simp
          have hsmem : s ∈ n.primeFactorsList := by rw [hpf]; simp
          have hrs : r ≤ s := by
            have hchain : List.IsChain (· ≤ ·) (r :: s :: rest) := by
              simpa [hpf] using Nat.isChain_primeFactorsList n
            have h := (List.isChain_cons.1 hchain).1
            simpa using h s (by simp)
          refine ⟨r, s, rest, ?_⟩
          exact ⟨rfl, Nat.prime_of_mem_primeFactorsList hrmem,
            Nat.prime_of_mem_primeFactorsList hsmem, hrs⟩

private theorem exists_first_three_prime_factors {n : ℕ}
    (h3 : OmegaAtLeast 3 n) :
    ∃ r s t, ∃ rest : List ℕ,
      n.primeFactorsList = r :: s :: t :: rest ∧
        r.Prime ∧ s.Prime ∧ t.Prime ∧ r ≤ s ∧ s ≤ t := by
  cases hpf : n.primeFactorsList with
  | nil =>
      simp [OmegaAtLeast, hpf] at h3
  | cons r tail =>
      cases tail with
      | nil =>
          simp [OmegaAtLeast, hpf] at h3
      | cons s tail' =>
          cases tail' with
          | nil =>
              simp [OmegaAtLeast, hpf] at h3
          | cons t rest =>
              have hrmem : r ∈ n.primeFactorsList := by rw [hpf]; simp
              have hsmem : s ∈ n.primeFactorsList := by rw [hpf]; simp
              have htmem : t ∈ n.primeFactorsList := by rw [hpf]; simp
              have hrs : r ≤ s := by
                have hchain : List.IsChain (· ≤ ·) (r :: s :: t :: rest) := by
                  simpa [hpf] using Nat.isChain_primeFactorsList n
                have h := (List.isChain_cons.1 hchain).1
                simpa using h s (by simp)
              have hst : s ≤ t := by
                have hchain : List.IsChain (· ≤ ·) (s :: t :: rest) := by
                  have h : List.IsChain (· ≤ ·) (r :: s :: t :: rest) := by
                    simpa [hpf] using Nat.isChain_primeFactorsList n
                  exact (List.isChain_cons.1 h).2
                have h := (List.isChain_cons.1 hchain).1
                simpa using h t (by simp)
              refine ⟨r, s, t, rest, ?_⟩
              exact ⟨rfl, Nat.prime_of_mem_primeFactorsList hrmem,
                Nat.prime_of_mem_primeFactorsList hsmem,
                Nat.prime_of_mem_primeFactorsList htmem, hrs, hst⟩

private theorem first_two_product_dvd {n r s : ℕ} {rest : List ℕ}
    (hn : n ≠ 0) (hpf : n.primeFactorsList = r :: s :: rest) :
    r * s ∣ n := by
  have hprod := Nat.prod_primeFactorsList hn
  rw [hpf, List.prod_cons, List.prod_cons] at hprod
  exact ⟨rest.prod, by simpa [Nat.mul_assoc] using hprod.symm⟩

private theorem first_three_product_dvd {n r s t : ℕ} {rest : List ℕ}
    (hn : n ≠ 0) (hpf : n.primeFactorsList = r :: s :: t :: rest) :
    r * s * t ∣ n := by
  have hprod := Nat.prod_primeFactorsList hn
  rw [hpf, List.prod_cons, List.prod_cons, List.prod_cons] at hprod
  exact ⟨rest.prod, by simpa [Nat.mul_assoc] using hprod.symm⟩

private theorem s2_point_at_least_one
    {N n : ℕ} {T : ℝ}
    (hn2 : 2 ≤ n) (hnN : n < N) (hcop : Nat.Coprime n N)
    (hrough : LeastPrimeFactorAtLeast ⌈T⌉₊ n) (h2 : OmegaAtLeast 2 n) :
    1 ≤ goldbachS2Point N T n := by
  rcases exists_first_two_prime_factors h2 with ⟨r, s, rest, hpf, hrPrime, hsPrime, hrs⟩
  have hchain : List.IsChain (· ≤ ·) (r :: s :: rest) := by
    simpa [hpf] using Nat.isChain_primeFactorsList n
  have hrdvd : r ∣ n := by
    exact Nat.dvd_of_mem_primeFactorsList (by rw [hpf]; simp)
  have hsdvd : s ∣ n := by
    exact Nat.dvd_of_mem_primeFactorsList (by rw [hpf]; simp)
  have hrN : r ≤ N := by
    have hrn : r ≤ n := Nat.le_of_dvd (by omega : 0 < n) hrdvd
    omega
  have hrT : T ≤ (r : ℝ) := by
    exact Nat.ceil_le.mp (hrough r hrPrime hrdvd)
  have hcopr : Nat.Coprime r N := by
    exact hrPrime.coprime_iff_not_dvd.mpr (prime_not_dvd_of_coprime hcop hrPrime hrdvd)
  have hrsqN : r ^ 2 ≤ N := by
    have hprod : r * s ∣ n := first_two_product_dvd (by omega) hpf
    have hle : r * s ≤ n := Nat.le_of_dvd (by omega) hprod
    have hrsq : r ^ 2 ≤ r * s := by
      simpa [pow_two] using Nat.mul_le_mul_left r hrs
    omega
  have hsieve : SurvivesSieve N r n := by
    intro ℓ hℓPrime hℓn hℓN
    have hmem : ℓ ∈ r :: s :: rest := by
      rw [← hpf, Nat.mem_primeFactorsList (by omega)]
      exact ⟨hℓPrime, hℓn⟩
    exact_mod_cast head_le_of_mem hchain hmem
  have hrMem : r ∈ goldbachS2Primes N T := by
    apply Finset.mem_filter.mpr
    refine ⟨?_, hrPrime, hcopr, hrT, hrsqN⟩
    exact Finset.mem_range.mpr (by omega)
  have hrPoint : literalHPoint N r r n := ⟨hrdvd, hsieve⟩
  have : r ∈ (goldbachS2Primes N T).filter (fun q => literalHPoint N q q n) := by
    simp [hrMem, hrPoint]
  have hcard :
      1 ≤ ((goldbachS2Primes N T).filter (fun q => literalHPoint N q q n)).card := by
    exact Finset.one_le_card.mpr ⟨r, this⟩
  unfold goldbachS2Point
  exact_mod_cast hcard

private theorem s4_point_at_least_one
    {N n : ℕ} {u : ℝ}
    (hn2 : 2 ≤ n) (hnN : n < N) (hcop : Nat.Coprime n N)
    (hrough : LeastPrimeFactorAtLeast ⌈u⌉₊ n) (h3 : OmegaAtLeast 3 n) :
    1 ≤ goldbachS4Point N u n := by
  rcases exists_first_three_prime_factors h3 with
    ⟨r, s, t, rest, hpf, hrPrime, hsPrime, htPrime, hrs, hst⟩
  have hchain : List.IsChain (· ≤ ·) (r :: s :: t :: rest) := by
    simpa [hpf] using Nat.isChain_primeFactorsList n
  have htail : List.IsChain (· ≤ ·) (s :: t :: rest) := by
    exact (List.isChain_cons.1 hchain).2
  have hrdvd : r ∣ n := by
    exact Nat.dvd_of_mem_primeFactorsList (by rw [hpf]; simp)
  have hsdvd : s ∣ n := by
    exact Nat.dvd_of_mem_primeFactorsList (by rw [hpf]; simp)
  have hsN : s ≤ N := by
    have hsn : s ≤ n := Nat.le_of_dvd (by omega : 0 < n) hsdvd
    omega
  have hrN : r ≤ N := by
    have hrn : r ≤ n := Nat.le_of_dvd (by omega : 0 < n) hrdvd
    omega
  have hru : u ≤ (r : ℝ) := by
    exact Nat.ceil_le.mp (hrough r hrPrime hrdvd)
  have hcoprs : Nat.Coprime (r * s) N := by
    refine Nat.coprime_mul_iff_left.mpr ?_
    constructor
    · exact hrPrime.coprime_iff_not_dvd.mpr (prime_not_dvd_of_coprime hcop hrPrime hrdvd)
    · exact hsPrime.coprime_iff_not_dvd.mpr (prime_not_dvd_of_coprime hcop hsPrime hsdvd)
  have hrsdvd : r * s ∣ n := by
    have hprod := Nat.prod_primeFactorsList (by omega : n ≠ 0)
    rw [hpf, List.prod_cons, List.prod_cons, List.prod_cons] at hprod
    exact ⟨t * rest.prod, by
      simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hprod.symm⟩
  have hrsqN : r * s ^ 2 ≤ N := by
    have hprod : r * s * t ∣ n := first_three_product_dvd (by omega) hpf
    have hle : r * s * t ≤ n := Nat.le_of_dvd (by omega) hprod
    have hrsq : r * s ^ 2 ≤ r * s * t := by
      simpa [pow_two, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
        Nat.mul_le_mul_left (r * s) hst
    omega
  have hsieve : SurvivesSieve (N * r) s n := by
    intro ℓ hℓPrime hℓn hℓNr
    have hmem : ℓ ∈ r :: s :: t :: rest := by
      rw [← hpf, Nat.mem_primeFactorsList (by omega)]
      exact ⟨hℓPrime, hℓn⟩
    have hnotr : ¬ℓ ∣ r := by
      intro hℓr
      exact hℓNr (dvd_mul_of_dvd_right hℓr N)
    have hℓne : ℓ ≠ r := by
      intro hEq
      apply hnotr
      simp [hEq]
    have hmemTail : ℓ ∈ s :: t :: rest := by
      rw [List.mem_cons] at hmem
      rcases hmem with hEq | hmemTail
      · exfalso
        exact hℓne hEq
      · exact hmemTail
    exact_mod_cast head_le_of_mem htail hmemTail
  have hrsMem : (r, s) ∈ goldbachS4Pairs N u := by
    apply Finset.mem_filter.mpr
    refine ⟨?_, hrPrime, hsPrime, hcoprs, hru, hrs, hrsqN⟩
    exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega)⟩
  have hrsPoint : literalHPoint (N * r) (r * s) s n := ⟨hrsdvd, hsieve⟩
  have : (r, s) ∈ (goldbachS4Pairs N u).filter
      (fun rs => literalHPoint (N * rs.1) (rs.1 * rs.2) rs.2 n) := by
    simp [hrsMem, hrsPoint]
  have hcard :
      1 ≤ ((goldbachS4Pairs N u).filter
        (fun rs => literalHPoint (N * rs.1) (rs.1 * rs.2) rs.2 n)).card := by
    exact Finset.one_le_card.mpr ⟨(r, s), this⟩
  unfold goldbachS4Point
  exact_mod_cast hcard

theorem goldbachBasicWeight_ge_s1_sub_s2_sub_s4_sub_bad
    {N n : ℕ} {u T : ℝ}
    (_hEven : Even N) (hn2 : 2 ≤ n) (hnN : n < N) (_hu : 2 ≤ u) (huT : u ≤ T) :
    goldbachBasicWeight ⌈u⌉₊ ⌈T⌉₊ n ≥
      goldbachS1Point N u n - goldbachS2Point N T n -
        goldbachS4Point N u n - goldbachBadPoint N n := by
  have hweightNonneg : 0 ≤ goldbachBasicWeight ⌈u⌉₊ ⌈T⌉₊ n := by
    apply goldbachBasicWeight_nonneg_of_le
    exact Nat.ceil_mono huT
  by_cases hcop : Nat.Coprime n N
  · have hs1 :
        goldbachS1Point N u n =
          if LeastPrimeFactorAtLeast ⌈u⌉₊ n then 1 else 0 :=
      goldbachS1Point_eq_indicator_of_coprime hcop
    have hbad : goldbachBadPoint N n = 0 := by simp [goldbachBadPoint, hcop]
    by_cases h3 : OmegaAtLeast 3 n
    · by_cases hrough : LeastPrimeFactorAtLeast ⌈u⌉₊ n
      · have hs4 : 1 ≤ goldbachS4Point N u n :=
          s4_point_at_least_one hn2 hnN hcop hrough h3
        have hright :
            goldbachS1Point N u n - goldbachS2Point N T n -
                goldbachS4Point N u n - goldbachBadPoint N n ≤ 0 := by
          rw [hs1, if_pos hrough, hbad]
          have hs2' := goldbachS2Point_nonneg N n T
          have hs4' : (1 : ℤ) ≤ goldbachS4Point N u n := hs4
          omega
        exact le_trans hright hweightNonneg
      · have hright :
            goldbachS1Point N u n - goldbachS2Point N T n -
                goldbachS4Point N u n - goldbachBadPoint N n ≤ 0 := by
          rw [hs1, if_neg hrough, hbad]
          have hs2' := goldbachS2Point_nonneg N n T
          have hs4' := goldbachS4Point_nonneg N n u
          omega
        exact le_trans hright hweightNonneg
    · by_cases hrough : LeastPrimeFactorAtLeast ⌈u⌉₊ n
      · by_cases hT2 : LeastPrimeFactorAtLeast ⌈T⌉₊ n ∧ OmegaAtLeast 2 n
        · have hs2 : 1 ≤ goldbachS2Point N T n :=
            s2_point_at_least_one hn2 hnN hcop hT2.1 hT2.2
          have hright :
              goldbachS1Point N u n - goldbachS2Point N T n -
                  goldbachS4Point N u n - goldbachBadPoint N n ≤ 0 := by
            rw [hs1, if_pos hrough, hbad]
            have hs2' : (1 : ℤ) ≤ goldbachS2Point N T n := hs2
            have hs4' := goldbachS4Point_nonneg N n u
            omega
          exact le_trans hright hweightNonneg
        · have hweightOne : goldbachBasicWeight ⌈u⌉₊ ⌈T⌉₊ n = 1 := by
            have h2false : ¬(LeastPrimeFactorAtLeast ⌈T⌉₊ n ∧ OmegaAtLeast 2 n) := hT2
            simp [goldbachBasicWeight, hrough, h3, h2false]
          rw [hweightOne, hs1, if_pos hrough, hbad]
          have hs2' := goldbachS2Point_nonneg N n T
          have hs4' := goldbachS4Point_nonneg N n u
          omega
      · have hright :
            goldbachS1Point N u n - goldbachS2Point N T n -
                goldbachS4Point N u n - goldbachBadPoint N n ≤ 0 := by
          rw [hs1, if_neg hrough, hbad]
          have hs2' := goldbachS2Point_nonneg N n T
          have hs4' := goldbachS4Point_nonneg N n u
          omega
        exact le_trans hright hweightNonneg
  · have hbad : goldbachBadPoint N n = 1 := by simp [goldbachBadPoint, hcop]
    have hright :
        goldbachS1Point N u n - goldbachS2Point N T n -
            goldbachS4Point N u n - goldbachBadPoint N n ≤ 0 := by
      have hs1' : goldbachS1Point N u n ≤ 1 := goldbachS1Point_le_one N n u
      have hs2' := goldbachS2Point_nonneg N n T
      have hs4' := goldbachS4Point_nonneg N n u
      rw [hbad]
      omega
    exact le_trans hright hweightNonneg

theorem goldbachS2_eq_sum_point
    (A : Finset ℕ) (N : ℕ) (T : ℝ) :
    goldbachS2 A N T = ∑ n ∈ A, goldbachS2Point N T n := by
  classical
  unfold goldbachS2
  simp_rw [literalH_eq_sum_indicator]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  rw [goldbachS2Point, sum_indicator_eq_card_filter]

theorem goldbachS4_eq_sum_point
    (A : Finset ℕ) (N : ℕ) (u : ℝ) :
    goldbachS4 A N u = ∑ n ∈ A, goldbachS4Point N u n := by
  classical
  unfold goldbachS4
  simp_rw [literalH_eq_sum_indicator]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  rw [goldbachS4Point, sum_indicator_eq_card_filter]

theorem goldbachBasicFiniteRHS_ge_S1_sub_S2_sub_S4_sub_X
    (A : Finset ℕ) {N : ℕ} {u T : ℝ}
    (hEven : Even N)
    (hA : ∀ ⦃n : ℕ⦄, n ∈ A → 2 ≤ n ∧ n < N)
    (hu : 2 ≤ u) (huT : u ≤ T) :
    goldbachBasicFiniteRHS A ⌈u⌉₊ ⌈T⌉₊ ≥
      goldbachS1 A N u - goldbachS2 A N T - goldbachS4 A N u - goldbachBadCount A N := by
  have hpoint :
      ∀ n ∈ A,
        goldbachBasicWeight ⌈u⌉₊ ⌈T⌉₊ n ≥
          goldbachS1Point N u n - goldbachS2Point N T n -
            goldbachS4Point N u n - goldbachBadPoint N n := by
    intro n hn
    exact goldbachBasicWeight_ge_s1_sub_s2_sub_s4_sub_bad hEven (hA hn).1 (hA hn).2 hu huT
  rw [← sum_goldbachBasicWeight_eq_finiteRHS]
  calc
    ∑ n ∈ A, goldbachBasicWeight ⌈u⌉₊ ⌈T⌉₊ n ≥
        ∑ n ∈ A,
          (goldbachS1Point N u n - goldbachS2Point N T n -
            goldbachS4Point N u n - goldbachBadPoint N n) := by
          exact Finset.sum_le_sum hpoint
    _ = (∑ n ∈ A, goldbachS1Point N u n) -
          (∑ n ∈ A, goldbachS2Point N T n) -
          (∑ n ∈ A, goldbachS4Point N u n) -
          (∑ n ∈ A, goldbachBadPoint N n) := by
          rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    _ = goldbachS1 A N u - goldbachS2 A N T - goldbachS4 A N u - goldbachBadCount A N := by
          simp [← goldbachS1_eq_sum_point, ← goldbachS2_eq_sum_point,
            ← goldbachS4_eq_sum_point, ← goldbachBadCount_eq_sum_indicator]

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig