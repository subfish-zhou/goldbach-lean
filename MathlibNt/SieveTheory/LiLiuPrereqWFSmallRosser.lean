import MathlibNt.SieveTheory.LiLiuPrereqWFGeometricBoxes
import MathlibNt.SieveTheory.LinearSieve

/-!
# Concrete lower and upper small-prime Rosser weights

Iwaniec, *A new form of the error term in the linear sieve* (1980), p.313,
defines the lower coefficient by the even-prefix cubic tests and the upper
coefficient by the odd-prefix tests. Here a prefix ending in `p` is the set
of prime factors at least `p`: its product times `p²` is the displayed cubic
expression. The level is real, so the cutoff at `D^ε` is strict, without rounding.

The small weight of p.316, Lemma 4, is this coefficient restricted to the
small sieve prime product. The finite cancellation argument is independent
of the density assertion in that lemma. No density or asymptotic estimate
is asserted here.
-/

namespace MathlibNt.SieveTheory.LiLiuPrereqWF.SmallRosser

open ArithmeticFunction Finset LiLiuPrereqWFAdmissibility
open scoped Classical

/-- The even-prefix test for the lower Rosser coefficient, with real level. -/
def LowerAdmissibleSet (L : ℝ) (s : Finset ℕ) : Prop :=
  ∀ p ∈ s, Even ((s.filter (fun q => p ≤ q)).card) →
    (((s.filter (fun q => p ≤ q)).prod id : ℕ) : ℝ) * (p : ℝ) ^ 2 < L

/-- The coefficient is `(-1)^ω(n)` on admissible divisors below the level
and zero elsewhere. In applications `M` is a squarefree prime product. -/
noncomputable def lowerWeight (M : ℕ) (L : ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => if n ∈ M.divisors ∧ (n : ℝ) < L ∧
      LowerAdmissibleSet L n.primeFactors then (-1 : ℝ) ^ n.primeFactors.card else 0,
    by simp⟩

@[simp]
theorem lowerWeight_apply (M n : ℕ) (L : ℝ) :
    lowerWeight M L n =
      if n ∈ M.divisors ∧ (n : ℝ) < L ∧ LowerAdmissibleSet L n.primeFactors
      then (-1 : ℝ) ^ n.primeFactors.card else 0 := rfl

/-- Exact real-level/natural-ceiling bridge, before finite certificates. -/
theorem lowerWeight_eq_producer (M : ℕ) (L : ℝ) :
    (lowerWeight M L : ℕ → ℝ) = LinearSieve.lowerRosserWeight M ⌈L⌉₊ := by
  funext n
  simp only [lowerWeight_apply, LinearSieve.lowerRosserWeight,
    LinearSieve.LowerRosserAdmissible, LinearSieve.LowerRosserAdmissibleSet,
    LowerAdmissibleSet, Nat.lt_ceil, Nat.cast_mul, Nat.cast_pow, neg_one_pow_eq_ite]

theorem lowerWeight_active {M n : ℕ} {L : ℝ} (h : lowerWeight M L n ≠ 0) :
    n ∈ M.divisors ∧ (n : ℝ) < L ∧ LowerAdmissibleSet L n.primeFactors := by
  by_contra hn
  rw [lowerWeight_apply, if_neg hn] at h
  exact h rfl

theorem lowerWeight_boundedOne (M : ℕ) (L : ℝ) : BoundedOne (lowerWeight M L) := by
  intro n
  rw [lowerWeight_apply]
  split <;> simp

theorem lowerWeight_lt_level {M n : ℕ} {L : ℝ} (h : lowerWeight M L n ≠ 0) :
    (n : ℝ) < L :=
  (lowerWeight_active h).2.1

theorem lowerWeight_eq_zero_of_level_le {M n : ℕ} {L : ℝ} (h : L ≤ (n : ℝ)) :
    lowerWeight M L n = 0 := by
  simp [lowerWeight_apply, not_lt_of_ge h]

theorem lowerWeight_supportedAt (M : ℕ) (L : ℝ) :
    SupportedAt (lowerWeight M L) L :=
  fun _ hn => (lowerWeight_lt_level hn).le

theorem lowerWeight_dvd {M n : ℕ} {L : ℝ} (h : lowerWeight M L n ≠ 0) : n ∣ M :=
  (Nat.mem_divisors.mp (lowerWeight_active h).1).1

theorem lowerWeight_squarefree {M n : ℕ} {L : ℝ}
    (hM : Squarefree M) (h : lowerWeight M L n ≠ 0) : Squarefree n :=
  Squarefree.squarefree_of_dvd (lowerWeight_dvd h) hM

@[simp]
theorem lowerWeight_one {M : ℕ} {L : ℝ} (hM : M ≠ 0) (hL : 1 < L) :
    lowerWeight M L 1 = 1 := by
  simp [lowerWeight_apply, Nat.mem_divisors, hM, hL, LowerAdmissibleSet]

theorem lowerWeight_prime {M p : ℕ} {L : ℝ}
    (hM : M ≠ 0) (hp : p.Prime) (hpd : p ∣ M) (hpL : (p : ℝ) < L) :
    lowerWeight M L p = -1 := by
  have hadm : LowerAdmissibleSet L {p} := by
    intro q hq hcard
    have hqp : q = p := Finset.mem_singleton.mp hq
    subst q
    norm_num [Finset.filter_singleton] at hcard
  simp [lowerWeight_apply, hp.primeFactors, Nat.mem_divisors, hpd, hM, hpL, hadm]

theorem lowerWeight_primeSupported (B : Finset ℕ) (L : ℝ)
    (hB : ∀ p ∈ B, p.Prime) :
    PrimeSupported B (lowerWeight (B.prod id) L) := by
  intro n hn
  have hprod : B.prod id ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun p hp => (hB p hp).ne_zero)
  have hsub := Nat.primeFactors_mono (lowerWeight_dvd hn) hprod
  simpa only [id_eq, Nat.primeFactors_prod hB] using hsub

theorem primeProduct_squarefree (B : Finset ℕ)
    (hB : ∀ p ∈ B, p.Prime) : Squarefree (B.prod id) := by
  refine Finset.squarefree_prod_of_pairwise_isCoprime
    (fun p hp q hq hpq => ?_) (fun p hp => (hB p hp).squarefree)
  exact Nat.coprime_iff_isRelPrime.mp ((Nat.coprime_primes (hB p hp) (hB q hq)).mpr hpq)

/-- The actual lower small-prime function, fixed before the box and its splits. -/
noncomputable def lowerSmallWeight (P : Finset ℕ) (D ε : ℝ) : ArithmeticFunction ℝ :=
  lowerWeight ((geometricSmallPrimes P D ε).prod id) (D ^ ε)

theorem smallPrimes_prime (P : Finset ℕ) (D ε : ℝ) :
    ∀ p ∈ geometricSmallPrimes P D ε, p.Prime :=
  fun _ hp => (Finset.mem_filter.mp hp).2.1

theorem lowerSmallWeight_boundedOne (P : Finset ℕ) (D ε : ℝ) :
    BoundedOne (lowerSmallWeight P D ε) :=
  lowerWeight_boundedOne _ _

theorem lowerSmallWeight_primeSupported (P : Finset ℕ) (D ε : ℝ) :
    PrimeSupported (geometricSmallPrimes P D ε) (lowerSmallWeight P D ε) :=
  lowerWeight_primeSupported _ _ (smallPrimes_prime P D ε)

theorem lowerSmallWeight_lt_level {P : Finset ℕ} {D ε : ℝ} {n : ℕ}
    (hn : lowerSmallWeight P D ε n ≠ 0) : (n : ℝ) < D ^ ε :=
  lowerWeight_lt_level hn

theorem lowerSmallWeight_eq_zero_of_level_le {P : Finset ℕ} {D ε : ℝ} {n : ℕ}
    (hn : D ^ ε ≤ (n : ℝ)) : lowerSmallWeight P D ε n = 0 :=
  lowerWeight_eq_zero_of_level_le hn

theorem lowerSmallWeight_supportedAt (P : Finset ℕ) (D ε : ℝ) :
    SupportedAt (lowerSmallWeight P D ε) (D ^ ε) :=
  lowerWeight_supportedAt _ _

theorem lowerSmallWeight_squarefree {P : Finset ℕ} {D ε : ℝ} {n : ℕ}
    (hn : lowerSmallWeight P D ε n ≠ 0) : Squarefree n :=
  lowerWeight_squarefree
    (primeProduct_squarefree _ (smallPrimes_prime P D ε)) hn

@[simp]
theorem lowerSmallWeight_one (P : Finset ℕ) {D ε : ℝ}
    (hD : 2 ≤ D) (hε : 0 < ε) : lowerSmallWeight P D ε 1 = 1 := by
  apply lowerWeight_one
  · exact Finset.prod_ne_zero_iff.mpr
      (fun p hp => (smallPrimes_prime P D ε p hp).ne_zero)
  · exact Real.one_lt_rpow (by linarith) hε

theorem smallPrime_lt_level (P : Finset ℕ) {D ε : ℝ}
    (hD : 1 ≤ D) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) {p : ℕ}
    (hp : p ∈ geometricSmallPrimes P D ε) : (p : ℝ) < D ^ ε := by
  apply lt_of_lt_of_le (Finset.mem_filter.mp hp).2.2
  exact Real.rpow_le_rpow_of_exponent_le hD (by nlinarith)

/-- Every small prime has coefficient `-1`; this is not a delta weight. -/
theorem lowerSmallWeight_prime (P : Finset ℕ) {D ε : ℝ}
    (hD : 1 ≤ D) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) {p : ℕ}
    (hp : p ∈ geometricSmallPrimes P D ε) : lowerSmallWeight P D ε p = -1 := by
  apply lowerWeight_prime
  · exact Finset.prod_ne_zero_iff.mpr
      (fun q hq => (smallPrimes_prime P D ε q hq).ne_zero)
  · exact smallPrimes_prime P D ε p hp
  · exact Finset.dvd_prod_of_mem id hp
  · exact smallPrime_lt_level P hD hε hε1 hp

/-- One concrete lower-small-weight geometric box term. -/
noncomputable def lowerBoxTerm (P : Finset ℕ) (D ε : ℝ)
    (input : List ℕ) : ArithmeticFunction ℝ :=
  geometricBoxTerm P D ε (ε ^ 9) input (lowerSmallWeight P D ε)

/-- No supplied function, support, or boundedness hypothesis remains.
The actual small weight and the box term precede all real level splits. -/
theorem iwaniec_lowerBoxTerm_wellFactorable (P : Finset ℕ)
    {upper : Bool} {D ε : ℝ} (input : List ℕ)
    (hD : 2 ≤ D) (hε : 0 < ε) (hεsmall : ε < 1 / 8)
    (hadm : Admissible upper (geometricLower D ε (ε ^ 9)) D input) :
    WellFactorable (lowerBoxTerm P D ε input) (D ^ (1 + ε + ε ^ 9)) :=
  iwaniec_boxTerm_wellFactorable P input (lowerSmallWeight P D ε)
    hD hε hεsmall hadm (lowerSmallWeight_primeSupported P D ε)
    (lowerSmallWeight_boundedOne P D ε) (lowerSmallWeight_supportedAt P D ε)

/-! ## Finite lower-sieve direction

The following least-prime pairing is a narrow real-level adaptation of the
finite argument in `LinearSieve.lean`, not an import of its analytic closure.
-/

noncomputable def setWeight (L : ℝ) (s : Finset ℕ) : ℝ :=
  if ((s.prod id : ℕ) : ℝ) < L ∧ LowerAdmissibleSet L s then
    if Even s.card then 1 else -1
  else 0

theorem admissible_insert_min_of_even
    {L : ℝ} {q : ℕ} {s : Finset ℕ} (hqs : q ∉ s)
    (hqmin : ∀ p ∈ s, q ≤ p) (hs : LowerAdmissibleSet L s)
    (heven : Even s.card) : LowerAdmissibleSet L (insert q s) := by
  intro p hp hcard
  obtain hp_eq | hp_s := Finset.mem_insert.mp hp
  · subst p
    have hfilter : (insert q s).filter (fun r => q ≤ r) = insert q s :=
      Finset.filter_eq_self.mpr fun r hr => by
        obtain rfl | hr_s := Finset.mem_insert.mp hr
        · exact le_rfl
        · exact hqmin r hr_s
    rw [hfilter, Finset.card_insert_of_notMem hqs, Nat.even_add_one] at hcard
    exact (hcard heven).elim
  · have hpq : ¬p ≤ q := by
      rw [not_le]
      exact lt_of_le_of_ne (hqmin p hp_s) (Ne.symm fun h => hqs (h ▸ hp_s))
    have hfilter : (insert q s).filter (fun r => p ≤ r) =
        s.filter (fun r => p ≤ r) := by
      simp [Finset.filter_insert, hpq]
    rw [hfilter] at hcard ⊢
    exact hs p hp_s hcard

theorem admissible_of_insert_min
    {L : ℝ} {q : ℕ} {s : Finset ℕ} (hqs : q ∉ s)
    (hqmin : ∀ p ∈ s, q ≤ p) (hs : LowerAdmissibleSet L (insert q s)) :
    LowerAdmissibleSet L s := by
  intro p hp hcard
  have hpq : ¬p ≤ q := by
    rw [not_le]
    exact lt_of_le_of_ne (hqmin p hp) (Ne.symm fun h => hqs (h ▸ hp))
  have hfilter : (insert q s).filter (fun r => p ≤ r) =
      s.filter (fun r => p ≤ r) := by
    simp [Finset.filter_insert, hpq]
  rw [← hfilter] at hcard ⊢
  exact hs p (Finset.mem_insert_of_mem hp) hcard

theorem prod_insert_min_lt_of_even
    {L : ℝ} {q : ℕ} {s : Finset ℕ} (hqs : q ∉ s) (hqprime : q.Prime)
    (hqL : (q : ℝ) < L) (hqmin : ∀ p ∈ s, q ≤ p)
    (hs : LowerAdmissibleSet L s) (heven : Even s.card) :
    (((insert q s).prod id : ℕ) : ℝ) < L := by
  by_cases hs0 : s = ∅
  · subst s
    simpa using hqL
  · have hsne : s.Nonempty := Finset.nonempty_iff_ne_empty.mpr hs0
    let p := s.min' hsne
    have hp : p ∈ s := Finset.min'_mem s hsne
    have hpmin : ∀ r ∈ s, p ≤ r := fun r hr => Finset.min'_le s r hr
    have hfilter : s.filter (fun r => p ≤ r) = s :=
      Finset.filter_eq_self.mpr hpmin
    have htest := hs p hp (by simpa [hfilter] using heven)
    rw [hfilter] at htest
    have hqp2 : q ≤ p ^ 2 := by
      calc
        q ≤ p := hqmin p hp
        _ ≤ p * p := Nat.le_mul_of_pos_right p
          (lt_of_lt_of_le hqprime.pos (hqmin p hp))
        _ = p ^ 2 := by ring
    have hqp2real : (q : ℝ) ≤ (p : ℝ) ^ 2 := by exact_mod_cast hqp2
    rw [Finset.prod_insert hqs, Nat.cast_mul]
    exact lt_of_le_of_lt (by
      simpa [mul_comm] using
        mul_le_mul_of_nonneg_right hqp2real (Nat.cast_nonneg (s.prod id))) htest

theorem sum_powerset_insert_pairs (f : Finset ℕ → ℝ)
    {q : ℕ} {T : Finset ℕ} (hqT : q ∉ T) :
    ∑ s ∈ (insert q T).powerset, f s =
      ∑ s ∈ T.powerset, (f s + f (insert q s)) := by
  rw [Finset.sum_powerset_insert hqT, ← Finset.sum_add_distrib]

theorem sum_divisors_eq_sum_powerset {n : ℕ}
    (hn : Squarefree n) (f : ℕ → ℝ) :
    ∑ d ∈ n.divisors, f d = ∑ s ∈ n.primeFactors.powerset, f (s.prod id) := by
  simpa only [Nat.divisors_filter_squarefree_of_squarefree hn, Nat.factors_eq,
    List.toFinset_coe, Nat.toFinset_factors, Finset.prod_val] using
    (Nat.sum_divisors_filter_squarefree (f := f) hn.ne_zero)

theorem lowerWeight_prod_eq_setWeight {M : ℕ} {L : ℝ}
    (hM : Squarefree M) {s : Finset ℕ} (hsub : s ⊆ M.primeFactors) :
    lowerWeight M L (s.prod id) = setWeight L s := by
  have hprime : ∀ p ∈ s, p.Prime := fun p hp =>
    Nat.prime_of_mem_primeFactors (hsub hp)
  have hdiv : s.prod id ∈ M.divisors := by
    rw [Nat.mem_divisors]
    refine ⟨?_, hM.ne_zero⟩
    rw [← Nat.prod_primeFactors_of_squarefree hM]
    simpa only [id_eq] using
      Finset.prod_dvd_prod_of_subset s M.primeFactors id hsub
  have hpf : (s.prod id).primeFactors = s := by
    simpa only [id_eq] using Nat.primeFactors_prod hprime
  rw [lowerWeight_apply, hpf]
  simp only [hdiv, true_and, neg_one_pow_eq_ite, setWeight]

/-- Unconditional finite lower-divisor-sum inequality for the explicit
coefficient. The hypotheses concern only the squarefree sieve prime product
and the prime cutoff, not a certificate or a sieve conclusion. -/
theorem lowerWeight_divisor_sum {M n : ℕ} {L : ℝ}
    (hM : Squarefree M) (hL : ∀ p ∈ M.primeFactors, (p : ℝ) < L) (hn : n ∣ M) :
    ∑ d ∈ n.divisors, lowerWeight M L d ≤ if n = 1 then 1 else 0 := by
  simp_rw [lowerWeight_eq_producer]
  exact LinearSieve.lowerRosserWeight_divisor_sum
    (LinearSieve.lowerRosserWeight_certificate hM hM.ne_zero
      (fun p hp => Nat.lt_ceil.mpr (hL p hp))) hn

/-- The actual lower small weight satisfies the finite lower-sieve direction
on every divisor of its small prime product, in particular for `0 < ε < 1/8`. -/
theorem lowerSmallWeight_divisor_sum (P : Finset ℕ) {D ε : ℝ} {n : ℕ}
    (hD : 1 ≤ D) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hn : n ∣ (geometricSmallPrimes P D ε).prod id) :
    ∑ d ∈ n.divisors, lowerSmallWeight P D ε d ≤ if n = 1 then 1 else 0 := by
  apply lowerWeight_divisor_sum
    (primeProduct_squarefree _ (smallPrimes_prime P D ε)) _ hn
  intro p hp
  have hmem : p ∈ geometricSmallPrimes P D ε := by
    simpa only [id_eq, Nat.primeFactors_prod (smallPrimes_prime P D ε)] using hp
  exact smallPrime_lt_level P hD hε hε1 hmem

/-- The finite lower-sieve direction on all natural numbers, obtained by
restricting the divisor sum to `gcd(n,M)`. Prime powers cause no loss. -/
theorem lowerWeight_divisor_sum_le_coprime {M n : ℕ} {L : ℝ}
    (hM : Squarefree M) (hL : ∀ p ∈ M.primeFactors, (p : ℝ) < L) :
    ∑ d ∈ n.divisors, lowerWeight M L d ≤ if n.Coprime M then 1 else 0 := by
  by_cases hn : n = 0
  · subst n
    simp only [Nat.divisors_zero, Finset.sum_empty]
    split <;> norm_num
  have hg : (n.gcd M) ≠ 0 :=
    (Squarefree.squarefree_of_dvd (Nat.gcd_dvd_right n M) hM).ne_zero
  have heq : ∑ d ∈ n.divisors, lowerWeight M L d =
      ∑ d ∈ (n.gcd M).divisors, lowerWeight M L d := by
    symm
    apply Finset.sum_subset
    · intro d hd
      exact Nat.mem_divisors.mpr
        ⟨(Nat.mem_divisors.mp hd).1.trans (Nat.gcd_dvd_left n M), hn⟩
    · intro d hd hnot
      by_contra hweight
      exact hnot (Nat.mem_divisors.mpr
        ⟨Nat.dvd_gcd (Nat.mem_divisors.mp hd).1 (lowerWeight_dvd hweight), hg⟩)
  rw [heq]
  exact lowerWeight_divisor_sum hM hL (Nat.gcd_dvd_right n M)

/-- The concrete small-prime weight is a lower bound for the indicator of
integers coprime to its sieve prime product. This is finite, not a density
estimate. -/
theorem lowerSmallWeight_divisor_sum_le_coprime (P : Finset ℕ) {D ε : ℝ}
    (hD : 1 ≤ D) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (n : ℕ) :
    ∑ d ∈ n.divisors, lowerSmallWeight P D ε d ≤
      if n.Coprime ((geometricSmallPrimes P D ε).prod id) then 1 else 0 := by
  apply lowerWeight_divisor_sum_le_coprime
    (primeProduct_squarefree _ (smallPrimes_prime P D ε))
  intro p hp
  have hmem : p ∈ geometricSmallPrimes P D ε := by
    simpa only [id_eq, Nat.primeFactors_prod (smallPrimes_prime P D ε)] using hp
  exact smallPrime_lt_level P hD hε hε1 hmem

/-! ## Concrete upper small weight -/

/-- The odd-prefix cubic test for the upper Rosser coefficient. -/
def UpperAdmissibleSet (L : ℝ) (s : Finset ℕ) : Prop :=
  ∀ p ∈ s, ¬Even ((s.filter (fun q => p ≤ q)).card) →
    (((s.filter (fun q => p ≤ q)).prod id : ℕ) : ℝ) * (p : ℝ) ^ 2 < L

/-- The upper coefficient with a strict real cutoff and odd-prefix tests. -/
noncomputable def upperWeight (M : ℕ) (L : ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => if n ∈ M.divisors ∧ (n : ℝ) < L ∧
      UpperAdmissibleSet L n.primeFactors then (-1 : ℝ) ^ n.primeFactors.card else 0,
    by simp⟩

@[simp]
theorem upperWeight_apply (M n : ℕ) (L : ℝ) :
    upperWeight M L n =
      if n ∈ M.divisors ∧ (n : ℝ) < L ∧ UpperAdmissibleSet L n.primeFactors
      then (-1 : ℝ) ^ n.primeFactors.card else 0 := rfl

/-- Exact real-level/natural-ceiling bridge, before finite certificates. -/
theorem upperWeight_eq_producer (M : ℕ) (L : ℝ) :
    (upperWeight M L : ℕ → ℝ) = LinearSieve.upperRosserWeight M ⌈L⌉₊ := by
  funext n
  simp only [upperWeight_apply, LinearSieve.upperRosserWeight,
    LinearSieve.UpperRosserAdmissible, LinearSieve.UpperRosserAdmissibleSet,
    UpperAdmissibleSet, Nat.lt_ceil, Nat.cast_mul, Nat.cast_pow, neg_one_pow_eq_ite]

theorem upperWeight_active {M n : ℕ} {L : ℝ} (h : upperWeight M L n ≠ 0) :
    n ∈ M.divisors ∧ (n : ℝ) < L ∧ UpperAdmissibleSet L n.primeFactors := by
  by_contra hn
  rw [upperWeight_apply, if_neg hn] at h
  exact h rfl

theorem upperWeight_boundedOne (M : ℕ) (L : ℝ) : BoundedOne (upperWeight M L) := by
  intro n
  rw [upperWeight_apply]
  split <;> simp

theorem upperWeight_lt_level {M n : ℕ} {L : ℝ} (h : upperWeight M L n ≠ 0) :
    (n : ℝ) < L :=
  (upperWeight_active h).2.1

theorem upperWeight_eq_zero_of_level_le {M n : ℕ} {L : ℝ} (h : L ≤ (n : ℝ)) :
    upperWeight M L n = 0 := by
  simp [upperWeight_apply, not_lt_of_ge h]

theorem upperWeight_supportedAt (M : ℕ) (L : ℝ) :
    SupportedAt (upperWeight M L) L :=
  fun _ hn => (upperWeight_lt_level hn).le

theorem upperWeight_dvd {M n : ℕ} {L : ℝ} (h : upperWeight M L n ≠ 0) : n ∣ M :=
  (Nat.mem_divisors.mp (upperWeight_active h).1).1

theorem upperWeight_squarefree {M n : ℕ} {L : ℝ}
    (hM : Squarefree M) (h : upperWeight M L n ≠ 0) : Squarefree n :=
  Squarefree.squarefree_of_dvd (upperWeight_dvd h) hM

@[simp]
theorem upperWeight_one {M : ℕ} {L : ℝ} (hM : M ≠ 0) (hL : 1 < L) :
    upperWeight M L 1 = 1 := by
  simp [upperWeight_apply, Nat.mem_divisors, hM, hL, UpperAdmissibleSet]

theorem upperWeight_prime {M p : ℕ} {L : ℝ}
    (hM : M ≠ 0) (hp : p.Prime) (hpd : p ∣ M) (hpL : (p : ℝ) ^ 3 < L) :
    upperWeight M L p = -1 := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
  have hcut : (p : ℝ) < L := lt_of_le_of_lt (by nlinarith [sq_nonneg (p : ℝ)]) hpL
  have hadm : UpperAdmissibleSet L {p} := by
    intro q hq _
    have hqp : q = p := Finset.mem_singleton.mp hq
    subst q
    simpa [Finset.filter_singleton, pow_succ, mul_comm] using hpL
  simp [upperWeight_apply, hp.primeFactors, Nat.mem_divisors, hpd, hM, hcut, hadm]

theorem upperWeight_primeSupported (B : Finset ℕ) (L : ℝ)
    (hB : ∀ p ∈ B, p.Prime) :
    PrimeSupported B (upperWeight (B.prod id) L) := by
  intro n hn
  have hprod : B.prod id ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun p hp => (hB p hp).ne_zero)
  have hsub := Nat.primeFactors_mono (upperWeight_dvd hn) hprod
  simpa only [id_eq, Nat.primeFactors_prod hB] using hsub

/-- The actual upper small-prime function, fixed before the box and its splits. -/
noncomputable def upperSmallWeight (P : Finset ℕ) (D ε : ℝ) : ArithmeticFunction ℝ :=
  upperWeight ((geometricSmallPrimes P D ε).prod id) (D ^ ε)

theorem upperSmallWeight_boundedOne (P : Finset ℕ) (D ε : ℝ) :
    BoundedOne (upperSmallWeight P D ε) :=
  upperWeight_boundedOne _ _

theorem upperSmallWeight_primeSupported (P : Finset ℕ) (D ε : ℝ) :
    PrimeSupported (geometricSmallPrimes P D ε) (upperSmallWeight P D ε) :=
  upperWeight_primeSupported _ _ (smallPrimes_prime P D ε)

theorem upperSmallWeight_lt_level {P : Finset ℕ} {D ε : ℝ} {n : ℕ}
    (hn : upperSmallWeight P D ε n ≠ 0) : (n : ℝ) < D ^ ε :=
  upperWeight_lt_level hn

theorem upperSmallWeight_eq_zero_of_level_le {P : Finset ℕ} {D ε : ℝ} {n : ℕ}
    (hn : D ^ ε ≤ (n : ℝ)) : upperSmallWeight P D ε n = 0 :=
  upperWeight_eq_zero_of_level_le hn

theorem upperSmallWeight_supportedAt (P : Finset ℕ) (D ε : ℝ) :
    SupportedAt (upperSmallWeight P D ε) (D ^ ε) :=
  upperWeight_supportedAt _ _

theorem upperSmallWeight_squarefree {P : Finset ℕ} {D ε : ℝ} {n : ℕ}
    (hn : upperSmallWeight P D ε n ≠ 0) : Squarefree n :=
  upperWeight_squarefree
    (primeProduct_squarefree _ (smallPrimes_prime P D ε)) hn

@[simp]
theorem upperSmallWeight_one (P : Finset ℕ) {D ε : ℝ}
    (hD : 2 ≤ D) (hε : 0 < ε) : upperSmallWeight P D ε 1 = 1 := by
  apply upperWeight_one
  · exact Finset.prod_ne_zero_iff.mpr
      (fun p hp => (smallPrimes_prime P D ε p hp).ne_zero)
  · exact Real.one_lt_rpow (by linarith) hε

/-- Under the small-parameter hypothesis every small prime passes the upper
cubic test, so the concrete upper weight is not a delta weight. -/
theorem upperSmallWeight_prime (P : Finset ℕ) {D ε : ℝ}
    (hD : 2 ≤ D) (hε : 0 < ε) (hεsmall : ε < 1 / 8) {p : ℕ}
    (hp : p ∈ geometricSmallPrimes P D ε) : upperSmallWeight P D ε p = -1 := by
  apply upperWeight_prime
  · exact Finset.prod_ne_zero_iff.mpr
      (fun q hq => (smallPrimes_prime P D ε q hq).ne_zero)
  · exact smallPrimes_prime P D ε p hp
  · exact Finset.dvd_prod_of_mem id hp
  · have hexp : ε ^ 2 * 3 < ε := by
      nlinarith [mul_pos hε (sub_pos.mpr hεsmall)]
    calc
      (p : ℝ) ^ 3 ≤ (D ^ (ε ^ 2)) ^ 3 :=
        pow_le_pow_left₀ (Nat.cast_nonneg p) (Finset.mem_filter.mp hp).2.2.le 3
      _ = D ^ (ε ^ 2 * 3) := (Real.rpow_mul_natCast (by linarith) (ε ^ 2) 3).symm
      _ < D ^ ε := Real.rpow_lt_rpow_of_exponent_lt (by linarith) hexp

/-- One concrete upper-small-weight geometric box term. -/
noncomputable def upperBoxTerm (P : Finset ℕ) (D ε : ℝ)
    (input : List ℕ) : ArithmeticFunction ℝ :=
  geometricBoxTerm P D ε (ε ^ 9) input (upperSmallWeight P D ε)

/-- The upper small weight needs no supplied function or support certificate.
The conclusion holds for either admissible geometric-box parity. -/
theorem iwaniec_upperBoxTerm_wellFactorable (P : Finset ℕ)
    {upper : Bool} {D ε : ℝ} (input : List ℕ)
    (hD : 2 ≤ D) (hε : 0 < ε) (hεsmall : ε < 1 / 8)
    (hadm : Admissible upper (geometricLower D ε (ε ^ 9)) D input) :
    WellFactorable (upperBoxTerm P D ε input) (D ^ (1 + ε + ε ^ 9)) :=
  iwaniec_boxTerm_wellFactorable P input (upperSmallWeight P D ε)
    hD hε hεsmall hadm (upperSmallWeight_primeSupported P D ε)
    (upperSmallWeight_boundedOne P D ε) (upperSmallWeight_supportedAt P D ε)

/-! ## Finite upper-sieve direction -/

noncomputable def upperSetWeight (L : ℝ) (s : Finset ℕ) : ℝ :=
  if ((s.prod id : ℕ) : ℝ) < L ∧ UpperAdmissibleSet L s then
    if Even s.card then 1 else -1
  else 0

theorem upperAdmissible_insert_min_of_odd
    {L : ℝ} {q : ℕ} {s : Finset ℕ} (hqs : q ∉ s)
    (hqmin : ∀ p ∈ s, q ≤ p) (hs : UpperAdmissibleSet L s)
    (hodd : ¬Even s.card) : UpperAdmissibleSet L (insert q s) := by
  intro p hp hcard
  obtain hp_eq | hp_s := Finset.mem_insert.mp hp
  · subst p
    have hfilter : (insert q s).filter (fun r => q ≤ r) = insert q s :=
      Finset.filter_eq_self.mpr fun r hr => by
        obtain rfl | hr_s := Finset.mem_insert.mp hr
        · exact le_rfl
        · exact hqmin r hr_s
    rw [hfilter, Finset.card_insert_of_notMem hqs, Nat.even_add_one] at hcard
    exact (hcard hodd).elim
  · have hpq : ¬p ≤ q := by
      rw [not_le]
      exact lt_of_le_of_ne (hqmin p hp_s) (Ne.symm fun h => hqs (h ▸ hp_s))
    have hfilter : (insert q s).filter (fun r => p ≤ r) =
        s.filter (fun r => p ≤ r) := by
      simp [Finset.filter_insert, hpq]
    rw [hfilter] at hcard ⊢
    exact hs p hp_s hcard

theorem upperAdmissible_of_insert_min
    {L : ℝ} {q : ℕ} {s : Finset ℕ} (hqs : q ∉ s)
    (hqmin : ∀ p ∈ s, q ≤ p) (hs : UpperAdmissibleSet L (insert q s)) :
    UpperAdmissibleSet L s := by
  intro p hp hcard
  have hpq : ¬p ≤ q := by
    rw [not_le]
    exact lt_of_le_of_ne (hqmin p hp) (Ne.symm fun h => hqs (h ▸ hp))
  have hfilter : (insert q s).filter (fun r => p ≤ r) =
      s.filter (fun r => p ≤ r) := by
    simp [Finset.filter_insert, hpq]
  rw [← hfilter] at hcard ⊢
  exact hs p (Finset.mem_insert_of_mem hp) hcard

theorem prod_insert_min_lt_of_odd
    {L : ℝ} {q : ℕ} {s : Finset ℕ} (hqs : q ∉ s) (hqprime : q.Prime)
    (hqmin : ∀ p ∈ s, q ≤ p) (hs : UpperAdmissibleSet L s)
    (hodd : ¬Even s.card) : (((insert q s).prod id : ℕ) : ℝ) < L := by
  have hsne : s.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hs0
    simp [hs0] at hodd
  let p := s.min' hsne
  have hp : p ∈ s := Finset.min'_mem s hsne
  have hpmin : ∀ r ∈ s, p ≤ r := fun r hr => Finset.min'_le s r hr
  have hfilter : s.filter (fun r => p ≤ r) = s :=
    Finset.filter_eq_self.mpr hpmin
  have htest := hs p hp (by simpa [hfilter] using hodd)
  rw [hfilter] at htest
  have hqp2 : q ≤ p ^ 2 := by
    calc
      q ≤ p := hqmin p hp
      _ ≤ p * p := Nat.le_mul_of_pos_right p
        (lt_of_lt_of_le hqprime.pos (hqmin p hp))
      _ = p ^ 2 := by ring
  have hqp2real : (q : ℝ) ≤ (p : ℝ) ^ 2 := by exact_mod_cast hqp2
  rw [Finset.prod_insert hqs, Nat.cast_mul]
  exact lt_of_le_of_lt (by
    simpa [mul_comm] using
      mul_le_mul_of_nonneg_right hqp2real (Nat.cast_nonneg (s.prod id))) htest

private theorem upperSetWeight_pair_nonneg
    {L : ℝ} {q : ℕ} {s : Finset ℕ} (hqs : q ∉ s) (hqprime : q.Prime)
    (hqmin : ∀ p ∈ s, q ≤ p) :
    0 ≤ upperSetWeight L s + upperSetWeight L (insert q s) := by
  have hcard : (insert q s).card = s.card + 1 :=
    Finset.card_insert_of_notMem hqs
  by_cases heven : Even s.card
  · have hodd : ¬Even (insert q s).card := by
      rw [hcard, Nat.even_add_one]
      exact not_not_intro heven
    have hback :
        (((insert q s).prod id : ℕ) : ℝ) < L ∧ UpperAdmissibleSet L (insert q s) →
          ((s.prod id : ℕ) : ℝ) < L ∧ UpperAdmissibleSet L s := by
      intro hins
      refine ⟨?_, upperAdmissible_of_insert_min hqs hqmin hins.2⟩
      apply lt_of_le_of_lt _ hins.1
      exact_mod_cast (show s.prod id ≤ (insert q s).prod id by
        rw [Finset.prod_insert hqs]
        exact Nat.le_mul_of_pos_left (s.prod id) hqprime.pos)
    by_cases hbase : ((s.prod id : ℕ) : ℝ) < L ∧ UpperAdmissibleSet L s
    · unfold upperSetWeight
      rw [if_pos hbase, if_pos heven]
      split <;> norm_num
    · have hins : ¬((((insert q s).prod id : ℕ) : ℝ) < L ∧
          UpperAdmissibleSet L (insert q s)) := fun h => hbase (hback h)
      unfold upperSetWeight
      rw [if_neg hbase, if_neg hins]
      norm_num
  · have hinsEven : Even (insert q s).card := by
      rw [hcard, Nat.even_add_one]
      exact heven
    by_cases hbase : ((s.prod id : ℕ) : ℝ) < L ∧ UpperAdmissibleSet L s
    · have hins : (((insert q s).prod id : ℕ) : ℝ) < L ∧
          UpperAdmissibleSet L (insert q s) :=
        ⟨prod_insert_min_lt_of_odd hqs hqprime hqmin hbase.2 heven,
          upperAdmissible_insert_min_of_odd hqs hqmin hbase.2 heven⟩
      unfold upperSetWeight
      rw [if_pos hbase, if_pos hins, if_neg heven, if_pos hinsEven]
      norm_num
    · unfold upperSetWeight
      rw [if_neg hbase]
      split <;> norm_num

private theorem sum_upperSetWeight_nonneg
    {L : ℝ} {S : Finset ℕ} (hS : S.Nonempty)
    (hprime : ∀ p ∈ S, p.Prime) :
    0 ≤ ∑ s ∈ S.powerset, upperSetWeight L s := by
  let q := S.min' hS
  let T := S.erase q
  have hqS : q ∈ S := Finset.min'_mem S hS
  have hqT : q ∉ T := by simp [T]
  have hST : insert q T = S := Finset.insert_erase hqS
  rw [← hST, sum_powerset_insert_pairs (upperSetWeight L) hqT]
  apply Finset.sum_nonneg
  intro s hs
  have hsubT : s ⊆ T := Finset.mem_powerset.mp hs
  have hqs : q ∉ s := fun h => hqT (hsubT h)
  apply upperSetWeight_pair_nonneg hqs (hprime q hqS)
  intro p hp
  exact Finset.min'_le S p (Finset.erase_subset q S (hsubT hp))

theorem upperWeight_prod_eq_setWeight {M : ℕ} {L : ℝ}
    (hM : Squarefree M) {s : Finset ℕ} (hsub : s ⊆ M.primeFactors) :
    upperWeight M L (s.prod id) = upperSetWeight L s := by
  have hprime : ∀ p ∈ s, p.Prime := fun p hp =>
    Nat.prime_of_mem_primeFactors (hsub hp)
  have hdiv : s.prod id ∈ M.divisors := by
    rw [Nat.mem_divisors]
    refine ⟨?_, hM.ne_zero⟩
    rw [← Nat.prod_primeFactors_of_squarefree hM]
    simpa only [id_eq] using
      Finset.prod_dvd_prod_of_subset s M.primeFactors id hsub
  have hpf : (s.prod id).primeFactors = s := by
    simpa only [id_eq] using Nat.primeFactors_prod hprime
  rw [upperWeight_apply, hpf]
  simp only [hdiv, true_and, neg_one_pow_eq_ite, upperSetWeight]

/-- The finite upper-sieve direction on divisors of a squarefree sieve product.
Only `1 < L` is required: there is no prime cutoff hypothesis. -/
theorem upperWeight_divisor_sum {M n : ℕ} {L : ℝ}
    (hM : Squarefree M) (hL : 1 < L) (hn : n ∣ M) :
    (if n = 1 then 1 else 0) ≤ ∑ d ∈ n.divisors, upperWeight M L d := by
  have hnSquarefree : Squarefree n := Squarefree.squarefree_of_dvd hn hM
  by_cases hn1 : n = 1
  · subst n
    simp only [Nat.divisors_one, Finset.sum_singleton]
    exact le_of_eq (upperWeight_one hM.ne_zero hL).symm
  · rw [if_neg hn1, sum_divisors_eq_sum_powerset hnSquarefree]
    have hnFactors : n.primeFactors.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hempty
      rcases Nat.primeFactors_eq_empty.mp hempty with hn0 | hn_one
      · exact hnSquarefree.ne_zero hn0
      · exact hn1 hn_one
    have hsub : n.primeFactors ⊆ M.primeFactors := Nat.primeFactors_mono hn hM.ne_zero
    calc
      0 ≤ ∑ s ∈ n.primeFactors.powerset, upperSetWeight L s :=
        sum_upperSetWeight_nonneg hnFactors (fun p hp => Nat.prime_of_mem_primeFactors hp)
      _ = ∑ s ∈ n.primeFactors.powerset, upperWeight M L (s.prod id) := by
        apply Finset.sum_congr rfl
        intro s hs
        exact (upperWeight_prod_eq_setWeight hM
          ((Finset.mem_powerset.mp hs).trans hsub)).symm

theorem upperSmallWeight_divisor_sum_of_le_one (P : Finset ℕ) {D ε : ℝ} {n : ℕ}
    (hD : 2 ≤ D) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hn : n ∣ (geometricSmallPrimes P D ε).prod id) :
    (if n = 1 then 1 else 0) ≤ ∑ d ∈ n.divisors, upperSmallWeight P D ε d :=
by
  let B := geometricSmallPrimes P D ε
  have hB : Squarefree (B.prod id) := primeProduct_squarefree _ (smallPrimes_prime P D ε)
  have hpB : (B.prod id).primeFactors = B := by
    simpa only [id_eq] using Nat.primeFactors_prod (smallPrimes_prime P D ε)
  have hL : 1 < D ^ ε := Real.one_lt_rpow (by linarith) hε
  have hcut : ∀ p ∈ (B.prod id).primeFactors, p < ⌈D ^ ε⌉₊ := by
    intro p hp
    rw [hpB] at hp
    exact Nat.lt_ceil.mpr (smallPrime_lt_level P (by linarith) hε.le hε1 hp)
  change (if n = 1 then 1 else 0) ≤ ∑ d ∈ n.divisors, upperWeight (B.prod id) (D ^ ε) d
  simp_rw [upperWeight_eq_producer]
  exact LinearSieve.upperRosserWeight_divisor_sum
    (LinearSieve.upperRosserWeight_certificate hB hB.ne_zero
      (Nat.lt_ceil.mpr (by simpa using hL)) hcut) hn

/-- The wider legacy API is retained: ε need not be at most one. -/
theorem upperSmallWeight_divisor_sum (P : Finset ℕ) {D ε : ℝ} {n : ℕ}
    (hD : 2 ≤ D) (hε : 0 < ε)
    (hn : n ∣ (geometricSmallPrimes P D ε).prod id) :
    (if n = 1 then 1 else 0) ≤ ∑ d ∈ n.divisors, upperSmallWeight P D ε d :=
  upperWeight_divisor_sum (primeProduct_squarefree _ (smallPrimes_prime P D ε))
    (Real.one_lt_rpow (by linarith) hε) hn

/-- The finite upper-sieve direction on positive integers, including prime
powers, by restriction to `gcd(n,M)`. The exclusion of zero is essential for
the empty-divisors convention when `M = 1`. -/
theorem upperWeight_divisor_sum_ge_coprime {M n : ℕ} {L : ℝ}
    (hM : Squarefree M) (hL : 1 < L) (hn : n ≠ 0) :
    (if n.Coprime M then 1 else 0) ≤ ∑ d ∈ n.divisors, upperWeight M L d := by
  have hg : (n.gcd M) ≠ 0 :=
    (Squarefree.squarefree_of_dvd (Nat.gcd_dvd_right n M) hM).ne_zero
  have heq : ∑ d ∈ n.divisors, upperWeight M L d =
      ∑ d ∈ (n.gcd M).divisors, upperWeight M L d := by
    symm
    apply Finset.sum_subset
    · intro d hd
      exact Nat.mem_divisors.mpr
        ⟨(Nat.mem_divisors.mp hd).1.trans (Nat.gcd_dvd_left n M), hn⟩
    · intro d hd hnot
      by_contra hweight
      exact hnot (Nat.mem_divisors.mpr
        ⟨Nat.dvd_gcd (Nat.mem_divisors.mp hd).1 (upperWeight_dvd hweight), hg⟩)
  rw [heq]
  exact upperWeight_divisor_sum hM hL (Nat.gcd_dvd_right n M)

/-- The concrete small-prime upper coefficient bounds the coprimality
indicator on every positive integer; no density estimate is asserted. -/
theorem upperSmallWeight_divisor_sum_ge_coprime (P : Finset ℕ) {D ε : ℝ}
    (hD : 2 ≤ D) (hε : 0 < ε) {n : ℕ} (hn : n ≠ 0) :
    (if n.Coprime ((geometricSmallPrimes P D ε).prod id) then 1 else 0) ≤
      ∑ d ∈ n.divisors, upperSmallWeight P D ε d :=
  upperWeight_divisor_sum_ge_coprime
    (primeProduct_squarefree _ (smallPrimes_prime P D ε))
    (Real.one_lt_rpow (by linarith) hε) hn

/-- The short lower weight itself is common WF at the external level. -/
theorem lowerSmallWeight_wellFactorable (P : Finset ℕ) {D ε : ℝ}
    (hD : 2 ≤ D) (hε : 0 < ε) (hεsmall : ε < 1 / 8) :
    WellFactorable (lowerSmallWeight P D ε) (D ^ (1 + ε + ε ^ 9)) := by
  simpa only [lowerBoxTerm, geometricBoxTerm, List.toFinset_nil, boxProduct,
    Finset.prod_empty, mul_one] using
    iwaniec_lowerBoxTerm_wellFactorable P [] hD hε hεsmall
      (admissible_nil false _ _)

/-- The short upper weight itself is common WF at the external level. -/
theorem upperSmallWeight_wellFactorable (P : Finset ℕ) {D ε : ℝ}
    (hD : 2 ≤ D) (hε : 0 < ε) (hεsmall : ε < 1 / 8) :
    WellFactorable (upperSmallWeight P D ε) (D ^ (1 + ε + ε ^ 9)) := by
  simpa only [upperBoxTerm, geometricBoxTerm, List.toFinset_nil, boxProduct,
    Finset.prod_empty, mul_one] using
    iwaniec_upperBoxTerm_wellFactorable P [] hD hε hεsmall
      (admissible_nil true _ _)

end MathlibNt.SieveTheory.LiLiuPrereqWF.SmallRosser
