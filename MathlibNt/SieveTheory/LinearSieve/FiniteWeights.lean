import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.AlmostPrime
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.Linarith
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiFiniteAbel
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiMainTermNormalization
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiMainRatioBound
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiPowerCoordinates

/-!
# Finite Moebius, Selberg, and lower Rosser weights

Finite lower and upper sieve inequalities, lower Rosser coefficients, and
Euler-normalized lower density recursions.
-/

namespace MathlibNt.SieveTheory.LinearSieve

open Real BoundingSieve

open scoped Classical

/-! ## 0. Finite lower-bound sieve interface -/

/-- A sequence of coefficients is lower Möbius when its divisor sums lie below
the coprimality indicator.  This is the exact finite dual of Mathlib's
`BoundingSieve.IsUpperMoebius`. -/
def IsLowerMoebius (muMinus : ℕ → ℝ) : Prop :=
  ∀ n : ℕ, ∑ d ∈ n.divisors, muMinus d ≤ if n = 1 then 1 else 0

/-- A lower Möbius sequence gives a lower bound for the sifted sum before any
asymptotic estimate is introduced. -/
theorem sum_of_lowerMoebius_le_siftedSum {S : BoundingSieve}
    (muMinus : ℕ → ℝ) (hmu : IsLowerMoebius muMinus) :
    ∑ d ∈ S.prodPrimes.divisors, muMinus d * S.multSum d ≤ S.siftedSum := by
  calc
    ∑ d ∈ S.prodPrimes.divisors, muMinus d * S.multSum d =
        ∑ n ∈ S.support, ∑ d ∈ S.prodPrimes.divisors,
          if d ∣ n then S.weights n * muMinus d else 0 := by
      symm
      rw [Finset.sum_comm]
      simp_rw [BoundingSieve.multSum, ← Finset.sum_filter, Finset.mul_sum, mul_comm]
    _ = ∑ n ∈ S.support, S.weights n *
        ∑ d ∈ (Nat.gcd S.prodPrimes n).divisors, muMinus d := by
      symm
      simp_rw [Finset.mul_sum, ← Finset.sum_filter]
      congr with n
      congr
      · rw [← Nat.divisors_filter_dvd_of_dvd S.prodPrimes_ne_zero
          (Nat.gcd_dvd_left _ _)]
        ext x
        simp +contextual [Nat.dvd_gcd_iff]
    _ ≤ S.siftedSum := by
      rw [S.siftedSum_eq_sum_support_mul_ite]
      gcongr with n
      exact hmu (Nat.gcd S.prodPrimes n)

/-- Explicit-error lower sieve inequality.  Unlike the historical pointwise
interfaces, the loss is the concrete finite quantity `errSum muMinus`. -/
theorem mainSum_sub_errSum_le_siftedSum_of_lowerMoebius {S : BoundingSieve}
    (muMinus : ℕ → ℝ) (hmu : IsLowerMoebius muMinus) :
    S.totalMass * S.mainSum muMinus - S.errSum muMinus ≤ S.siftedSum := by
  have hrem : -S.errSum muMinus ≤
      ∑ d ∈ S.prodPrimes.divisors, muMinus d * S.rem d := by
    rw [BoundingSieve.errSum, ← Finset.sum_neg_distrib]
    apply Finset.sum_le_sum
    intro d hd
    rw [← abs_mul]
    exact neg_abs_le _
  calc
    S.totalMass * S.mainSum muMinus - S.errSum muMinus ≤
        S.totalMass * S.mainSum muMinus +
          ∑ d ∈ S.prodPrimes.divisors, muMinus d * S.rem d := by
      linarith
    _ = ∑ d ∈ S.prodPrimes.divisors, muMinus d * S.multSum d := by
      rw [BoundingSieve.mainSum, Finset.mul_sum, ← Finset.sum_add_distrib]
      congr with d
      rw [BoundingSieve.rem]
      ring
    _ ≤ S.siftedSum := sum_of_lowerMoebius_le_siftedSum muMinus hmu

/-! ## 0.1. Finite upper Selberg weights -/

/-- A coefficient sequence has upper-sieve level support when it vanishes on
divisors of `P` outside the strict natural-number level `D`. -/
def HasUpperLevelSupport (P D : ℕ) (muPlus : ℕ → ℝ) : Prop :=
  ∀ d : ℕ, d ∣ P → ¬d < D → muPlus d = 0

/-- The upper Möbius condition restricted to divisors of a fixed finite prime
product.  This is the exact amount of positivity used by a finite sieve. -/
def IsUpperMoebiusOn (P : ℕ) (muPlus : ℕ → ℝ) : Prop :=
  ∀ n : ℕ, n ∣ P →
    (if n = 1 then 1 else 0) ≤ ∑ d ∈ n.divisors, muPlus d

/-- A finite upper-Möbius coefficient bounds the sifted sum from above. -/
theorem siftedSum_le_sum_of_upperMoebiusOn {S : BoundingSieve}
    (muPlus : ℕ → ℝ) (hmu : IsUpperMoebiusOn S.prodPrimes muPlus) :
    S.siftedSum ≤
      ∑ d ∈ S.prodPrimes.divisors, muPlus d * S.multSum d := by
  calc
    S.siftedSum ≤ ∑ n ∈ S.support, S.weights n *
        ∑ d ∈ (Nat.gcd S.prodPrimes n).divisors, muPlus d := by
      rw [S.siftedSum_eq_sum_support_mul_ite]
      gcongr with n
      exact hmu (Nat.gcd S.prodPrimes n) (Nat.gcd_dvd_left _ _)
    _ = ∑ n ∈ S.support, ∑ d ∈ S.prodPrimes.divisors,
        if d ∣ n then S.weights n * muPlus d else 0 := by
      simp_rw [Finset.mul_sum, ← Finset.sum_filter]
      congr with n
      congr
      · rw [← Nat.divisors_filter_dvd_of_dvd S.prodPrimes_ne_zero
          (Nat.gcd_dvd_left _ _)]
        ext x
        simp +contextual [Nat.dvd_gcd_iff]
    _ = ∑ d ∈ S.prodPrimes.divisors, muPlus d * S.multSum d := by
      rw [Finset.sum_comm]
      simp_rw [BoundingSieve.multSum, ← Finset.sum_filter, Finset.mul_sum, mul_comm]

/-- The exact finite upper-sieve remainder sum at level `D`. -/
def upperErrSum (S : BoundingSieve) (D : ℕ) (muPlus : ℕ → ℝ) : ℝ :=
  ∑ d ∈ S.prodPrimes.divisors with d < D, |muPlus d| * |S.rem d|

theorem errSum_eq_upperErrSum {S : BoundingSieve} {D : ℕ} {muPlus : ℕ → ℝ}
    (hsupp : HasUpperLevelSupport S.prodPrimes D muPlus) :
    S.errSum muPlus = upperErrSum S D muPlus := by
  rw [BoundingSieve.errSum, upperErrSum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hD : d < D
  · simp [hD]
  · have hzero : muPlus d = 0 :=
      hsupp d (Nat.mem_divisors.mp hd).1 hD
    simp [hD, hzero]

/-- Finite upper sieve inequality with no Selberg representation: an upper
Möbius certificate on divisors and level support are sufficient. -/
theorem siftedSum_le_mainSum_add_upperErrSum_of_upperMoebiusOn
  {S : BoundingSieve} (D : ℕ) (muPlus : ℕ → ℝ)
  (hmu : IsUpperMoebiusOn S.prodPrimes muPlus)
  (hsupp : HasUpperLevelSupport S.prodPrimes D muPlus) :
  S.siftedSum ≤
    S.totalMass * S.mainSum muPlus + upperErrSum S D muPlus := by
  calc
  S.siftedSum ≤
      ∑ d ∈ S.prodPrimes.divisors, muPlus d * S.multSum d :=
    siftedSum_le_sum_of_upperMoebiusOn muPlus hmu
  _ = S.totalMass * S.mainSum muPlus +
      ∑ d ∈ S.prodPrimes.divisors, muPlus d * S.rem d := by
    rw [BoundingSieve.mainSum, Finset.mul_sum, ← Finset.sum_add_distrib]
    congr with d
    rw [BoundingSieve.rem]
    ring
  _ ≤ S.totalMass * S.mainSum muPlus + S.errSum muPlus := by
    rw [BoundingSieve.errSum]
    gcongr _ + ∑ d ∈ _, ?_ with d
    rw [← abs_mul]
    exact le_abs_self (muPlus d * S.rem d)
  _ = S.totalMass * S.mainSum muPlus + upperErrSum S D muPlus := by
    rw [errSum_eq_upperErrSum hsupp]

/-- A finite Selberg upper weight records the underlying `lambda`, its
normalization, and the level support of the resulting `lambdaSquared`
coefficient. -/
structure UpperSelbergWeightsAtLevel (P D : ℕ) where
  lambda : ℕ → ℝ
  lambda_one : lambda 1 = 1
  muPlus_level_support :
    HasUpperLevelSupport P D (BoundingSieve.lambdaSquared lambda)
  muPlus_abs_le_threePow (d : ℕ) :
    |BoundingSieve.lambdaSquared lambda d| ≤ (3 : ℝ) ^ d.primeFactors.card

namespace UpperSelbergWeightsAtLevel

/-- The explicit upper coefficient generated by a finite Selberg weight. -/
def muPlus {P D : ℕ} (W : UpperSelbergWeightsAtLevel P D) : ℕ → ℝ :=
  BoundingSieve.lambdaSquared W.lambda

theorem isUpperMoebius {P D : ℕ} (W : UpperSelbergWeightsAtLevel P D) :
    BoundingSieve.IsUpperMoebius W.muPlus :=
  BoundingSieve.upperMoebius_lambdaSquared W.lambda W.lambda_one

theorem hasUpperLevelSupport {P D : ℕ} (W : UpperSelbergWeightsAtLevel P D) :
    HasUpperLevelSupport P D W.muPlus :=
  W.muPlus_level_support

end UpperSelbergWeightsAtLevel

/-- Finite upper Selberg inequality with the main sum and the exact
level-restricted remainder sum kept separate. -/
theorem siftedSum_le_mainSum_add_upperErrSum {S : BoundingSieve} {D : ℕ}
    (W : UpperSelbergWeightsAtLevel S.prodPrimes D) :
    S.siftedSum ≤
      S.totalMass * S.mainSum W.muPlus + upperErrSum S D W.muPlus := by
  rw [← errSum_eq_upperErrSum W.hasUpperLevelSupport]
  exact S.siftedSum_le_mainSum_errSum_of_upperMoebius W.muPlus W.isUpperMoebius

/-! ## 0.2. Finite lower Rosser weights -/

/-- The lower Möbius condition needed by a sieve with the *fixed* finite
product `P`.  Requiring it for all natural numbers, as `IsLowerMoebius` does,
is unnecessarily strong for a finite sieve. -/
def IsLowerMoebiusOn (P : ℕ) (muMinus : ℕ → ℝ) : Prop :=
  ∀ n : ℕ, n ∣ P →
    ∑ d ∈ n.divisors, muMinus d ≤ if n = 1 then 1 else 0

/-- The finite lower-Möbius expansion. -/
theorem sum_of_lowerMoebiusOn_le_siftedSum {S : BoundingSieve}
    (muMinus : ℕ → ℝ) (hmu : IsLowerMoebiusOn S.prodPrimes muMinus) :
    ∑ d ∈ S.prodPrimes.divisors, muMinus d * S.multSum d ≤ S.siftedSum := by
  calc
    ∑ d ∈ S.prodPrimes.divisors, muMinus d * S.multSum d =
        ∑ n ∈ S.support, ∑ d ∈ S.prodPrimes.divisors,
          if d ∣ n then S.weights n * muMinus d else 0 := by
      symm
      rw [Finset.sum_comm]
      simp_rw [BoundingSieve.multSum, ← Finset.sum_filter, Finset.mul_sum, mul_comm]
    _ = ∑ n ∈ S.support, S.weights n *
        ∑ d ∈ (Nat.gcd S.prodPrimes n).divisors, muMinus d := by
      symm
      simp_rw [Finset.mul_sum, ← Finset.sum_filter]
      congr with n
      congr
      · rw [← Nat.divisors_filter_dvd_of_dvd S.prodPrimes_ne_zero
          (Nat.gcd_dvd_left _ _)]
        ext x
        simp +contextual [Nat.dvd_gcd_iff]
    _ ≤ S.siftedSum := by
      rw [S.siftedSum_eq_sum_support_mul_ite]
      gcongr with n
      exact hmu (Nat.gcd S.prodPrimes n) (Nat.gcd_dvd_left _ _)

/-- The error sum at a natural level.  It deliberately contains only `d < D`;
this is the finite error term occurring in the lower fundamental lemma. -/
def lowerErrSum (S : BoundingSieve) (D : ℕ) (muMinus : ℕ → ℝ) : ℝ :=
  ∑ d ∈ S.prodPrimes.divisors with d < D, |muMinus d| * |S.rem d|

/-- A coefficient sequence has level support if it vanishes outside the
divisors below the level. -/
def HasLowerLevelSupport (P D : ℕ) (muMinus : ℕ → ℝ) : Prop :=
  ∀ d : ℕ, d ∣ P → ¬ d < D → muMinus d = 0

theorem errSum_eq_lowerErrSum {S : BoundingSieve} {D : ℕ} {muMinus : ℕ → ℝ}
    (hsupp : HasLowerLevelSupport S.prodPrimes D muMinus) :
    S.errSum muMinus = lowerErrSum S D muMinus := by
  rw [BoundingSieve.errSum, lowerErrSum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hD : d < D
  · simp [hD]
  · have hzero : muMinus d = 0 :=
      hsupp d (Nat.mem_divisors.mp hd).1 hD
    simp [hD, hzero]

/-- Finite lower sieve inequality with its error sum explicitly restricted to
the level. -/
theorem mainSum_sub_lowerErrSum_le_siftedSum {S : BoundingSieve}
    (D : ℕ) (muMinus : ℕ → ℝ)
    (hmu : IsLowerMoebiusOn S.prodPrimes muMinus)
    (hsupp : HasLowerLevelSupport S.prodPrimes D muMinus) :
    S.totalMass * S.mainSum muMinus - lowerErrSum S D muMinus ≤ S.siftedSum := by
  rw [← errSum_eq_lowerErrSum hsupp]
  have hrem : -S.errSum muMinus ≤
      ∑ d ∈ S.prodPrimes.divisors, muMinus d * S.rem d := by
    rw [BoundingSieve.errSum, ← Finset.sum_neg_distrib]
    apply Finset.sum_le_sum
    intro d hd
    rw [← abs_mul]
    exact neg_abs_le _
  calc
    S.totalMass * S.mainSum muMinus - S.errSum muMinus ≤
        S.totalMass * S.mainSum muMinus +
          ∑ d ∈ S.prodPrimes.divisors, muMinus d * S.rem d := by
      linarith
    _ = ∑ d ∈ S.prodPrimes.divisors, muMinus d * S.multSum d := by
      rw [BoundingSieve.mainSum, Finset.mul_sum, ← Finset.sum_add_distrib]
      congr with d
      rw [BoundingSieve.rem]
      ring
    _ ≤ S.siftedSum := sum_of_lowerMoebiusOn_le_siftedSum muMinus hmu

/-- The standard lower Rosser test on a finite set of distinct primes.  For a
prime `p` in an even position of the decreasing list, the filter is precisely
the prefix `p₁,…,p₂l`; thus its test is
`p₁⋯p₂l₋₁ * p₂l^3 < D`. -/
def LowerRosserAdmissibleSet (D : ℕ) (s : Finset ℕ) : Prop :=
  ∀ p ∈ s, Even ((s.filter (fun q => p ≤ q)).card) →
    (s.filter (fun q => p ≤ q)).prod id * p ^ 2 < D

/-- The lower Rosser test for the prime factors of a natural number. -/
def LowerRosserAdmissible (D d : ℕ) : Prop :=
  LowerRosserAdmissibleSet D d.primeFactors

noncomputable def lowerRosserSetWeight (D : ℕ) (s : Finset ℕ) : ℝ :=
  if s.prod id < D ∧ LowerRosserAdmissibleSet D s then
    if Even s.card then 1 else -1
  else 0

theorem Internal.sum_divisors_eq_sum_primeFactors_powerset {n : ℕ}
    (hn : Squarefree n) (f : ℕ → ℝ) :
    ∑ d ∈ n.divisors, f d =
      ∑ s ∈ n.primeFactors.powerset, f (s.prod id) := by
  refine Finset.sum_bij (fun d _ ↦ d.primeFactors) ?_ ?_ ?_ ?_
  · intro d hd
    rw [Finset.mem_powerset]
    exact Nat.primeFactors_mono (Nat.mem_divisors.mp hd).1 hn.ne_zero
  · intro d₁ hd₁ d₂ hd₂ heq
    have hs₁ : Squarefree d₁ :=
      Squarefree.squarefree_of_dvd (Nat.mem_divisors.mp hd₁).1 hn
    have hs₂ : Squarefree d₂ :=
      Squarefree.squarefree_of_dvd (Nat.mem_divisors.mp hd₂).1 hn
    calc
      d₁ = d₁.primeFactors.prod id := by
        simpa only [id_eq] using (Nat.prod_primeFactors_of_squarefree hs₁).symm
      _ = d₂.primeFactors.prod id := by rw [heq]
      _ = d₂ := by
        simpa only [id_eq] using Nat.prod_primeFactors_of_squarefree hs₂
  · intro s hs
    have hsub : s ⊆ n.primeFactors := Finset.mem_powerset.mp hs
    have hprime : ∀ p ∈ s, p.Prime := fun p hp ↦
      Nat.prime_of_mem_primeFactors (hsub hp)
    refine ⟨s.prod id, ?_, Nat.primeFactors_prod hprime⟩
    rw [Nat.mem_divisors]
    refine ⟨?_, hn.ne_zero⟩
    rw [← Nat.prod_primeFactors_of_squarefree hn]
    simpa only [id_eq] using
      Finset.prod_dvd_prod_of_subset s n.primeFactors id hsub
  · intro d hd
    have hsd : Squarefree d :=
      Squarefree.squarefree_of_dvd (Nat.mem_divisors.mp hd).1 hn
    congr 1
    simpa only [id_eq] using (Nat.prod_primeFactors_of_squarefree hsd).symm

private theorem lowerRosserAdmissibleSet_insert_min_of_even
    {D q : ℕ} {s : Finset ℕ} (hqs : q ∉ s)
    (hqmin : ∀ p ∈ s, q ≤ p) (hs : LowerRosserAdmissibleSet D s)
    (heven : Even s.card) :
    LowerRosserAdmissibleSet D (insert q s) := by
  intro p hp hcard
  obtain hp_eq | hp_s := Finset.mem_insert.mp hp
  · subst p
    have hfilter : (insert q s).filter (fun r ↦ q ≤ r) = insert q s :=
      Finset.filter_eq_self.mpr fun r hr ↦ by
        obtain rfl | hr_s := Finset.mem_insert.mp hr
        · exact le_rfl
        · exact hqmin r hr_s
    rw [hfilter, Finset.card_insert_of_notMem hqs, Nat.even_add_one] at hcard
    exact (hcard heven).elim
  · have hpq : ¬p ≤ q := by
      rw [not_le]
      exact lt_of_le_of_ne (hqmin p hp_s) (Ne.symm fun h ↦ hqs (h ▸ hp_s))
    have hfilter : (insert q s).filter (fun r ↦ p ≤ r) =
        s.filter (fun r ↦ p ≤ r) := by
      simp [Finset.filter_insert, hpq]
    rw [hfilter] at hcard ⊢
    exact hs p hp_s hcard

private theorem lowerRosserAdmissibleSet_of_insert_min
    {D q : ℕ} {s : Finset ℕ} (hqs : q ∉ s)
    (hqmin : ∀ p ∈ s, q ≤ p)
    (hs : LowerRosserAdmissibleSet D (insert q s)) :
    LowerRosserAdmissibleSet D s := by
  intro p hp hcard
  have hpq : ¬p ≤ q := by
    rw [not_le]
    exact lt_of_le_of_ne (hqmin p hp) (Ne.symm fun h ↦ hqs (h ▸ hp))
  have hfilter : (insert q s).filter (fun r ↦ p ≤ r) =
      s.filter (fun r ↦ p ≤ r) := by
    simp [Finset.filter_insert, hpq]
  rw [← hfilter] at hcard ⊢
  exact hs p (Finset.mem_insert_of_mem hp) hcard

private theorem prod_insert_min_lt_of_lowerRosserAdmissibleSet_even
    {D q : ℕ} {s : Finset ℕ} (hqs : q ∉ s) (hqprime : q.Prime)
    (hqD : q < D) (hqmin : ∀ p ∈ s, q ≤ p)
    (hs : LowerRosserAdmissibleSet D s) (heven : Even s.card) :
    (insert q s).prod id < D := by
  by_cases hs0 : s = ∅
  · subst s
    simpa using hqD
  · have hsne : s.Nonempty := Finset.nonempty_iff_ne_empty.mpr hs0
    let p := s.min' hsne
    have hp : p ∈ s := Finset.min'_mem s hsne
    have hpmin : ∀ r ∈ s, p ≤ r := fun r hr ↦ Finset.min'_le s r hr
    have hfilter : s.filter (fun r ↦ p ≤ r) = s :=
      Finset.filter_eq_self.mpr hpmin
    have htest := hs p hp (by simpa [hfilter] using heven)
    rw [hfilter] at htest
    have hqp2 : q ≤ p ^ 2 := by
      calc
        q ≤ p := hqmin p hp
        _ ≤ p * p := Nat.le_mul_of_pos_right p
          (lt_of_lt_of_le hqprime.pos (hqmin p hp))
        _ = p ^ 2 := by ring
    rw [Finset.prod_insert hqs]
    exact lt_of_le_of_lt (by
      simpa [mul_comm] using Nat.mul_le_mul_right (s.prod id) hqp2) htest

private theorem lowerRosserSetWeight_pair_nonpos
    {D q : ℕ} {s : Finset ℕ} (hqs : q ∉ s) (hqprime : q.Prime)
    (hqD : q < D) (hqmin : ∀ p ∈ s, q ≤ p) :
    lowerRosserSetWeight D s + lowerRosserSetWeight D (insert q s) ≤ 0 := by
  have hcard : (insert q s).card = s.card + 1 :=
    Finset.card_insert_of_notMem hqs
  by_cases heven : Even s.card
  · have hodd : ¬Even (insert q s).card := by
      rw [hcard, Nat.even_add_one]
      exact not_not_intro heven
    by_cases hbase :
        s.prod id < D ∧ LowerRosserAdmissibleSet D s
    · have hins :
          (insert q s).prod id < D ∧
            LowerRosserAdmissibleSet D (insert q s) :=
        ⟨prod_insert_min_lt_of_lowerRosserAdmissibleSet_even
            hqs hqprime hqD hqmin hbase.2 heven,
          lowerRosserAdmissibleSet_insert_min_of_even
            hqs hqmin hbase.2 heven⟩
      unfold lowerRosserSetWeight
      rw [if_pos hbase, if_pos hins, if_pos heven, if_neg hodd]
      norm_num
    · unfold lowerRosserSetWeight
      rw [if_neg hbase]
      split <;> norm_num
  · have hinsEven : Even (insert q s).card := by
      rw [hcard, Nat.even_add_one]
      exact heven
    have hback :
        (insert q s).prod id < D ∧
            LowerRosserAdmissibleSet D (insert q s) →
          s.prod id < D ∧ LowerRosserAdmissibleSet D s := by
      intro hins
      refine ⟨?_, lowerRosserAdmissibleSet_of_insert_min hqs hqmin hins.2⟩
      exact lt_of_le_of_lt (by
        rw [Finset.prod_insert hqs]
        exact Nat.le_mul_of_pos_left (s.prod id) hqprime.pos) hins.1
    by_cases hbase :
        s.prod id < D ∧ LowerRosserAdmissibleSet D s
    · unfold lowerRosserSetWeight
      rw [if_pos hbase, if_neg heven]
      split <;> norm_num
    · have hins :
          ¬((insert q s).prod id < D ∧
            LowerRosserAdmissibleSet D (insert q s)) :=
        fun h ↦ hbase (hback h)
      unfold lowerRosserSetWeight
      rw [if_neg hbase, if_neg hins]
      norm_num

private theorem sum_lowerRosserSetWeight_nonpos
    {D : ℕ} {S : Finset ℕ} (hS : S.Nonempty)
    (hprime : ∀ p ∈ S, p.Prime) (hD : ∀ p ∈ S, p < D) :
    ∑ s ∈ S.powerset, lowerRosserSetWeight D s ≤ 0 := by
  let q := S.min' hS
  let T := S.erase q
  have hqS : q ∈ S := Finset.min'_mem S hS
  have hqT : q ∉ T := by simp [T]
  have hST : insert q T = S := Finset.insert_erase hqS
  have hdis : Disjoint T.powerset (T.powerset.image (insert q)) := by
    rw [Finset.disjoint_left]
    intro s hs hsi
    have hqnot : q ∉ s :=
      fun hqs ↦ hqT (Finset.mem_powerset.mp hs hqs)
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hsi
    exact hqnot (Finset.mem_insert_self q u)
  have hinj :
      Set.InjOn (insert q) (↑T.powerset : Set (Finset ℕ)) := by
    intro s hs u hu hsu
    have hqs : q ∉ s :=
      fun h ↦ hqT (Finset.mem_powerset.mp hs h)
    have hqu : q ∉ u :=
      fun h ↦ hqT (Finset.mem_powerset.mp hu h)
    have heq := congrArg (fun v : Finset ℕ ↦ v.erase q) hsu
    simpa [Finset.erase_insert, hqs, hqu] using heq
  rw [← hST, Finset.powerset_insert, Finset.sum_union hdis,
    Finset.sum_image hinj, ← Finset.sum_add_distrib]
  apply Finset.sum_nonpos
  intro s hs
  have hsubT : s ⊆ T := Finset.mem_powerset.mp hs
  have hqs : q ∉ s := fun h ↦ hqT (hsubT h)
  apply lowerRosserSetWeight_pair_nonpos hqs (hprime q hqS) (hD q hqS)
  intro p hp
  exact Finset.min'_le S p (Finset.erase_subset q S (hsubT hp))

/-- The explicit finite lower Rosser/Jurkat coefficient.  The `d < D` clause
is part of the finite-level convention; the source admissibility test is
`LowerRosserAdmissible`. -/
noncomputable def lowerRosserWeight (P D d : ℕ) : ℝ :=
  if d ∈ P.divisors ∧ d < D ∧ LowerRosserAdmissible D d then
    if Even d.primeFactors.card then 1 else -1
  else 0

private theorem lowerRosserWeight_prod_eq_setWeight {P D : ℕ}
    (hP : Squarefree P) {s : Finset ℕ} (hsub : s ⊆ P.primeFactors) :
    lowerRosserWeight P D (s.prod id) = lowerRosserSetWeight D s := by
  have hprime : ∀ p ∈ s, p.Prime := fun p hp ↦
    Nat.prime_of_mem_primeFactors (hsub hp)
  have hdiv : s.prod id ∈ P.divisors := by
    rw [Nat.mem_divisors]
    refine ⟨?_, hP.ne_zero⟩
    rw [← Nat.prod_primeFactors_of_squarefree hP]
    simpa only [id_eq] using
      Finset.prod_dvd_prod_of_subset s P.primeFactors id hsub
  have hpf : (s.prod id).primeFactors = s := by
    simpa only [id_eq] using Nat.primeFactors_prod hprime
  unfold lowerRosserWeight lowerRosserSetWeight LowerRosserAdmissible
  rw [hpf]
  simp only [hdiv, true_and]

/-- For an active odd set, adjoining a new least prime remains active exactly
until the cubic lower-Rosser cutoff `q ^ 3 * ∏ s < D` is crossed. -/
theorem lowerRosser_insert_min_active_iff_cube_lt
    {D q : ℕ} {s : Finset ℕ} (hqs : q ∉ s) (hqprime : q.Prime)
    (hqmin : ∀ p ∈ s, q ≤ p) (hodd : ¬Even s.card)
    (hs : s.prod id < D ∧ LowerRosserAdmissibleSet D s) :
    (insert q s).prod id < D ∧
        LowerRosserAdmissibleSet D (insert q s) ↔
      s.prod id * q ^ 3 < D := by
  have hfilterq :
      (insert q s).filter (fun r ↦ q ≤ r) = insert q s :=
    Finset.filter_eq_self.mpr fun r hr ↦ by
      obtain rfl | hr_s := Finset.mem_insert.mp hr
      · exact le_rfl
      · exact hqmin r hr_s
  have hinsEven : Even (insert q s).card := by
    rw [Finset.card_insert_of_notMem hqs, Nat.even_add_one]
    exact hodd
  constructor
  · intro hins
    have htest := hins.2 q (Finset.mem_insert_self q s) (by
      simpa [hfilterq] using hinsEven)
    rw [hfilterq, Finset.prod_insert hqs] at htest
    simpa only [id_eq, pow_succ, mul_assoc, mul_comm, mul_left_comm] using htest
  · intro hcube
    constructor
    · rw [Finset.prod_insert hqs]
      have hqle : q ≤ q ^ 3 := by
        exact Nat.le_pow (by norm_num)
      exact lt_of_le_of_lt
        (by simpa [mul_comm] using Nat.mul_le_mul_left (s.prod id) hqle)
        (by simpa [mul_comm] using hcube)
    · intro p hp hcard
      obtain rfl | hp_s := Finset.mem_insert.mp hp
      · rw [hfilterq, Finset.prod_insert hqs]
        simpa [pow_succ, mul_assoc, mul_comm, mul_left_comm] using hcube
      · have hpq : ¬p ≤ q := by
          rw [not_le]
          exact lt_of_le_of_ne (hqmin p hp_s)
            (Ne.symm fun h ↦ hqs (h ▸ hp_s))
        have hfilter :
            (insert q s).filter (fun r ↦ p ≤ r) =
              s.filter (fun r ↦ p ≤ r) := by
          simp [Finset.filter_insert, hpq]
        rw [hfilter] at hcard ⊢
        exact hs.2 p hp_s hcard

/-- The odd lower-Rosser boundary exposed when a new least prime is inserted. -/
def LowerRosserBoundarySet (D q : ℕ) (s : Finset ℕ) : Prop :=
  ¬Even s.card ∧
    s.prod id < D ∧ LowerRosserAdmissibleSet D s ∧
    ¬((insert q s).prod id < D ∧
      LowerRosserAdmissibleSet D (insert q s))

/-- The abstract odd lower-Rosser boundary is exactly the cubic shell
`D ≤ q ^ 3 * ∏ s` once `q` is the new least prime. -/
theorem lowerRosserBoundarySet_iff_cube_le
    {D q : ℕ} {s : Finset ℕ} (hqs : q ∉ s) (hqprime : q.Prime)
    (hqmin : ∀ p ∈ s, q ≤ p) :
    LowerRosserBoundarySet D q s ↔
      ¬Even s.card ∧
        s.prod id < D ∧ LowerRosserAdmissibleSet D s ∧
        D ≤ s.prod id * q ^ 3 := by
  constructor
  · rintro ⟨hodd, hsD, hsAdmissible, hins⟩
    refine ⟨hodd, hsD, hsAdmissible, ?_⟩
    rw [← not_lt]
    exact fun hcube ↦ hins
      ((lowerRosser_insert_min_active_iff_cube_lt hqs hqprime hqmin hodd
        ⟨hsD, hsAdmissible⟩).mpr hcube)
  · rintro ⟨hodd, hsD, hsAdmissible, hcube⟩
    refine ⟨hodd, hsD, hsAdmissible, ?_⟩
    intro hins
    have hlt :=
      (lowerRosser_insert_min_active_iff_cube_lt hqs hqprime hqmin hodd
        ⟨hsD, hsAdmissible⟩).mp hins
    omega

/-- Exact lower-Rosser one-prime pairing on an active odd tail.  The ordinary
Euler factor survives away from the cubic shell, while crossing the shell
contributes one negative boundary term. -/
theorem lowerRosserSetWeight_insert_min_pair
    (nu : ℕ → ℝ) {D q : ℕ} {s : Finset ℕ}
    (hqs : q ∉ s) (hqprime : q.Prime) (hqmin : ∀ p ∈ s, q ≤ p)
    (hodd : ¬Even s.card)
    (hs : s.prod id < D ∧ LowerRosserAdmissibleSet D s) :
    lowerRosserSetWeight D s +
        nu q * lowerRosserSetWeight D (insert q s) =
      (1 - nu q) * lowerRosserSetWeight D s -
        if LowerRosserBoundarySet D q s then nu q else 0 := by
  have hactive := lowerRosser_insert_min_active_iff_cube_lt
    hqs hqprime hqmin hodd hs
  have hinseven : Even (insert q s).card := by
    rw [Finset.card_insert_of_notMem hqs, Nat.even_add_one]
    exact hodd
  by_cases hcube : s.prod id * q ^ 3 < D
  · have hins := hactive.mpr hcube
    have hboundary : ¬LowerRosserBoundarySet D q s := by
      intro hb
      exact hb.2.2.2 hins
    have hsprod : ∏ x ∈ s, x < D := by simpa using hs.1
    have hinsprod : ∏ x ∈ insert q s, x < D := by simpa using hins.1
    simp [lowerRosserSetWeight, hsprod, hs.2, hinsprod, hodd, hinseven,
      hins.2, hboundary]
    ring
  · have hins : ¬((insert q s).prod id < D ∧
        LowerRosserAdmissibleSet D (insert q s)) := by
      exact fun ha ↦ hcube (hactive.mp ha)
    have hboundary : LowerRosserBoundarySet D q s :=
      ⟨hodd, hs.1, hs.2, hins⟩
    have hsprod : ∏ x ∈ s, x < D := by simpa using hs.1
    have hins' : ¬((∏ x ∈ insert q s, x) < D ∧
        LowerRosserAdmissibleSet D (insert q s)) := by simpa using hins
    simp [lowerRosserSetWeight, hsprod, hs.2, hodd, hins', hboundary]

/-- The finite lower Rosser density sum over subsets of a prescribed prime set.
This is the lower-sieve counterpart of `upperRosserSetDensitySum`. -/
noncomputable def lowerRosserSetDensitySum
    (nu : ℕ → ℝ) (D : ℕ) (P : Finset ℕ) : ℝ :=
  ∑ s ∈ P.powerset, lowerRosserSetWeight D s * ∏ p ∈ s, nu p

/-- Exact one-prime pairing, including inactive and even tails. -/
theorem lowerRosserSetWeight_insert_min_pair_all
    (nu : ℕ → ℝ) {D q : ℕ} {s : Finset ℕ}
    (hqs : q ∉ s) (hqprime : q.Prime) (hqD : q < D)
    (hqmin : ∀ p ∈ s, q ≤ p) :
    lowerRosserSetWeight D s +
        nu q * lowerRosserSetWeight D (insert q s) =
      (1 - nu q) * lowerRosserSetWeight D s -
        if LowerRosserBoundarySet D q s then nu q else 0 := by
  by_cases hactive : s.prod id < D ∧ LowerRosserAdmissibleSet D s
  · by_cases heven : Even s.card
    · have hins : (insert q s).prod id < D ∧
          LowerRosserAdmissibleSet D (insert q s) :=
        ⟨prod_insert_min_lt_of_lowerRosserAdmissibleSet_even
            hqs hqprime hqD hqmin hactive.2 heven,
          lowerRosserAdmissibleSet_insert_min_of_even
            hqs hqmin hactive.2 heven⟩
      have hodd : ¬Even (insert q s).card := by
        rw [Finset.card_insert_of_notMem hqs, Nat.even_add_one]
        exact not_not_intro heven
      have hboundary : ¬LowerRosserBoundarySet D q s :=
        fun hb ↦ hb.1 heven
      have hsprod : ∏ x ∈ s, x < D := by simpa using hactive.1
      have hinsprod : ∏ x ∈ insert q s, x < D := by simpa using hins.1
      simp [lowerRosserSetWeight, hsprod, hinsprod, hactive.2, hins.2,
        heven, hodd, hboundary]
      ring
    · exact lowerRosserSetWeight_insert_min_pair
        nu hqs hqprime hqmin heven hactive
  · have hins : ¬((insert q s).prod id < D ∧
          LowerRosserAdmissibleSet D (insert q s)) := by
      intro ha
      apply hactive
      refine ⟨?_, lowerRosserAdmissibleSet_of_insert_min hqs hqmin ha.2⟩
      exact lt_of_le_of_lt (by
        rw [Finset.prod_insert hqs]
        exact Nat.le_mul_of_pos_left (s.prod id) hqprime.pos) ha.1
    have hboundary : ¬LowerRosserBoundarySet D q s :=
      fun hb ↦ hactive ⟨hb.2.1, hb.2.2.1⟩
    have hactive' : ¬((∏ x ∈ s, x) < D ∧
        LowerRosserAdmissibleSet D s) := by simpa using hactive
    have hins' : ¬((∏ x ∈ insert q s, x) < D ∧
        LowerRosserAdmissibleSet D (insert q s)) := by simpa using hins
    simp [lowerRosserSetWeight, hactive', hins', hboundary]

/-- Adjoining a new least prime gives the exact Euler factor, minus precisely
its odd cubic-boundary contribution. -/
theorem lowerRosserSetDensitySum_insert_min
    (nu : ℕ → ℝ) {D q : ℕ} {P : Finset ℕ}
    (hqP : q ∉ P) (hqprime : q.Prime) (hqD : q < D)
    (hqmin : ∀ p ∈ P, q ≤ p) :
    lowerRosserSetDensitySum nu D (insert q P) =
      (1 - nu q) * lowerRosserSetDensitySum nu D P -
        nu q * ∑ s ∈ P.powerset.filter (LowerRosserBoundarySet D q),
          ∏ p ∈ s, nu p := by
  have hdis : Disjoint P.powerset (P.powerset.image (insert q)) := by
    rw [Finset.disjoint_left]
    intro s hs hsi
    have hqnot : q ∉ s :=
      fun h ↦ hqP (Finset.mem_powerset.mp hs h)
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hsi
    exact hqnot (Finset.mem_insert_self q u)
  have hinj : Set.InjOn (insert q) (↑P.powerset : Set (Finset ℕ)) := by
    intro s hs u hu hsu
    have hqs : q ∉ s :=
      fun h ↦ hqP (Finset.mem_powerset.mp hs h)
    have hqu : q ∉ u :=
      fun h ↦ hqP (Finset.mem_powerset.mp hu h)
    have heq := congrArg (fun v : Finset ℕ ↦ v.erase q) hsu
    simpa [Finset.erase_insert, hqs, hqu] using heq
  unfold lowerRosserSetDensitySum
  rw [Finset.powerset_insert, Finset.sum_union hdis,
    Finset.sum_image hinj, ← Finset.sum_add_distrib]
  calc
    _ = ∑ s ∈ P.powerset,
        (((1 - nu q) * lowerRosserSetWeight D s -
          if LowerRosserBoundarySet D q s then nu q else 0) *
          ∏ p ∈ s, nu p) := by
      apply Finset.sum_congr rfl
      intro s hs
      have hsub : s ⊆ P := Finset.mem_powerset.mp hs
      have hqs : q ∉ s := fun h ↦ hqP (hsub h)
      rw [Finset.prod_insert hqs]
      calc
        _ = (lowerRosserSetWeight D s +
              nu q * lowerRosserSetWeight D (insert q s)) *
              ∏ p ∈ s, nu p := by ring
        _ = _ := by
          rw [lowerRosserSetWeight_insert_min_pair_all nu hqs hqprime hqD
            (fun p hp ↦ hqmin p (hsub hp))]
    _ = (1 - nu q) *
          ∑ s ∈ P.powerset,
            lowerRosserSetWeight D s * ∏ p ∈ s, nu p -
        nu q * ∑ s ∈ P.powerset.filter (LowerRosserBoundarySet D q),
          ∏ p ∈ s, nu p := by
      rw [Finset.mul_sum]
      simp_rw [sub_mul]
      rw [Finset.sum_sub_distrib]
      congr 1
      · apply Finset.sum_congr rfl
        intro s hs
        ring
      · rw [Finset.sum_filter, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro s hs
        split <;> simp_all

/-- Euler-product-normalized form of the one-prime lower recurrence.  This is
pure finite algebra; the nonzero assumptions are kept explicit and no limiting
or contraction statement is used. -/
theorem lowerRosserSetDensityRatio_insert_min
    (nu : ℕ → ℝ) {D q : ℕ} {P : Finset ℕ} (hq : q ∉ P)
    (hqprime : q.Prime) (hqD : q < D) (hqmin : ∀ p ∈ P, q ≤ p)
    (hqFactor : 1 - nu q ≠ 0)
    (hPFactor : (∏ p ∈ P, (1 - nu p)) ≠ 0) :
    lowerRosserSetDensitySum nu D (insert q P) /
          ∏ p ∈ insert q P, (1 - nu p) =
      lowerRosserSetDensitySum nu D P / ∏ p ∈ P, (1 - nu p) -
        (nu q / (1 - nu q)) *
          ((∑ s ∈ P.powerset.filter (LowerRosserBoundarySet D q),
              ∏ p ∈ s, nu p) /
            ∏ p ∈ P, (1 - nu p)) := by
  classical
  rw [lowerRosserSetDensitySum_insert_min nu hq hqprime hqD hqmin,
    Finset.prod_insert hq]
  field_simp

/-! ## Finite Euler-normalized lower recursion

This deliberately stays at one finite recursion step.  In particular it does
not package an all-depth tail or introduce a continuous majorant. -/

/-- The lower Rosser density on the relative Euler-product scale. -/
noncomputable def lowerRosserSetRelativeDensity
    (nu : ℕ → ℝ) (D : ℕ) (P : Finset ℕ) : ℝ :=
  lowerRosserSetDensitySum nu D P / ∏ p ∈ P, (1 - nu p)

/-- The finite odd-boundary correction on the same relative Euler-product
scale as `lowerRosserSetRelativeDensity`. -/
noncomputable def lowerRosserBoundaryRelativeDensity
    (nu : ℕ → ℝ) (D q : ℕ) (P : Finset ℕ) : ℝ :=
  (∑ s ∈ P.powerset.filter (LowerRosserBoundarySet D q),
      ∏ p ∈ s, nu p) /
    ∏ p ∈ P, (1 - nu p)

/-- Exact normalized successor identity when a new least prime is adjoined.
The lower recursion subtracts, rather than adds, its odd-boundary mass. -/
theorem lowerRosserSetRelativeDensity_insert_min
    (nu : ℕ → ℝ) {D q : ℕ} {P : Finset ℕ}
    (hqP : q ∉ P) (hqprime : q.Prime) (hqD : q < D)
    (hqmin : ∀ p ∈ P, q ≤ p) (hqFactor : 1 - nu q ≠ 0)
    (hPFactor : (∏ p ∈ P, (1 - nu p)) ≠ 0) :
    lowerRosserSetRelativeDensity nu D (insert q P) =
      lowerRosserSetRelativeDensity nu D P -
        (nu q / (1 - nu q)) *
          lowerRosserBoundaryRelativeDensity nu D q P := by
  rw [lowerRosserSetRelativeDensity, lowerRosserSetRelativeDensity,
    lowerRosserBoundaryRelativeDensity,
    lowerRosserSetDensitySum_insert_min nu hqP hqprime hqD hqmin,
    Finset.prod_insert hqP]
  field_simp

/-- A finite lower boundary has nonnegative relative density under the local
sieve bounds `0 ≤ nu p < 1`. -/
theorem lowerRosserBoundaryRelativeDensity_nonneg
    (nu : ℕ → ℝ) {D q : ℕ} {P : Finset ℕ}
    (hnu : ∀ p ∈ P, 0 ≤ nu p) (hnuOne : ∀ p ∈ P, nu p < 1) :
    0 ≤ lowerRosserBoundaryRelativeDensity nu D q P := by
  unfold lowerRosserBoundaryRelativeDensity
  apply div_nonneg
  · apply Finset.sum_nonneg
    intro s hs
    apply Finset.prod_nonneg
    intro p hp
    exact hnu p (Finset.mem_powerset.mp (Finset.mem_filter.mp hs).1 hp)
  · apply Finset.prod_nonneg
    intro p hp
    exact sub_nonneg.mpr (hnuOne p hp).le

/-- Monotone normalized successor interface: adjoining a least prime can only
decrease the relative lower density when `0 ≤ nu < 1`. -/
theorem lowerRosserSetRelativeDensity_insert_min_le
    (nu : ℕ → ℝ) {D q : ℕ} {P : Finset ℕ}
    (hqP : q ∉ P) (hqprime : q.Prime) (hqD : q < D)
    (hqmin : ∀ p ∈ P, q ≤ p) (hnuq : 0 ≤ nu q) (hnuqOne : nu q < 1)
    (hnu : ∀ p ∈ P, 0 ≤ nu p) (hnuOne : ∀ p ∈ P, nu p < 1) :
    lowerRosserSetRelativeDensity nu D (insert q P) ≤
      lowerRosserSetRelativeDensity nu D P := by
  have hqFactor : 1 - nu q ≠ 0 :=
    sub_ne_zero.mpr (ne_of_gt hnuqOne)
  have hPFactor : (∏ p ∈ P, (1 - nu p)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun p hp =>
      sub_ne_zero.mpr (ne_of_gt (hnuOne p hp))
  rw [lowerRosserSetRelativeDensity_insert_min nu hqP hqprime hqD hqmin
    hqFactor hPFactor]
  exact sub_le_self _ (mul_nonneg
    (div_nonneg hnuq (sub_nonneg.mpr hnuqOne.le))
    (lowerRosserBoundaryRelativeDensity_nonneg nu hnu hnuOne))

/-- Terminal base for the finite normalized lower recursion. -/
theorem lowerRosserSetRelativeDensity_empty
    (nu : ℕ → ℝ) {D : ℕ} (hD : 1 < D) :
    lowerRosserSetRelativeDensity nu D ∅ = 1 := by
  simp [lowerRosserSetRelativeDensity, lowerRosserSetDensitySum,
    lowerRosserSetWeight, LowerRosserAdmissibleSet, hD]

/-- Cubic-shell form of `lowerRosserSetDensitySum_insert_min`. -/
theorem lowerRosserSetDensitySum_insert_min_cube
    (nu : ℕ → ℝ) {D q : ℕ} {P : Finset ℕ}
    (hqP : q ∉ P) (hqprime : q.Prime) (hqD : q < D)
    (hqmin : ∀ p ∈ P, q ≤ p) :
    lowerRosserSetDensitySum nu D (insert q P) =
      (1 - nu q) * lowerRosserSetDensitySum nu D P -
        nu q * ∑ s ∈ P.powerset.filter (fun s ↦
          ¬Even s.card ∧ s.prod id < D ∧
            LowerRosserAdmissibleSet D s ∧ D ≤ s.prod id * q ^ 3),
          ∏ p ∈ s, nu p := by
  rw [lowerRosserSetDensitySum_insert_min nu hqP hqprime hqD hqmin]
  have hfilter :
      P.powerset.filter (LowerRosserBoundarySet D q) =
        P.powerset.filter (fun s ↦
          ¬Even s.card ∧ s.prod id < D ∧
            LowerRosserAdmissibleSet D s ∧ D ≤ s.prod id * q ^ 3) := by
    apply Finset.filter_congr
    intro s hs
    have hsub : s ⊆ P := Finset.mem_powerset.mp hs
    exact lowerRosserBoundarySet_iff_cube_le
      (fun h ↦ hqP (hsub h)) hqprime (fun p hp ↦ hqmin p (hsub hp))
  rw [hfilter]


/-- The cubic-boundary mass lost when the new least prime `q` is inserted. -/
noncomputable def lowerRosserBoundaryMass
    (nu : ℕ → ℝ) (D q : ℕ) (P : Finset ℕ) : ℝ :=
  ∑ s ∈ P.powerset.filter (fun s ↦
      ¬Even s.card ∧ s.prod id < D ∧
        LowerRosserAdmissibleSet D s ∧ D ≤ s.prod id * q ^ 3),
    ∏ p ∈ s, nu p

/-- The total (unnormalized) boundary loss in a finite sequence of least-prime
insertions. Earlier losses are multiplied by all Euler factors inserted later. -/
noncomputable def lowerRosserBoundaryAccum
    (nu : ℕ → ℝ) (D : ℕ) (P : Finset ℕ) : List ℕ → ℝ
  | [] => 0
  | q :: qs =>
      (1 - nu q) * lowerRosserBoundaryAccum nu D P qs +
        nu q * lowerRosserBoundaryMass nu D q (qs.foldr insert P)

private theorem mem_foldr_insert_iff {x : ℕ} {P : Finset ℕ} :
    ∀ qs : List ℕ, x ∈ qs.foldr insert P ↔ x ∈ P ∨ x ∈ qs
  | [] => by simp
  | q :: qs => by
      rw [List.foldr_cons]
      simp only [Finset.mem_insert, mem_foldr_insert_iff qs, List.mem_cons]
      aesop

/-- Exact finite iteration of the lower Rosser density recurrence.

The list is ordered increasingly, so `foldr insert P` inserts its largest prime
first and its smallest prime last. The formula uses no division by Euler
factors; consequently it needs no positivity or nonvanishing hypothesis on
`1 - nu q`. -/
theorem lowerRosserSetDensitySum_foldr_insert
    (nu : ℕ → ℝ) (D : ℕ) (P : Finset ℕ) (qs : List ℕ)
    (hprime : ∀ q ∈ qs, q.Prime)
    (hD : ∀ q ∈ qs, q < D)
    (hordered : qs.Pairwise (· < ·))
    (hdisjoint : ∀ q ∈ qs, q ∉ P)
    (hbase : ∀ q ∈ qs, ∀ p ∈ P, q ≤ p) :
    lowerRosserSetDensitySum nu D (qs.foldr insert P) =
      (qs.map (fun q ↦ 1 - nu q)).prod * lowerRosserSetDensitySum nu D P -
        lowerRosserBoundaryAccum nu D P qs := by
  induction qs with
  | nil => simp [lowerRosserBoundaryAccum]
  | cons q qs ih =>
      have hord := List.pairwise_cons.mp hordered
      have hqnot : q ∉ qs.foldr insert P := by
        rw [mem_foldr_insert_iff]
        rintro (hqP | hq)
        · exact hdisjoint q (by simp) hqP
        · exact (Nat.lt_irrefl q) (hord.1 q hq)
      have hqmin : ∀ p ∈ qs.foldr insert P, q ≤ p := by
        intro p hp
        rw [mem_foldr_insert_iff] at hp
        rcases hp with hp | hp
        · exact hbase q (by simp) p hp
        · exact (hord.1 p hp).le
      have ih' := ih
        (fun r hr ↦ hprime r (by simp [hr]))
        (fun r hr ↦ hD r (by simp [hr]))
        hord.2
        (fun r hr ↦ hdisjoint r (by simp [hr]))
        (fun r hr p hp ↦ hbase r (by simp [hr]) p hp)
      rw [List.foldr_cons,
        lowerRosserSetDensitySum_insert_min_cube nu hqnot
          (hprime q (by simp)) (hD q (by simp)) hqmin,
        ih']
      simp only [List.map_cons, List.prod_cons, lowerRosserBoundaryAccum,
        lowerRosserBoundaryMass]
      ring

/-- The `BoundingSieve.mainSum` of the explicit lower Rosser coefficient is
exactly its finite subset density sum.  This is the first finite transport edge
from Suzuki's Rosser--Iwaniec coefficient to the density recursion. -/
theorem mainSum_lowerRosserWeight_eq_setDensitySum
    (S : BoundingSieve) (D : ℕ) :
    S.mainSum (lowerRosserWeight S.prodPrimes D) =
      lowerRosserSetDensitySum S.nu D S.prodPrimes.primeFactors := by
  unfold BoundingSieve.mainSum lowerRosserSetDensitySum
  rw [Internal.sum_divisors_eq_sum_primeFactors_powerset S.prodPrimes_squarefree]
  apply Finset.sum_congr rfl
  intro s hs
  have hsub : s ⊆ S.prodPrimes.primeFactors :=
    Finset.mem_powerset.mp hs
  have hdiv : s.prod id ∣ S.prodPrimes := by
    rw [← Nat.prod_primeFactors_of_squarefree S.prodPrimes_squarefree]
    simpa only [id_eq] using
      Finset.prod_dvd_prod_of_subset s S.prodPrimes.primeFactors id hsub
  have hprime : ∀ p ∈ s, p.Prime :=
    fun p hp ↦ Nat.prime_of_mem_primeFactors (hsub hp)
  have hpf : (s.prod id).primeFactors = s := by
    simpa only [id_eq] using Nat.primeFactors_prod hprime
  rw [lowerRosserWeight_prod_eq_setWeight S.prodPrimes_squarefree hsub,
    ← S.prod_primeFactors_nu hdiv, hpf]

theorem abs_lowerRosserWeight_le_one (P D d : ℕ) :
    |lowerRosserWeight P D d| ≤ 1 := by
  unfold lowerRosserWeight
  split
  · split <;> norm_num
  · norm_num

theorem lowerRosserWeight_dvd {P D d : ℕ}
    (h : lowerRosserWeight P D d ≠ 0) : d ∣ P := by
  unfold lowerRosserWeight at h
  split at h
  · exact (Nat.mem_divisors.mp ‹d ∈ P.divisors ∧ d < D ∧ LowerRosserAdmissible D d›.1).1
  · simp at h

theorem lowerRosserWeight_lt_level {P D d : ℕ}
    (h : lowerRosserWeight P D d ≠ 0) : d < D := by
  unfold lowerRosserWeight at h
  split at h
  · exact ‹d ∈ P.divisors ∧ d < D ∧ LowerRosserAdmissible D d›.2.1
  · simp at h

theorem lowerRosserWeight_hasLowerLevelSupport (P D : ℕ) :
    HasLowerLevelSupport P D (lowerRosserWeight P D) := by
  intro d hd hD
  unfold lowerRosserWeight
  simp [hD]

/-- A finite Rosser certificate is the combinatorial toggle-min conclusion:
even admissible subsets inject into odd admissible subsets.  Its consequence
is exactly the lower divisor-sum inequality needed by `BoundingSieve`. -/
def IsLowerRosserCertificate (P D : ℕ) : Prop :=
  IsLowerMoebiusOn P (lowerRosserWeight P D)

/-- The explicit lower Rosser weight is an unconditional finite lower-Möbius
certificate for a squarefree prime product whose prime factors lie below the
level. -/
theorem lowerRosserWeight_certificate {P D : ℕ} (hP : Squarefree P)
    (hP0 : P ≠ 0) (hD : ∀ p ∈ P.primeFactors, p < D) :
    IsLowerRosserCertificate P D := by
  intro n hn
  have hnSquarefree : Squarefree n := Squarefree.squarefree_of_dvd hn hP
  rw [Internal.sum_divisors_eq_sum_primeFactors_powerset hnSquarefree]
  by_cases hn1 : n = 1
  · subst n
    simp only [Nat.primeFactors_one, Finset.powerset_empty,
      Finset.sum_singleton, Finset.prod_empty]
    unfold lowerRosserWeight
    split <;> norm_num
  · rw [if_neg hn1]
    have hnFactors : n.primeFactors.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hempty
      rcases Nat.primeFactors_eq_empty.mp hempty with hn0 | hn_one
      · exact hnSquarefree.ne_zero hn0
      · exact hn1 hn_one
    have hsub : n.primeFactors ⊆ P.primeFactors :=
      Nat.primeFactors_mono hn hP0
    calc
      ∑ s ∈ n.primeFactors.powerset, lowerRosserWeight P D (s.prod id) =
          ∑ s ∈ n.primeFactors.powerset, lowerRosserSetWeight D s := by
        apply Finset.sum_congr rfl
        intro s hs
        exact lowerRosserWeight_prod_eq_setWeight hP
          ((Finset.mem_powerset.mp hs).trans hsub)
      _ ≤ 0 := sum_lowerRosserSetWeight_nonpos hnFactors
        (fun p hp ↦ Nat.prime_of_mem_primeFactors hp)
        (fun p hp ↦ hD p (hsub hp))

/-- A certified lower Rosser weight supplies the finite divisor-sum lower
bound, while retaining the explicit source formula above. -/
theorem lowerRosserWeight_divisor_sum {P D n : ℕ}
    (hcert : IsLowerRosserCertificate P D) (hn : n ∣ P) :
    ∑ d ∈ n.divisors, lowerRosserWeight P D d ≤ if n = 1 then 1 else 0 :=
  hcert n hn


end MathlibNt.SieveTheory.LinearSieve
