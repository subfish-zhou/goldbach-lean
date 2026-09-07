import MathlibNt.SieveTheory.SwitchingPrinciple
import Mathlib.Data.Finset.NatDivisors
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.SmoothNumbers
import Mathlib.RingTheory.Radical.NatInt

/-!
# The Jurkat--Richert 1965 `gamma(p) = 1`, `q = 1` specialization

This file begins the literal finite specialization of Jurkat--Richert (1965),
with local density exactly `1 / p`. The companion `ChenTheoremFive` module
proves its complete two-sided Theorem 5. The separate `ChenRichertConsumer`
module connects the actual Goldbach density `1 / (p - 1)` through constructed
delay majorants and modern sieve comparisons, not by identifying the densities.

The literal Buchstab and Euler identities `(2.2)` and `(2.3)` are proved below.
The concrete count is then expanded to every positive finite depth along
explicit chains `pᵢ < ... < p₁`, in the nested recursive form used by the
paper's induction, and then flattened into the four displayed finite sums of
formula `(2.1)`.  The finite Rosser identities instantiate existing adapted
coefficient machinery at `1 / p`; no identification with the concrete count
expansion is asserted.  The algebraic comparison and terminal lemmas isolate
two further finite steps needed by the source proof.
-/

open scoped BigOperators ArithmeticFunction.zeta ArithmeticFunction.Moebius

namespace MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne

open MathlibNt.SieveTheory

noncomputable section

/-- The literal local density `gamma(p) / p` when `gamma(p) = 1`. -/
def localDensity (p : ℕ) : ℝ := 1 / (p : ℝ)

/-- The local Euler factor is nonzero at every prime. -/
theorem one_sub_localDensity_ne_zero {p : ℕ} (hp : p.Prime) :
    1 - localDensity p ≠ 0 := by
  have hpReal : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hlt : localDensity p < 1 := by
    simpa [localDensity] using
      ((div_lt_one (by positivity : (0 : ℝ) < p)).2 hpReal)
  exact ne_of_gt (sub_pos.mpr hlt)

/-- After Euler normalization, a selected prime contributes `1 / (p - 1)`. -/
theorem localDensity_div_one_sub {p : ℕ} (hp : p.Prime) :
    localDensity p / (1 - localDensity p) = 1 / ((p : ℝ) - 1) := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hp1 : (p : ℝ) - 1 ≠ 0 := sub_ne_zero.mpr (ne_of_gt (by exact_mod_cast hp.one_lt))
  unfold localDensity
  field_simp

/-- The finite prime carrier `p < z`, `p ∤ k` from the 1965 paper. -/
noncomputable def siftingPrimes (k : ℕ) (z : ℝ) : Finset ℕ :=
  (Finset.range ⌈z⌉₊).filter
    (fun p => p.Prime ∧ (p : ℝ) < z ∧ ¬p ∣ k)

theorem mem_siftingPrimes {k p : ℕ} {z : ℝ} :
    p ∈ siftingPrimes k z ↔ p.Prime ∧ (p : ℝ) < z ∧ ¬p ∣ k := by
  rw [siftingPrimes, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨_, hp, hpz, hpk⟩
    exact ⟨hp, hpz, hpk⟩
  · rintro ⟨hp, hpz, hpk⟩
    exact ⟨Nat.lt_ceil.mpr hpz, hp, hpz, hpk⟩

/-- At `k = 1`, the source's strict real cutoff is exactly Mathlib's
natural prime cutoff at `ceil z`. -/
theorem siftingPrimes_one_eq_primesBelow {z : ℝ} :
    siftingPrimes 1 z = ⌈z⌉₊.primesBelow := by
  ext p
  rw [mem_siftingPrimes, Nat.mem_primesBelow]
  constructor
  · rintro ⟨hp, hpz, -⟩
    exact ⟨Nat.lt_ceil.mpr hpz, hp⟩
  · rintro ⟨hpz, hp⟩
    exact
      ⟨hp, Nat.lt_ceil.mp hpz,
        fun hp1 => hp.ne_one (Nat.dvd_one.mp hp1)⟩

/-- The selected primes below `z` omitted only because they divide `k`. -/
noncomputable def excludedSiftingPrimes (k : ℕ) (z : ℝ) : Finset ℕ :=
  (siftingPrimes 1 z).filter (fun p => p ∣ k)

/-- The squarefree product of the primes omitted from `P_k(z)`. -/
noncomputable def excludedSiftingFactor (k : ℕ) (z : ℝ) : ℕ :=
  (excludedSiftingPrimes k z).prod id

theorem siftingPrimes_union_excluded
    (k : ℕ) (z : ℝ) :
    siftingPrimes k z ∪ excludedSiftingPrimes k z =
      siftingPrimes 1 z := by
  ext p
  simp only [Finset.mem_union, excludedSiftingPrimes,
    Finset.mem_filter, mem_siftingPrimes]
  constructor
  · rintro (⟨hp, hpz, hpk⟩ | ⟨⟨hp, hpz, hp1⟩, hpk⟩)
    · exact ⟨hp, hpz, fun hp1 => hp.ne_one (Nat.dvd_one.mp hp1)⟩
    · exact ⟨hp, hpz, hp1⟩
  · rintro ⟨hp, hpz, hp1⟩
    by_cases hpk : p ∣ k
    · exact Or.inr ⟨⟨hp, hpz, hp1⟩, hpk⟩
    · exact Or.inl ⟨hp, hpz, hpk⟩

theorem excludedSiftingFactor_dvd_siftingPrimes_one
    (k : ℕ) (z : ℝ) :
    excludedSiftingFactor k z ∣ (siftingPrimes 1 z).prod id := by
  exact Finset.prod_dvd_prod_of_subset
    (excludedSiftingPrimes k z) (siftingPrimes 1 z) id
    (Finset.filter_subset _ _)

theorem excludedSiftingFactor_primeFactors
    (k : ℕ) (z : ℝ) :
    (excludedSiftingFactor k z).primeFactors =
      excludedSiftingPrimes k z := by
  exact Nat.primeFactors_prod fun p hp =>
    (mem_siftingPrimes.mp (Finset.mem_filter.mp hp).1).1

/-- The paper's finite Euler product `R_k(z)`. -/
noncomputable def sieveProduct (k : ℕ) (z : ℝ) : ℝ :=
  ∏ p ∈ siftingPrimes k z, (1 - localDensity p)

theorem sieveProduct_pos (k : ℕ) (z : ℝ) :
    0 < sieveProduct k z := by
  unfold sieveProduct
  apply Finset.prod_pos
  intro p hp
  have hpPrime := (mem_siftingPrimes.mp hp).1
  have hpReal : (1 : ℝ) < p := by exact_mod_cast hpPrime.one_lt
  have hlt : localDensity p < 1 := by
    simpa [localDensity] using
      ((div_lt_one (by positivity : (0 : ℝ) < p)).2 hpReal)
  exact sub_pos.mpr hlt

/-- The literal product over primes `p < z` is the standard finite Mertens
product through `ceil z - 1`; this records the strict real cutoff exactly. -/
theorem sieveProduct_one_eq_mertensPrimeProduct (z : ℝ) :
    sieveProduct 1 z =
      AnalyticNumberTheory.Mertens.primeProduct (⌈z⌉₊ - 1) := by
  unfold sieveProduct AnalyticNumberTheory.Mertens.primeProduct
  apply Finset.prod_congr
  · ext p
    rw [mem_siftingPrimes, AnalyticNumberTheory.Mertens.mem_primesUpTo]
    constructor
    · rintro ⟨hp, hpz, hp1⟩
      have hpCeil : p < ⌈z⌉₊ := Nat.lt_ceil.mpr hpz
      exact ⟨hp, by omega⟩
    · rintro ⟨hp, hpCeil⟩
      have hpTwo : 2 ≤ p := hp.two_le
      have hpLtCeil : p < ⌈z⌉₊ := by omega
      exact
        ⟨hp, Nat.lt_ceil.mp hpLtCeil,
          fun hp1 => hp.ne_one (Nat.dvd_one.mp hp1)⟩
  · intro p hp
    rfl

/-- Mertens' product theorem with the paper's literal strict real cutoff.
The proof of `(3.9)` below transports `log (ceil z - 1)` to `log z`. -/
theorem exists_sieveProduct_one_mertens_bound :
    ∃ C > 0, ∀ z : ℝ, 2 ≤ ⌈z⌉₊ - 1 →
      |sieveProduct 1 z -
          Real.exp (-Real.eulerMascheroniConstant) /
            Real.log (⌈z⌉₊ - 1 : ℕ)| ≤
        C / Real.log (⌈z⌉₊ - 1 : ℕ) ^ 2 := by
  obtain ⟨C, hC, hMertens⟩ :=
    AnalyticNumberTheory.Mertens.primeProduct_mertens_nat
  refine ⟨C, hC, fun z hz => ?_⟩
  rw [sieveProduct_one_eq_mertensPrimeProduct]
  exact hMertens (⌈z⌉₊ - 1) hz

/-- Inverting a positive Mertens approximation preserves its leading
coefficient and costs only an additive constant once the logarithm is large. -/
private theorem inv_le_log_div_add_of_abs_sub_le
    {P a C L : ℝ}
    (hP : 0 < P) (ha : 0 < a) (hC : 0 ≤ C) (hL : 0 < L)
    (hlarge : 2 * C ≤ a * L)
    (happrox : |P - a / L| ≤ C / L ^ 2) :
    P⁻¹ ≤ L / a + 2 * C / a ^ 2 := by
  have hlower : a / L - C / L ^ 2 ≤ P := by
    have h := (abs_le.mp happrox).1
    linarith
  have hcoefficient : 0 ≤ L / a + 2 * C / a ^ 2 := by
    positivity
  rw [inv_le_iff_one_le_mul₀ hP]
  calc
    1 ≤ (L / a + 2 * C / a ^ 2) *
          (a / L - C / L ^ 2) := by
      have hnonneg :
          0 ≤ C * (a * L - 2 * C) / (a ^ 2 * L ^ 2) :=
        div_nonneg
          (mul_nonneg hC (sub_nonneg.mpr hlarge))
          (mul_nonneg (sq_nonneg a) (sq_nonneg L))
      have hid :
          (L / a + 2 * C / a ^ 2) *
                (a / L - C / L ^ 2) - 1 =
            C * (a * L - 2 * C) / (a ^ 2 * L ^ 2) := by
        field_simp [ha.ne', hL.ne']
        ring
      linarith
    _ ≤ (L / a + 2 * C / a ^ 2) * P :=
      mul_le_mul_of_nonneg_left hlower hcoefficient

/-- Uniform reciprocal Mertens bound at the paper's strict real cutoff.
The leading coefficient is exactly `exp EulerGamma`; the finite initial range
is absorbed into one additive constant rather than checked by a finite scan. -/
theorem exists_sieveProduct_one_inv_le_log_div_add :
    ∃ B > 0, ∀ z : ℝ, 1 < z →
      (sieveProduct 1 z)⁻¹ ≤
        Real.log z / Real.exp (-Real.eulerMascheroniConstant) + B := by
  obtain ⟨C, hC, hMertens⟩ :=
    exists_sieveProduct_one_mertens_bound
  let a := Real.exp (-Real.eulerMascheroniConstant)
  let N := ⌈Real.exp (2 * C / a)⌉₊ + 2
  let B :=
    2 * C / a ^ 2 +
      ∑ n ∈ Finset.range N,
        (AnalyticNumberTheory.Mertens.primeProduct n)⁻¹ +
      1
  have ha : 0 < a := by
    dsimp [a]
    positivity
  have hsumNonneg :
      0 ≤ ∑ n ∈ Finset.range N,
        (AnalyticNumberTheory.Mertens.primeProduct n)⁻¹ := by
    exact Finset.sum_nonneg fun n _ =>
      (inv_pos.mpr
        (AnalyticNumberTheory.Mertens.primeProduct_pos n)).le
  refine ⟨B, ?_, fun z hz => ?_⟩
  · have herrorNonneg : 0 ≤ 2 * C / a ^ 2 := by
      positivity
    dsimp [B]
    linarith
  · let n := ⌈z⌉₊ - 1
    have hzPos : 0 < z := zero_lt_one.trans hz
    have hnLtZ : (n : ℝ) < z := by
      have hceilOne : 1 ≤ ⌈z⌉₊ := Nat.one_le_ceil_iff.mpr hzPos
      have hceilLt : (⌈z⌉₊ : ℝ) < z + 1 :=
        Nat.ceil_lt_add_one hzPos.le
      change (((⌈z⌉₊ - 1 : ℕ) : ℝ)) < z
      rw [Nat.cast_sub hceilOne]
      norm_num
      linarith
    by_cases hN : N ≤ n
    · have hNtwo : 2 ≤ N := by
        dsimp [N]
        omega
      have hnTwo : 2 ≤ n := hNtwo.trans hN
      have hnPos : (0 : ℝ) < n := by
        exact_mod_cast (lt_of_lt_of_le (by omega : 0 < N) hN)
      have hExpN : Real.exp (2 * C / a) ≤ (N : ℝ) := by
        calc
          Real.exp (2 * C / a) ≤
              (⌈Real.exp (2 * C / a)⌉₊ : ℝ) :=
            Nat.le_ceil _
          _ ≤ (⌈Real.exp (2 * C / a)⌉₊ + 2 : ℕ) := by
            norm_num
          _ = (N : ℝ) := by rfl
      have hLogThreshold :
          2 * C / a ≤ Real.log (n : ℝ) :=
        (Real.le_log_iff_exp_le hnPos).2
          (hExpN.trans (Nat.cast_le.mpr hN))
      have hlarge :
          2 * C ≤ a * Real.log (n : ℝ) := by
        have h := (div_le_iff₀ ha).mp hLogThreshold
        simpa [mul_comm] using h
      have hnLogPos : 0 < Real.log (n : ℝ) :=
        Real.log_pos (by exact_mod_cast (show 1 < n by omega))
      have hinverse :
          (sieveProduct 1 z)⁻¹ ≤
            Real.log (n : ℝ) / a + 2 * C / a ^ 2 := by
        exact
          inv_le_log_div_add_of_abs_sub_le
            (sieveProduct_pos 1 z) ha hC.le hnLogPos hlarge
            (hMertens z hnTwo)
      have hLogLe : Real.log (n : ℝ) ≤ Real.log z :=
        Real.strictMonoOn_log.monotoneOn hnPos hzPos hnLtZ.le
      have hDivLe :
          Real.log (n : ℝ) / a ≤ Real.log z / a :=
        (div_le_div_iff_of_pos_right ha).2 hLogLe
      change
        (sieveProduct 1 z)⁻¹ ≤
          Real.log z / a + B
      have hfinite :
          2 * C / a ^ 2 ≤ B := by
        dsimp [B]
        linarith
      linarith
    · have hnMem : n ∈ Finset.range N :=
        Finset.mem_range.mpr (Nat.lt_of_not_ge hN)
      have hinverseSum :
          (AnalyticNumberTheory.Mertens.primeProduct n)⁻¹ ≤
            ∑ m ∈ Finset.range N,
              (AnalyticNumberTheory.Mertens.primeProduct m)⁻¹ := by
        exact
          Finset.single_le_sum
            (s := Finset.range N)
            (f := fun m =>
              (AnalyticNumberTheory.Mertens.primeProduct m)⁻¹)
            (fun m _ =>
              (inv_pos.mpr
                (AnalyticNumberTheory.Mertens.primeProduct_pos m)).le)
            hnMem
      have hLogNonneg : 0 ≤ Real.log z / a :=
        div_nonneg (Real.log_pos hz).le ha.le
      have hErrorNonneg : 0 ≤ 2 * C / a ^ 2 := by
        positivity
      rw [sieveProduct_one_eq_mertensPrimeProduct]
      change
        (AnalyticNumberTheory.Mertens.primeProduct n)⁻¹ ≤
          Real.log z / a + B
      dsimp [B]
      linarith

/-- The preceding strict-cutoff inversion with its leading coefficient in the
paper's displayed `exp EulerGamma` normalization. -/
theorem exists_sieveProduct_one_inv_le_exp_mul_log_add :
    ∃ B > 0, ∀ z : ℝ, 1 < z →
      (sieveProduct 1 z)⁻¹ ≤
        Real.exp Real.eulerMascheroniConstant * Real.log z + B := by
  obtain ⟨B, hB, hInv⟩ :=
    exists_sieveProduct_one_inv_le_log_div_add
  refine ⟨B, hB, fun z hz => ?_⟩
  calc
    (sieveProduct 1 z)⁻¹ ≤
        Real.log z / Real.exp (-Real.eulerMascheroniConstant) + B :=
      hInv z hz
    _ = Real.exp Real.eulerMascheroniConstant * Real.log z + B := by
      rw [div_eq_mul_inv, Real.exp_neg]
      simp only [inv_inv]
      ring

/-- The literal finite Euler identity `(2.3)`:
`R_k(z) = 1 - sum_{p < z, p ∤ k} R_k(p) / p`. -/
theorem sieveProduct_eq_one_sub_sum (k : ℕ) (z : ℝ) :
    sieveProduct k z =
      1 - ∑ p ∈ siftingPrimes k z,
        localDensity p * sieveProduct k p := by
  unfold sieveProduct
  rw [Finset.prod_one_sub_ordered]
  apply congrArg (fun x : ℝ => 1 - x)
  apply Finset.sum_congr rfl
  intro p hp
  congr 1
  have hpz : (p : ℝ) < z := (mem_siftingPrimes.mp hp).2.1
  congr 1
  ext q
  rw [Finset.mem_filter, mem_siftingPrimes, mem_siftingPrimes]
  constructor
  · rintro ⟨⟨hqPrime, hqz, hqk⟩, hqp⟩
    exact ⟨hqPrime, by exact_mod_cast hqp, hqk⟩
  · rintro ⟨hqPrime, hqp, hqk⟩
    refine ⟨⟨hqPrime, ?_, hqk⟩, by exact_mod_cast hqp⟩
    exact hqp.trans hpz

/-- The paper's sifted cardinality `A_k(M; z)`. -/
noncomputable def siftedCount (M : Finset ℕ) (k : ℕ) (z : ℝ) : ℝ :=
  ((M.filter fun n => Nat.Coprime ((siftingPrimes k z).prod id) n).card : ℝ)

/-- The same sifted cardinality with an explicit finite prime carrier. -/
noncomputable def siftedCountOn (M P : Finset ℕ) : ℝ :=
  ((M.filter fun n => Nat.Coprime (P.prod id) n).card : ℝ)

/-- The divisibility-fiber realization of the paper's conditioned count
`A_k(M_p; p)`: `p` divides the original element, and no selected prime below
`p` divides it. -/
noncomputable def conditionedSiftedCountOn
    (M P : Finset ℕ) (p : ℕ) : ℝ :=
  ((M.filter fun n =>
      p ∣ n ∧ Nat.Coprime ((P.filter fun q => q < p).prod id) n).card : ℝ)

/-- Finite Buchstab partition over an arbitrary finite prime carrier.  Every
non-sifted element is assigned to its least selected prime divisor. -/
theorem siftedCountOn_eq_card_sub_conditioned_sum
    (M P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime) :
    siftedCountOn M P =
      (M.card : ℝ) - ∑ p ∈ P, conditionedSiftedCountOn M P p := by
  induction P using Finset.induction_on_max with
  | empty =>
      simp [siftedCountOn, conditionedSiftedCountOn]
  | insert a P hmax ih =>
      have haP : a ∉ P := by
        intro ha
        exact (Nat.lt_irrefl a) (hmax a ha)
      have haPrime : a.Prime := hprime a (Finset.mem_insert_self a P)
      have hPprime : ∀ p ∈ P, p.Prime := by
        intro p hp
        exact hprime p (Finset.mem_insert_of_mem hp)
      have hbelowA :
          (insert a P).filter (fun q => q < a) = P := by
        ext q
        simp only [Finset.mem_filter, Finset.mem_insert]
        constructor
        · rintro ⟨hq | hq, hlt⟩
          · subst q
            simp at hlt
          · exact hq
        · intro hq
          exact ⟨Or.inr hq, hmax q hq⟩
      have hbelowOld (p : ℕ) (hp : p ∈ P) :
          (insert a P).filter (fun q => q < p) =
            P.filter (fun q => q < p) := by
        ext q
        simp only [Finset.mem_filter, Finset.mem_insert]
        constructor
        · rintro ⟨hq | hq, hqp⟩
          · subst q
            exact (Nat.not_lt_of_ge (Nat.le_of_lt (hmax p hp)) hqp).elim
          · exact ⟨hq, hqp⟩
        · rintro ⟨hq, hqp⟩
          exact ⟨Or.inr hq, hqp⟩
      have hsplitNat :
          (M.filter fun n =>
              Nat.Coprime (P.prod id) n ∧ ¬a ∣ n).card +
            (M.filter fun n =>
              a ∣ n ∧ Nat.Coprime (P.prod id) n).card =
            (M.filter fun n => Nat.Coprime (P.prod id) n).card := by
        have hsplit :=
          Finset.card_filter_add_card_filter_not
            (s := M.filter fun n => Nat.Coprime (P.prod id) n)
            (p := fun n => a ∣ n)
        simpa only [Finset.filter_filter, Nat.add_comm, and_comm] using hsplit
      have hsplitReal :
          (((M.filter fun n =>
              Nat.Coprime (P.prod id) n ∧ ¬a ∣ n).card : ℕ) : ℝ) =
            ((M.filter fun n => Nat.Coprime (P.prod id) n).card : ℝ) -
            ((M.filter fun n =>
              a ∣ n ∧ Nat.Coprime (P.prod id) n).card : ℝ) := by
        have hsplitCast :=
          congrArg (fun n : ℕ => (n : ℝ)) hsplitNat
        push_cast at hsplitCast
        linarith
      have hsiftInsert :
          siftedCountOn M (insert a P) =
            siftedCountOn M P -
              conditionedSiftedCountOn M (insert a P) a := by
        rw [siftedCountOn, siftedCountOn, conditionedSiftedCountOn,
          Finset.prod_insert haP, hbelowA]
        convert hsplitReal using 1
        apply congrArg (fun S : Finset ℕ => (S.card : ℝ))
        ext n
        simp only [Finset.mem_filter]
        simp only [id_eq]
        rw [Nat.coprime_mul_iff_left, haPrime.coprime_iff_not_dvd]
        tauto
      have hold :
          ∑ p ∈ P, conditionedSiftedCountOn M (insert a P) p =
            ∑ p ∈ P, conditionedSiftedCountOn M P p := by
        apply Finset.sum_congr rfl
        intro p hp
        simp only [conditionedSiftedCountOn, hbelowOld p hp]
      calc
        siftedCountOn M (insert a P) =
            siftedCountOn M P -
              conditionedSiftedCountOn M (insert a P) a := hsiftInsert
        _ = (M.card : ℝ) -
              ∑ p ∈ P, conditionedSiftedCountOn M P p -
              conditionedSiftedCountOn M (insert a P) a := by rw [ih hPprime]
        _ = (M.card : ℝ) -
              (conditionedSiftedCountOn M (insert a P) a +
                ∑ p ∈ P, conditionedSiftedCountOn M (insert a P) p) := by
              rw [hold]
              ring
        _ = (M.card : ℝ) -
              ∑ p ∈ insert a P, conditionedSiftedCountOn M (insert a P) p := by
              rw [Finset.sum_insert haP]

/-- The literal finite Buchstab identity `(2.2)` for the paper's carrier
`p < z`, `p ∤ k`. -/
theorem siftedCount_eq_card_sub_conditioned_sum
    (M : Finset ℕ) (k : ℕ) (z : ℝ) :
    siftedCount M k z =
      (M.card : ℝ) -
        ∑ p ∈ siftingPrimes k z,
          conditionedSiftedCountOn M (siftingPrimes k z) p := by
  change siftedCountOn M (siftingPrimes k z) =
    (M.card : ℝ) -
      ∑ p ∈ siftingPrimes k z,
        conditionedSiftedCountOn M (siftingPrimes k z) p
  exact
    siftedCountOn_eq_card_sub_conditioned_sum M (siftingPrimes k z)
      (fun p hp => (mem_siftingPrimes.mp hp).1)

/-- Subtracting `(2.2)` at two cutoffs leaves exactly the conditioned primes
in the interval `z₁ ≤ p < z`.  This is the unsplit identity used to begin
formula `(2.4)`. -/
theorem siftedCount_eq_siftedCount_sub_interval
    (M : Finset ℕ) (k : ℕ) {z₁ z : ℝ} (hz : z₁ ≤ z) :
    siftedCount M k z =
      siftedCount M k z₁ -
        ∑ p ∈ (siftingPrimes k z).filter (fun p : ℕ => z₁ ≤ (p : ℝ)),
          conditionedSiftedCountOn M (siftingPrimes k z) p := by
  have hlow :
      (siftingPrimes k z).filter (fun p : ℕ => (p : ℝ) < z₁) =
        siftingPrimes k z₁ := by
    ext p
    simp only [Finset.mem_filter, mem_siftingPrimes]
    constructor
    · rintro ⟨⟨hp, -, hpk⟩, hpz₁⟩
      exact ⟨hp, hpz₁, hpk⟩
    · rintro ⟨hp, hpz₁, hpk⟩
      exact ⟨⟨hp, hpz₁.trans_le hz, hpk⟩, hpz₁⟩
  have hbelow (p : ℕ) (hp : p ∈ siftingPrimes k z₁) :
      (siftingPrimes k z).filter (fun q => q < p) =
        (siftingPrimes k z₁).filter (fun q => q < p) := by
    have hpz₁ : (p : ℝ) < z₁ := (mem_siftingPrimes.mp hp).2.1
    ext q
    simp only [Finset.mem_filter, mem_siftingPrimes]
    constructor
    · rintro ⟨⟨hq, -, hqk⟩, hqp⟩
      exact ⟨⟨hq, (by exact_mod_cast hqp : (q : ℝ) < p).trans hpz₁, hqk⟩, hqp⟩
    · rintro ⟨⟨hq, hqz₁, hqk⟩, hqp⟩
      exact ⟨⟨hq, hqz₁.trans_le hz, hqk⟩, hqp⟩
  have hold :
      ∑ p ∈ siftingPrimes k z₁,
          conditionedSiftedCountOn M (siftingPrimes k z) p =
        ∑ p ∈ siftingPrimes k z₁,
          conditionedSiftedCountOn M (siftingPrimes k z₁) p := by
    apply Finset.sum_congr rfl
    intro p hp
    simp only [conditionedSiftedCountOn, hbelow p hp]
  have hsplit :
      ∑ p ∈ siftingPrimes k z,
          conditionedSiftedCountOn M (siftingPrimes k z) p =
        ∑ p ∈ siftingPrimes k z₁,
            conditionedSiftedCountOn M (siftingPrimes k z₁) p +
          ∑ p ∈ (siftingPrimes k z).filter (fun p : ℕ => z₁ ≤ (p : ℝ)),
            conditionedSiftedCountOn M (siftingPrimes k z) p := by
    have hpartition :=
      Finset.sum_filter_add_sum_filter_not (siftingPrimes k z)
        (fun p : ℕ => (p : ℝ) < z₁)
        (fun p => conditionedSiftedCountOn M (siftingPrimes k z) p)
    rw [hlow, hold] at hpartition
    simpa only [not_lt] using hpartition.symm
  rw [siftedCount_eq_card_sub_conditioned_sum,
    siftedCount_eq_card_sub_conditioned_sum, hsplit]
  ring

/-- The first, recursively expandable prime range in the depth-one instance
of Theorem 1. -/
noncomputable def theoremOneInteriorPrimes
    (k : ℕ) (z₁ z y : ℝ) : Finset ℕ :=
  ((siftingPrimes k z).filter (fun p : ℕ => z₁ ≤ (p : ℝ))).filter
    (fun p => (p : ℝ) < Real.sqrt (y / p))

/-- The terminal boundary-prime range in the depth-one instance of Theorem 1. -/
noncomputable def theoremOneBoundaryPrimes
    (k : ℕ) (z₁ z y : ℝ) : Finset ℕ :=
  ((siftingPrimes k z).filter (fun p : ℕ => z₁ ≤ (p : ℝ))).filter
    (fun p => Real.sqrt (y / p) ≤ (p : ℝ) ∧ (p : ℝ) < y / p)

/-- Formula `(2.4)`, equivalently the depth-one case of Theorem 1.  The
conditioned primes are split at `sqrt (y / p)`, and the upper boundary
`p < y / p` follows from `p < z ≤ sqrt y`. -/
theorem siftedCount_theoremOne_depthOne
    (M : Finset ℕ) (k : ℕ) {z₁ z y : ℝ}
    (hz₁ : 2 ≤ z₁) (hz : z₁ ≤ z) (hzy : z ≤ Real.sqrt y) :
    siftedCount M k z =
      siftedCount M k z₁ -
        ∑ p ∈ theoremOneInteriorPrimes k z₁ z y,
          conditionedSiftedCountOn M (siftingPrimes k z) p -
        ∑ p ∈ theoremOneBoundaryPrimes k z₁ z y,
          conditionedSiftedCountOn M (siftingPrimes k z) p := by
  let interval :=
    (siftingPrimes k z).filter (fun p : ℕ => z₁ ≤ (p : ℝ))
  let interior := fun p : ℕ => (p : ℝ) < Real.sqrt (y / p)
  have hpUpper (p : ℕ) (hp : p ∈ interval) : (p : ℝ) < y / p := by
    have hpSift : p ∈ siftingPrimes k z := (Finset.mem_filter.mp hp).1
    have hpz : (p : ℝ) < z := (mem_siftingPrimes.mp hpSift).2.1
    have hpPrime : p.Prime := (mem_siftingPrimes.mp hpSift).1
    have hpPos : (0 : ℝ) < p := by exact_mod_cast hpPrime.pos
    have hsqrtPos : 0 < Real.sqrt y := by linarith
    have hy : 0 ≤ y := (Real.sqrt_pos.mp hsqrtPos).le
    have hpSqrt : (p : ℝ) < Real.sqrt y := hpz.trans_le hzy
    have hpSq : (p : ℝ) * p < y := by
      nlinarith [Real.sq_sqrt hy]
    exact (lt_div_iff₀ hpPos).2 hpSq
  have hboundary :
      interval.filter (fun p => ¬interior p) =
        theoremOneBoundaryPrimes k z₁ z y := by
    change
      interval.filter (fun p : ℕ => ¬(p : ℝ) < Real.sqrt (y / p)) =
        interval.filter
          (fun p : ℕ =>
            Real.sqrt (y / p) ≤ (p : ℝ) ∧ (p : ℝ) < y / p)
    ext p
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hp, hnot⟩
      exact ⟨hp, not_lt.mp hnot, hpUpper p hp⟩
    · rintro ⟨hp, hsqrt, -⟩
      exact ⟨hp, not_lt.mpr hsqrt⟩
  have hpartition :=
    Finset.sum_filter_add_sum_filter_not interval interior
      (fun p => conditionedSiftedCountOn M (siftingPrimes k z) p)
  rw [siftedCount_eq_siftedCount_sub_interval M k hz]
  change
    siftedCount M k z₁ -
        ∑ p ∈ interval,
          conditionedSiftedCountOn M (siftingPrimes k z) p =
      siftedCount M k z₁ -
        ∑ p ∈ interval.filter interior,
          conditionedSiftedCountOn M (siftingPrimes k z) p -
        ∑ p ∈ theoremOneBoundaryPrimes k z₁ z y,
          conditionedSiftedCountOn M (siftingPrimes k z) p
  rw [← hboundary]
  linarith

/-- The original-source divisibility fiber for successive chain primes.
Chains are stored least/newest prime first, so `[pᵢ, ..., p₁]` displays the
source order `pᵢ < ... < p₁`. -/
def conditionedCarrier (M : Finset ℕ) : List ℕ → Finset ℕ
  | [] => M
  | p :: ps => (conditionedCarrier M ps).filter fun n => p ∣ n

/-- The successive source scale: for `[pᵢ, ..., p₁]` this is
`y / (p₁ ... pᵢ)`. -/
def chainScale (y : ℝ) : List ℕ → ℝ
  | [] => y
  | p :: ps => chainScale y ps / p

/-- The divisibility-fiber realization of
`A_k(M_{p₁...pᵢ}; u)` attached to a prime chain. -/
noncomputable def chainSiftedCount
    (M : Finset ℕ) (k : ℕ) (ps : List ℕ) (u : ℝ) : ℝ :=
  siftedCount (conditionedCarrier M ps) k u

/-- An explicit interior chain from Theorem 1.  For the list
`[pᵢ, ..., p₁]`, every prime lies in `[z₁, z)`, the entries satisfy
`pᵢ < ... < p₁`, and each `pⱼ < sqrt (yⱼ)`. -/
def theoremOneInteriorChain
    (k : ℕ) (z₁ z y : ℝ) : List ℕ → Prop
  | [] => True
  | p :: ps =>
      p.Prime ∧ z₁ ≤ (p : ℝ) ∧ (p : ℝ) < z ∧ ¬p ∣ k ∧
        (∀ q ∈ ps, p < q) ∧
        (p : ℝ) < Real.sqrt (chainScale y (p :: ps)) ∧
        theoremOneInteriorChain k z₁ z y ps

/-- An explicit boundary chain from Theorem 1.  Its least/newest prime
`pᵢ` satisfies `sqrt (yᵢ) ≤ pᵢ < yᵢ`; all preceding primes satisfy the
interior constraints. -/
def theoremOneBoundaryChain
    (k : ℕ) (z₁ z y : ℝ) : List ℕ → Prop
  | [] => False
  | p :: ps =>
      p.Prime ∧ z₁ ≤ (p : ℝ) ∧ (p : ℝ) < z ∧ ¬p ∣ k ∧
        (∀ q ∈ ps, p < q) ∧
        Real.sqrt (chainScale y (p :: ps)) ≤ (p : ℝ) ∧
        (p : ℝ) < chainScale y (p :: ps) ∧
        theoremOneInteriorChain k z₁ z y ps

/-- The recursive scale is literally `y / (p₁ ... pᵢ)`. -/
theorem chainScale_eq_div_prod (y : ℝ) (ps : List ℕ) :
    chainScale y ps = y / (ps.prod : ℝ) := by
  induction ps with
  | nil => simp [chainScale]
  | cons p ps ih =>
      rw [chainScale, ih]
      simp only [List.prod_cons, Nat.cast_mul]
      rw [div_div]
      congr 1
      ring

/-- Every entry of an interior chain is prime. -/
theorem prime_of_mem_theoremOneInteriorChain
    {k q : ℕ} {ps : List ℕ} {z₁ z y : ℝ}
    (hchain : theoremOneInteriorChain k z₁ z y ps) (hq : q ∈ ps) :
    q.Prime := by
  induction ps with
  | nil => simp at hq
  | cons p ps ih =>
      rcases hchain with
        ⟨hpPrime, hz₁p, hpz, hpk, horder, hpInterior, htail⟩
      simp only [List.mem_cons] at hq
      rcases hq with rfl | hq
      · exact hpPrime
      · exact ih htail hq

/-- Along an interior chain, successive divisibility conditioning is exactly
conditioning by the product `p₁ ... pᵢ`. -/
theorem conditionedCarrier_eq_filter_prod_of_interiorChain
    (M : Finset ℕ) {k : ℕ} {ps : List ℕ} {z₁ z y : ℝ}
    (hchain : theoremOneInteriorChain k z₁ z y ps) :
    conditionedCarrier M ps = M.filter fun n => ps.prod ∣ n := by
  induction ps with
  | nil => simp [conditionedCarrier]
  | cons p ps ih =>
      rcases hchain with
        ⟨hpPrime, hz₁p, hpz, hpk, horder, hpInterior, htail⟩
      have hcoprime : Nat.Coprime p ps.prod := by
        rw [Nat.coprime_list_prod_right_iff]
        intro q hq
        rw [hpPrime.coprime_iff_not_dvd]
        intro hpq
        have hpqEq : p = q :=
          (Nat.prime_dvd_prime_iff_eq hpPrime
            (prime_of_mem_theoremOneInteriorChain htail hq)).mp hpq
        exact (ne_of_lt (horder q hq)) hpqEq
      rw [conditionedCarrier, ih htail]
      rw [Finset.filter_filter]
      apply Finset.filter_congr
      intro n hn
      simp only [List.prod_cons]
      constructor
      · rintro ⟨hprod, hp⟩
        exact hcoprime.mul_dvd_of_dvd_of_dvd hp hprod
      · intro hprod
        rcases hprod with ⟨c, rfl⟩
        refine ⟨?_, ?_⟩
        · exact ⟨p * c, by ac_rfl⟩
        · exact ⟨ps.prod * c, by ac_rfl⟩

/-- On the paper's prime carrier, conditioning at `p` is exactly sifting the
`p`-divisibility fibre at cutoff `p`. -/
theorem conditionedSiftedCountOn_siftingPrimes_eq
    (M : Finset ℕ) (k : ℕ) {z : ℝ} {p : ℕ}
    (hp : p ∈ siftingPrimes k z) :
    conditionedSiftedCountOn M (siftingPrimes k z) p =
      siftedCount (M.filter fun n => p ∣ n) k p := by
  have hpz : (p : ℝ) < z := (mem_siftingPrimes.mp hp).2.1
  have hbelow :
      (siftingPrimes k z).filter (fun q => q < p) =
        siftingPrimes k p := by
    ext q
    simp only [Finset.mem_filter, mem_siftingPrimes]
    constructor
    · rintro ⟨⟨hqPrime, -, hqk⟩, hqp⟩
      exact ⟨hqPrime, by exact_mod_cast hqp, hqk⟩
    · rintro ⟨hqPrime, hqp, hqk⟩
      refine ⟨⟨hqPrime, hqp.trans hpz, hqk⟩, ?_⟩
      exact_mod_cast hqp
  rw [conditionedSiftedCountOn, siftedCount, hbelow]
  congr 1
  apply congrArg Finset.card
  ext n
  simp only [Finset.mem_filter]
  tauto

/-- Appending an interior prime to an explicit interior chain preserves all
of the paper's chain and square-root constraints. -/
theorem theoremOneInteriorChain_cons_of_mem
    {k p q : ℕ} {ps : List ℕ} {z₁ z y : ℝ}
    (hchain : theoremOneInteriorChain k z₁ z y (p :: ps))
    (hq :
      q ∈ theoremOneInteriorPrimes k z₁ p
        (chainScale y (p :: ps))) :
    theoremOneInteriorChain k z₁ z y (q :: p :: ps) := by
  rcases hchain with
    ⟨hpPrime, hz₁p, hpz, hpk, horder, hpInterior, htail⟩
  rw [theoremOneInteriorPrimes, Finset.mem_filter,
    Finset.mem_filter] at hq
  rcases hq with ⟨⟨hqSift, hz₁q⟩, hqInterior⟩
  rcases mem_siftingPrimes.mp hqSift with ⟨hqPrime, hqp, hqk⟩
  have hqpNat : q < p := by exact_mod_cast hqp
  refine
    ⟨hqPrime, hz₁q, hqp.trans hpz, hqk, ?_, ?_,
      ⟨hpPrime, hz₁p, hpz, hpk, horder, hpInterior, htail⟩⟩
  · intro a ha
    simp only [List.mem_cons] at ha
    rcases ha with rfl | ha
    · exact hqpNat
    · exact hqpNat.trans (horder a ha)
  · simpa only [chainScale] using hqInterior

/-- Appending a boundary prime to an explicit interior chain produces exactly
the boundary condition `sqrt (yᵢ) ≤ pᵢ < yᵢ`. -/
theorem theoremOneBoundaryChain_cons_of_mem
    {k p q : ℕ} {ps : List ℕ} {z₁ z y : ℝ}
    (hchain : theoremOneInteriorChain k z₁ z y (p :: ps))
    (hq :
      q ∈ theoremOneBoundaryPrimes k z₁ p
        (chainScale y (p :: ps))) :
    theoremOneBoundaryChain k z₁ z y (q :: p :: ps) := by
  rw [theoremOneBoundaryPrimes, Finset.mem_filter,
    Finset.mem_filter] at hq
  rcases hq with ⟨⟨hqSift, hz₁q⟩, hqBoundary, hqUpper⟩
  rcases mem_siftingPrimes.mp hqSift with ⟨hqPrime, hqp, hqk⟩
  have hqpNat : q < p := by exact_mod_cast hqp
  rcases hchain with
    ⟨hpPrime, hz₁p, hpz, hpk, horder, hpInterior, htail⟩
  refine
    ⟨hqPrime, hz₁q, hqp.trans hpz, hqk, ?_, ?_, ?_,
      ⟨hpPrime, hz₁p, hpz, hpk, horder, hpInterior, htail⟩⟩
  · intro a ha
    simp only [List.mem_cons] at ha
    rcases ha with rfl | ha
    · exact hqpNat
    · exact hqpNat.trans (horder a ha)
  · simpa only [chainScale] using hqBoundary
  · simpa only [chainScale] using hqUpper

/-- The exact induction step in the proof of Theorem 1.  Starting from any
nonempty interior chain `[pᵢ, ..., p₁]`, it applies `(2.4)` to
`(M_{p₁...pᵢ}, yᵢ, pᵢ)`, producing the next interior and boundary chains. -/
theorem chainSiftedCount_eq_at_z₁_sub_extensions
    (M : Finset ℕ) (k p : ℕ) (ps : List ℕ) {z₁ z y : ℝ}
    (hz₁ : 2 ≤ z₁)
    (hchain : theoremOneInteriorChain k z₁ z y (p :: ps)) :
    chainSiftedCount M k (p :: ps) p =
      chainSiftedCount M k (p :: ps) z₁ -
        ∑ q ∈ theoremOneInteriorPrimes k z₁ p
            (chainScale y (p :: ps)),
          chainSiftedCount M k (q :: p :: ps) q -
        ∑ q ∈ theoremOneBoundaryPrimes k z₁ p
            (chainScale y (p :: ps)),
          chainSiftedCount M k (q :: p :: ps) q := by
  rcases hchain with
    ⟨hpPrime, hz₁p, hpz, hpk, horder, hpInterior, htail⟩
  have hdepth :=
    siftedCount_theoremOne_depthOne
      (conditionedCarrier M (p :: ps)) k hz₁ hz₁p hpInterior.le
  have hinterior :
      ∑ q ∈ theoremOneInteriorPrimes k z₁ p
          (chainScale y (p :: ps)),
          conditionedSiftedCountOn (conditionedCarrier M (p :: ps))
            (siftingPrimes k p) q =
        ∑ q ∈ theoremOneInteriorPrimes k z₁ p
          (chainScale y (p :: ps)),
          chainSiftedCount M k (q :: p :: ps) q := by
    apply Finset.sum_congr rfl
    intro q hq
    have hqSift : q ∈ siftingPrimes k p :=
      (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1
    rw [conditionedSiftedCountOn_siftingPrimes_eq _ _ hqSift]
    rfl
  have hboundary :
      ∑ q ∈ theoremOneBoundaryPrimes k z₁ p
          (chainScale y (p :: ps)),
          conditionedSiftedCountOn (conditionedCarrier M (p :: ps))
            (siftingPrimes k p) q =
        ∑ q ∈ theoremOneBoundaryPrimes k z₁ p
          (chainScale y (p :: ps)),
          chainSiftedCount M k (q :: p :: ps) q := by
    apply Finset.sum_congr rfl
    intro q hq
    have hqSift : q ∈ siftingPrimes k p :=
      (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1
    rw [conditionedSiftedCountOn_siftingPrimes_eq _ _ hqSift]
    rfl
  rw [hinterior, hboundary] at hdepth
  simpa only [chainSiftedCount] using hdepth

/-- The current upper cutoff at a node of the Theorem 1 recursion. -/
def chainCutoff (z : ℝ) : List ℕ → ℝ
  | [] => z
  | p :: _ => p

/-- The exact finite recursive expansion generated by the proof of Theorem 1.
At positive depth it replaces every interior terminal count by `(2.4)`;
boundary counts are terminal and are not expanded. -/
noncomputable def theoremOneRecursiveExpansion
    (M : Finset ℕ) (k : ℕ) (z₁ z y : ℝ) (ps : List ℕ) : ℕ → ℝ
  | 0 => chainSiftedCount M k ps (chainCutoff z ps)
  | r + 1 =>
      chainSiftedCount M k ps z₁ -
        ∑ q ∈ theoremOneInteriorPrimes k z₁ (chainCutoff z ps)
            (chainScale y ps),
          theoremOneRecursiveExpansion M k z₁ z y (q :: ps) r -
        ∑ q ∈ theoremOneBoundaryPrimes k z₁ (chainCutoff z ps)
            (chainScale y ps),
          chainSiftedCount M k (q :: ps) q

/-- A prime in the initial interior range is an explicit one-prime interior
chain. -/
theorem theoremOneInteriorChain_singleton_of_mem
    {k q : ℕ} {z₁ z y : ℝ}
    (hq : q ∈ theoremOneInteriorPrimes k z₁ z y) :
    theoremOneInteriorChain k z₁ z y [q] := by
  rw [theoremOneInteriorPrimes, Finset.mem_filter,
    Finset.mem_filter] at hq
  rcases hq with ⟨⟨hqSift, hz₁q⟩, hqInterior⟩
  rcases mem_siftingPrimes.mp hqSift with ⟨hqPrime, hqz, hqk⟩
  refine ⟨hqPrime, hz₁q, hqz, hqk, ?_, ?_, trivial⟩
  · simp
  · simpa only [chainScale] using hqInterior

/-- A prime in the initial boundary range is an explicit one-prime boundary
chain. -/
theorem theoremOneBoundaryChain_singleton_of_mem
    {k q : ℕ} {z₁ z y : ℝ}
    (hq : q ∈ theoremOneBoundaryPrimes k z₁ z y) :
    theoremOneBoundaryChain k z₁ z y [q] := by
  rw [theoremOneBoundaryPrimes, Finset.mem_filter,
    Finset.mem_filter] at hq
  rcases hq with ⟨⟨hqSift, hz₁q⟩, hqBoundary, hqUpper⟩
  rcases mem_siftingPrimes.mp hqSift with ⟨hqPrime, hqz, hqk⟩
  refine ⟨hqPrime, hz₁q, hqz, hqk, ?_, ?_, ?_, trivial⟩
  · simp
  · simpa only [chainScale] using hqBoundary
  · simpa only [chainScale] using hqUpper

/-- Formula `(2.4)` with its conditioned terms written as the one-prime
chains that seed the finite Theorem 1 recursion. -/
theorem siftedCount_eq_at_z₁_sub_chain_extensions
    (M : Finset ℕ) (k : ℕ) {z₁ z y : ℝ}
    (hz₁ : 2 ≤ z₁) (hz : z₁ ≤ z) (hzy : z ≤ Real.sqrt y) :
    siftedCount M k z =
      siftedCount M k z₁ -
        ∑ q ∈ theoremOneInteriorPrimes k z₁ z y,
          chainSiftedCount M k [q] q -
        ∑ q ∈ theoremOneBoundaryPrimes k z₁ z y,
          chainSiftedCount M k [q] q := by
  have hdepth :=
    siftedCount_theoremOne_depthOne M k hz₁ hz hzy
  have hinterior :
      ∑ q ∈ theoremOneInteriorPrimes k z₁ z y,
          conditionedSiftedCountOn M (siftingPrimes k z) q =
        ∑ q ∈ theoremOneInteriorPrimes k z₁ z y,
          chainSiftedCount M k [q] q := by
    apply Finset.sum_congr rfl
    intro q hq
    have hqSift : q ∈ siftingPrimes k z :=
      (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1
    rw [conditionedSiftedCountOn_siftingPrimes_eq _ _ hqSift]
    rfl
  have hboundary :
      ∑ q ∈ theoremOneBoundaryPrimes k z₁ z y,
          conditionedSiftedCountOn M (siftingPrimes k z) q =
        ∑ q ∈ theoremOneBoundaryPrimes k z₁ z y,
          chainSiftedCount M k [q] q := by
    apply Finset.sum_congr rfl
    intro q hq
    have hqSift : q ∈ siftingPrimes k z :=
      (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1
    rw [conditionedSiftedCountOn_siftingPrimes_eq _ _ hqSift]
    rfl
  rwa [hinterior, hboundary] at hdepth

/-- Every explicit interior chain admits the exact recursive expansion at
every finite depth.  This is the arbitrary-depth induction statement before
flattening the nested sums into the four alternating sums of `(2.1)`. -/
theorem chainSiftedCount_eq_recursiveExpansion
    (M : Finset ℕ) (k p : ℕ) (ps : List ℕ) {z₁ z y : ℝ}
    (hz₁ : 2 ≤ z₁)
    (hchain : theoremOneInteriorChain k z₁ z y (p :: ps))
    (r : ℕ) :
    chainSiftedCount M k (p :: ps) p =
      theoremOneRecursiveExpansion M k z₁ z y (p :: ps) r := by
  induction r generalizing p ps with
  | zero => rfl
  | succ r ih =>
      have hinterior :
          ∑ q ∈ theoremOneInteriorPrimes k z₁ p
              (chainScale y (p :: ps)),
              chainSiftedCount M k (q :: p :: ps) q =
            ∑ q ∈ theoremOneInteriorPrimes k z₁ p
              (chainScale y (p :: ps)),
              theoremOneRecursiveExpansion M k z₁ z y
                (q :: p :: ps) r := by
        apply Finset.sum_congr rfl
        intro q hq
        exact
          ih q (p :: ps)
            (theoremOneInteriorChain_cons_of_mem hchain hq)
      rw [theoremOneRecursiveExpansion]
      simp only [chainCutoff]
      rw [← hinterior]
      exact
        chainSiftedCount_eq_at_z₁_sub_extensions
          M k p ps hz₁ hchain

/-- The concrete count has the exact nested Theorem 1 expansion at every
positive finite depth.  The recursion ranges only over explicit chains
`pᵢ < ... < p₁`, with all interior and boundary inequalities enforced by the
prime carriers and preserved by the chain lemmas above. -/
theorem siftedCount_eq_theoremOneRecursiveExpansion
    (M : Finset ℕ) (k : ℕ) {z₁ z y : ℝ}
    (hz₁ : 2 ≤ z₁) (hz : z₁ ≤ z) (hzy : z ≤ Real.sqrt y)
    (r : ℕ) :
    siftedCount M k z =
      theoremOneRecursiveExpansion M k z₁ z y [] (r + 1) := by
  have hinterior :
      ∑ q ∈ theoremOneInteriorPrimes k z₁ z y,
          chainSiftedCount M k [q] q =
        ∑ q ∈ theoremOneInteriorPrimes k z₁ z y,
          theoremOneRecursiveExpansion M k z₁ z y [q] r := by
    apply Finset.sum_congr rfl
    intro q hq
    exact
      chainSiftedCount_eq_recursiveExpansion M k q [] hz₁
        (theoremOneInteriorChain_singleton_of_mem hq) r
  rw [theoremOneRecursiveExpansion]
  simp only [chainCutoff, chainScale, chainSiftedCount, conditionedCarrier]
  rw [← hinterior]
  exact siftedCount_eq_at_z₁_sub_chain_extensions M k hz₁ hz hzy

/-- The sum over all interior extensions of `ps` by exactly `i` primes,
evaluated at the common cutoff `u`.  Its nested finite sums are the explicit
prime-chain sum `pᵢ < ... < p₁` in `(2.1)`. -/
noncomputable def theoremOneInteriorDepthSum
    (M : Finset ℕ) (k : ℕ) (z₁ z y : ℝ) (ps : List ℕ) (u : ℝ) : ℕ → ℝ
  | 0 => chainSiftedCount M k ps u
  | i + 1 =>
      ∑ q ∈ theoremOneInteriorPrimes k z₁ (chainCutoff z ps)
          (chainScale y ps),
        theoremOneInteriorDepthSum M k z₁ z y (q :: ps) u i

/-- The sum over the interior chains obtained from `ps` at exact depth `i`,
with each terminal count evaluated at its newest prime. -/
noncomputable def theoremOneTerminalDepthSum
    (M : Finset ℕ) (k : ℕ) (z₁ z y : ℝ) (ps : List ℕ) : ℕ → ℝ
  | 0 => chainSiftedCount M k ps (chainCutoff z ps)
  | i + 1 =>
      ∑ q ∈ theoremOneInteriorPrimes k z₁ (chainCutoff z ps)
          (chainScale y ps),
        theoremOneTerminalDepthSum M k z₁ z y (q :: ps) i

/-- The sum over exact-depth boundary chains extending `ps`.  The final prime
is in the boundary range; all earlier primes are in the interior range. -/
noncomputable def theoremOneBoundaryDepthSum
    (M : Finset ℕ) (k : ℕ) (z₁ z y : ℝ) (ps : List ℕ) : ℕ → ℝ
  | 0 => 0
  | 1 =>
      ∑ q ∈ theoremOneBoundaryPrimes k z₁ (chainCutoff z ps)
          (chainScale y ps),
        chainSiftedCount M k (q :: ps) q
  | i + 2 =>
      ∑ q ∈ theoremOneInteriorPrimes k z₁ (chainCutoff z ps)
          (chainScale y ps),
        theoremOneBoundaryDepthSum M k z₁ z y (q :: ps) (i + 1)

/-- The signed sum of the common-`z₁` interior terms at depths `0,...,r-1`. -/
noncomputable def theoremOneInteriorCumulative
    (M : Finset ℕ) (k : ℕ) (z₁ z y : ℝ) (ps : List ℕ) (r : ℕ) : ℝ :=
  ∑ i ∈ Finset.range r,
    (-1 : ℝ) ^ i * theoremOneInteriorDepthSum M k z₁ z y ps z₁ i

/-- The signed sum of boundary terms at depths `1,...,r`. -/
noncomputable def theoremOneBoundaryCumulative
    (M : Finset ℕ) (k : ℕ) (z₁ z y : ℝ) (ps : List ℕ) (r : ℕ) : ℝ :=
  ∑ i ∈ Finset.range r,
    (-1 : ℝ) ^ (i + 1) *
      theoremOneBoundaryDepthSum M k z₁ z y ps (i + 1)

/-- Pulling the first prime out of the signed interior-depth sum. -/
theorem theoremOneInteriorCumulative_succ
    (M : Finset ℕ) (k : ℕ) (z₁ z y : ℝ) (ps : List ℕ) (r : ℕ) :
    theoremOneInteriorCumulative M k z₁ z y ps (r + 1) =
      chainSiftedCount M k ps z₁ -
        ∑ q ∈ theoremOneInteriorPrimes k z₁ (chainCutoff z ps)
            (chainScale y ps),
          theoremOneInteriorCumulative M k z₁ z y (q :: ps) r := by
  induction r with
  | zero =>
      simp [theoremOneInteriorCumulative, theoremOneInteriorDepthSum]
  | succ r ih =>
      have hstep (as : List ℕ) :
          theoremOneInteriorCumulative M k z₁ z y as (r + 1) =
            theoremOneInteriorCumulative M k z₁ z y as r +
              (-1 : ℝ) ^ r *
                theoremOneInteriorDepthSum M k z₁ z y as z₁ r := by
        simp [theoremOneInteriorCumulative, Finset.sum_range_succ]
      have houter :
          theoremOneInteriorCumulative M k z₁ z y ps (r + 1 + 1) =
            theoremOneInteriorCumulative M k z₁ z y ps (r + 1) +
              (-1 : ℝ) ^ (r + 1) *
                theoremOneInteriorDepthSum M k z₁ z y ps z₁ (r + 1) := by
        simp [theoremOneInteriorCumulative, Finset.sum_range_succ]
      rw [houter]
      simp only [theoremOneInteriorDepthSum]
      rw [ih]
      simp_rw [hstep]
      simp only [Finset.sum_add_distrib, Finset.mul_sum]
      rw [pow_succ]
      simp only [mul_neg, mul_one, neg_mul]
      rw [Finset.sum_neg_distrib]
      ring

/-- Pulling the first prime out of the signed boundary-depth sum. -/
theorem theoremOneBoundaryCumulative_succ
    (M : Finset ℕ) (k : ℕ) (z₁ z y : ℝ) (ps : List ℕ) (r : ℕ) :
    theoremOneBoundaryCumulative M k z₁ z y ps (r + 1) =
      -∑ q ∈ theoremOneBoundaryPrimes k z₁ (chainCutoff z ps)
          (chainScale y ps),
          chainSiftedCount M k (q :: ps) q -
        ∑ q ∈ theoremOneInteriorPrimes k z₁ (chainCutoff z ps)
            (chainScale y ps),
          theoremOneBoundaryCumulative M k z₁ z y (q :: ps) r := by
  induction r with
  | zero =>
      simp [theoremOneBoundaryCumulative, theoremOneBoundaryDepthSum]
  | succ r ih =>
      have hstep (as : List ℕ) :
          theoremOneBoundaryCumulative M k z₁ z y as (r + 1) =
            theoremOneBoundaryCumulative M k z₁ z y as r +
              (-1 : ℝ) ^ (r + 1) *
                theoremOneBoundaryDepthSum M k z₁ z y as (r + 1) := by
        simp [theoremOneBoundaryCumulative, Finset.sum_range_succ]
      have houter :
          theoremOneBoundaryCumulative M k z₁ z y ps (r + 1 + 1) =
            theoremOneBoundaryCumulative M k z₁ z y ps (r + 1) +
              (-1 : ℝ) ^ (r + 1 + 1) *
                theoremOneBoundaryDepthSum M k z₁ z y ps (r + 1 + 1) := by
        simp [theoremOneBoundaryCumulative, Finset.sum_range_succ]
      rw [houter]
      rw [ih]
      simp only [theoremOneBoundaryDepthSum]
      simp_rw [hstep]
      simp only [Finset.sum_add_distrib, Finset.mul_sum]
      rw [show r + 1 + 1 = (r + 1) + 1 by omega, pow_succ]
      simp only [mul_neg, mul_one, neg_mul]
      rw [Finset.sum_neg_distrib]
      ring

/-- The nested recursion is exactly the sum of its signed interior levels, its
last interior level, and all boundary levels. -/
theorem theoremOneRecursiveExpansion_eq_alternatingDepthSums
    (M : Finset ℕ) (k : ℕ) (z₁ z y : ℝ) (ps : List ℕ) (r : ℕ) :
    theoremOneRecursiveExpansion M k z₁ z y ps r =
      theoremOneInteriorCumulative M k z₁ z y ps r +
        (-1 : ℝ) ^ r * theoremOneTerminalDepthSum M k z₁ z y ps r +
        theoremOneBoundaryCumulative M k z₁ z y ps r := by
  induction r generalizing ps with
  | zero =>
      simp [theoremOneRecursiveExpansion, theoremOneInteriorCumulative,
        theoremOneTerminalDepthSum, theoremOneBoundaryCumulative]
  | succ r ih =>
      have hexpand :
          ∑ q ∈ theoremOneInteriorPrimes k z₁ (chainCutoff z ps)
              (chainScale y ps),
              theoremOneRecursiveExpansion M k z₁ z y (q :: ps) r =
            ∑ q ∈ theoremOneInteriorPrimes k z₁ (chainCutoff z ps)
              (chainScale y ps),
              (theoremOneInteriorCumulative M k z₁ z y (q :: ps) r +
                (-1 : ℝ) ^ r *
                  theoremOneTerminalDepthSum M k z₁ z y (q :: ps) r +
                theoremOneBoundaryCumulative M k z₁ z y (q :: ps) r) := by
        apply Finset.sum_congr rfl
        intro q hq
        exact ih (q :: ps)
      rw [theoremOneRecursiveExpansion, hexpand,
        theoremOneInteriorCumulative_succ,
        theoremOneBoundaryCumulative_succ]
      simp only [theoremOneTerminalDepthSum, Finset.sum_add_distrib,
        Finset.mul_sum]
      rw [pow_succ]
      simp only [mul_neg, mul_one, neg_mul]
      rw [Finset.sum_neg_distrib]
      ring

/-- The four finite sums displayed in Jurkat--Richert formula `(2.1)`.

The first term is `A_k(M;z₁)`.  The first sum has depths `1 ≤ i < r` and
common cutoff `z₁`; the next term is the exact depth-`r` interior sum with
cutoff `pᵣ`; and the last sum has boundary depths `1 ≤ i ≤ r`.  In the two
outer sums, `i + 1` is the displayed one-based depth.  The recursively defined
inner sums range only over the explicit prime chains enforced by
`theoremOneInteriorPrimes` and `theoremOneBoundaryPrimes`. -/
theorem siftedCount_eq_theoremOneFourSums
    (M : Finset ℕ) (k : ℕ) {z₁ z y : ℝ}
    (hz₁ : 2 ≤ z₁) (hz : z₁ ≤ z) (hzy : z ≤ Real.sqrt y)
    (r : ℕ) (hr : 0 < r) :
    siftedCount M k z =
      siftedCount M k z₁ +
        ∑ i ∈ Finset.range (r - 1),
          (-1 : ℝ) ^ (i + 1) *
            theoremOneInteriorDepthSum M k z₁ z y [] z₁ (i + 1) +
        (-1 : ℝ) ^ r *
          theoremOneTerminalDepthSum M k z₁ z y [] r +
        ∑ i ∈ Finset.range r,
          (-1 : ℝ) ^ (i + 1) *
            theoremOneBoundaryDepthSum M k z₁ z y [] (i + 1) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr)
  rw [siftedCount_eq_theoremOneRecursiveExpansion M k hz₁ hz hzy r,
    theoremOneRecursiveExpansion_eq_alternatingDepthSums]
  simp only [theoremOneInteriorCumulative, Finset.sum_range_succ',
    theoremOneInteriorDepthSum, theoremOneBoundaryCumulative,
    chainSiftedCount, conditionedCarrier, Nat.succ_sub_one,
    pow_succ, mul_neg, mul_one, neg_mul]
  ring

/-- A literal `H_k(M)` source: `M` consists of positive integers and every
coprime divisor count differs from `y / d` by at most one. -/
structure RegularSource where
  carrier : Finset ℕ
  zero_not_mem : 0 ∉ carrier
  k : ℕ
  k_pos : 0 < k
  y : ℝ
  one_lt_y : 1 < y
  regular :
    ∀ d : ℕ, 0 < d → Nat.Coprime d k →
      |(((carrier.filter fun n => d ∣ n).card : ℝ) - y / d)| ≤ 1

/-- Jurkat--Richert's literal finite quotient set
`M_d = {m | m * d ∈ M}`. -/
def literalQuotientCarrier (M : Finset ℕ) (d : ℕ) : Finset ℕ :=
  (M.filter fun n => d ∣ n).image fun n => n / d

/-- The quotient-set definition has the paper's literal membership
condition when `d` is positive. -/
theorem mem_literalQuotientCarrier
    (M : Finset ℕ) {d m : ℕ} (hd : 0 < d) :
    m ∈ literalQuotientCarrier M d ↔ m * d ∈ M := by
  simp only [literalQuotientCarrier, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨n, ⟨hnM, hdn⟩, rfl⟩
    rwa [Nat.div_mul_cancel hdn]
  · intro hm
    refine
      ⟨m * d, ⟨hm, ⟨m, by simp [Nat.mul_comm]⟩⟩,
        Nat.mul_div_cancel m hd⟩

/-- Division by `d` is the exact bijection from the original-element
divisibility fibre to the literal quotient carrier. -/
theorem literalQuotientCarrier_bijOn
    (M : Finset ℕ) {d : ℕ} (hd : 0 < d) :
    Set.BijOn (fun n => n / d) ↑(M.filter fun n => d ∣ n)
      ↑(literalQuotientCarrier M d) := by
  refine ⟨?_, ?_, ?_⟩
  · intro n hn
    apply (mem_literalQuotientCarrier M hd).2
    rw [Nat.div_mul_cancel (Finset.mem_filter.mp hn).2]
    exact (Finset.mem_filter.mp hn).1
  · intro a ha b hb hab
    have hda : d ∣ a := (Finset.mem_filter.mp ha).2
    have hdb : d ∣ b := (Finset.mem_filter.mp hb).2
    change a / d = b / d at hab
    calc
      a = a / d * d := (Nat.div_mul_cancel hda).symm
      _ = b / d * d := by rw [hab]
      _ = b := Nat.div_mul_cancel hdb
  · intro m hm
    rcases Finset.mem_image.mp hm with ⟨n, hn, rfl⟩
    exact ⟨n, hn, rfl⟩

/-- The literal quotient carrier and the original divisibility fibre have
the same cardinality. -/
theorem card_literalQuotientCarrier
    (M : Finset ℕ) {d : ℕ} (hd : 0 < d) :
    (literalQuotientCarrier M d).card =
      (M.filter fun n => d ∣ n).card := by
  exact Finset.card_image_iff.mpr
    (literalQuotientCarrier_bijOn M hd).injOn

/-- Divisibility by `e` in the literal quotient is divisibility by `d * e`
in the original source. -/
theorem card_filter_literalQuotientCarrier
    (M : Finset ℕ) {d e : ℕ} (hd : 0 < d) :
    ((literalQuotientCarrier M d).filter fun m => e ∣ m).card =
      (M.filter fun n => d * e ∣ n).card := by
  have hfilter :
      (literalQuotientCarrier M d).filter (fun m => e ∣ m) =
        literalQuotientCarrier (M.filter fun n => d * e ∣ n) d := by
    ext m
    rw [Finset.mem_filter, mem_literalQuotientCarrier M hd,
      mem_literalQuotientCarrier (M.filter fun n => d * e ∣ n) hd,
      Finset.mem_filter]
    have hcancel : d * e ∣ m * d ↔ e ∣ m := by
      rw [Nat.mul_comm m d]
      exact Nat.mul_dvd_mul_iff_left hd
    tauto
  rw [hfilter, card_literalQuotientCarrier _ hd]
  apply congrArg Finset.card
  ext n
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨⟨hnM, hde⟩, -⟩
    exact ⟨hnM, hde⟩
  · rintro ⟨hnM, hde⟩
    exact ⟨⟨hnM, hde⟩, dvd_of_mul_right_dvd hde⟩

/-- A regular source remains regular after literal quotienting: its new
scale is `y / d`, its excluded modulus is `k * d`, and regularity at `e`
is inherited from the original divisor `d * e`. -/
noncomputable def RegularSource.literalQuotient
    (source : RegularSource) (d : ℕ) (hd : 0 < d)
    (hdk : Nat.Coprime d source.k) (hdy : (d : ℝ) < source.y) :
    RegularSource where
  carrier := literalQuotientCarrier source.carrier d
  zero_not_mem := by
    intro hzero
    apply source.zero_not_mem
    simpa using
      (mem_literalQuotientCarrier source.carrier hd).mp hzero
  k := source.k * d
  k_pos := Nat.mul_pos source.k_pos hd
  y := source.y / d
  one_lt_y := (one_lt_div₀ (by exact_mod_cast hd)).2 hdy
  regular := by
    intro e he hekd
    have hek : Nat.Coprime e source.k :=
      (Nat.coprime_mul_iff_right.mp hekd).1
    have hdek : Nat.Coprime (d * e) source.k := hdk.mul_left hek
    rw [card_filter_literalQuotientCarrier source.carrier hd]
    simpa only [Nat.cast_mul, div_div] using
      source.regular (d * e) (Nat.mul_pos hd he) hdek

/-- Below every prime divisor of `d`, quotienting and adding `d` to the
excluded modulus preserves the existing divisibility-fibre sifted count. -/
theorem siftedCount_literalQuotientCarrier_eq_divisibilityFiber
    (M : Finset ℕ) (k d : ℕ) (z : ℝ) (hd : 0 < d)
    (hz : ∀ p : ℕ, p.Prime → p ∣ d → z ≤ (p : ℝ)) :
    siftedCount (literalQuotientCarrier M d) (k * d) z =
      siftedCount (M.filter fun n => d ∣ n) k z := by
  have hprimes : siftingPrimes (k * d) z = siftingPrimes k z := by
    ext p
    rw [mem_siftingPrimes, mem_siftingPrimes]
    constructor
    · rintro ⟨hpPrime, hpz, hpkd⟩
      exact
        ⟨hpPrime, hpz,
          fun hpk => hpkd (dvd_mul_of_dvd_left hpk d)⟩
    · rintro ⟨hpPrime, hpz, hpk⟩
      refine ⟨hpPrime, hpz, ?_⟩
      intro hpkd
      rcases hpPrime.dvd_mul.mp hpkd with hpk' | hpd
      · exact hpk hpk'
      · exact (not_lt_of_ge (hz p hpPrime hpd)) hpz
  let P := siftingPrimes k z
  have hPd : Nat.Coprime (P.prod id) d := by
    rw [Nat.coprime_prod_left_iff]
    intro p hp
    change Nat.Coprime p d
    rw [(mem_siftingPrimes.mp hp).1.coprime_iff_not_dvd]
    intro hpd
    exact
      (not_lt_of_ge (hz p (mem_siftingPrimes.mp hp).1 hpd))
        (mem_siftingPrimes.mp hp).2.1
  have hfilter :
      (literalQuotientCarrier M d).filter
          (fun m => Nat.Coprime (P.prod id) m) =
        ((M.filter fun n => d ∣ n).filter
          (fun n => Nat.Coprime (P.prod id) n)).image (fun n => n / d) := by
    rw [literalQuotientCarrier, Finset.filter_image]
    congr 1
    ext n
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hn, hcop⟩
      refine ⟨hn, ?_⟩
      rw [← Nat.div_mul_cancel hn.2, Nat.coprime_mul_iff_right]
      exact ⟨hcop, hPd⟩
    · rintro ⟨hn, hcop⟩
      refine ⟨hn, ?_⟩
      rw [← Nat.div_mul_cancel hn.2, Nat.coprime_mul_iff_right] at hcop
      exact hcop.1
  unfold siftedCount
  rw [hprimes]
  change
    (((literalQuotientCarrier M d).filter
      (fun m => Nat.Coprime (P.prod id) m)).card : ℝ) = _
  rw [hfilter]
  congr 1
  exact Finset.card_image_iff.mpr fun a ha b hb hab =>
    (literalQuotientCarrier_bijOn M hd).injOn
      (Finset.mem_filter.mp ha).1 (Finset.mem_filter.mp hb).1 hab

/-- A product of distinct primes is squarefree. -/
private theorem squarefree_prod_of_primes
    {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) :
    Squarefree (s.prod id) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      have haPrime : a.Prime := hs a (by simp [ha])
      have hcoprime : a.Coprime (s.prod id) := by
        rw [haPrime.coprime_iff_not_dvd]
        intro hadvd
        have hprodNe : s.prod id ≠ 0 :=
          Finset.prod_ne_zero_iff.mpr
            (fun p hp => (hs p (by simp [hp])).ne_zero)
        have hamem : a ∈ (s.prod id).primeFactors :=
          (Nat.mem_primeFactors.mpr ⟨haPrime, hadvd, hprodNe⟩)
        have hprimeFactors :
            (s.prod id).primeFactors = s :=
          Nat.primeFactors_prod (fun p hp => hs p (by simp [hp]))
        rw [hprimeFactors] at hamem
        exact ha hamem
      rw [Finset.prod_insert ha]
      simpa only [id_eq] using
        (Nat.squarefree_mul hcoprime).2
          ⟨haPrime.squarefree,
            ih (fun p hp => hs p (by simp [hp]))⟩

/-- The Euler product over any finite prime carrier is its product's exact
totient ratio. -/
theorem prod_one_sub_localDensity_eq_totient_div_prod
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    (∏ p ∈ s, (1 - localDensity p)) =
      (Nat.totient (s.prod id) : ℝ) / (s.prod id : ℕ) := by
  have hsq := squarefree_prod_of_primes hs
  have hpf : (s.prod id).primeFactors = s :=
    Nat.primeFactors_prod hs
  have htotient :
      (∏ p ∈ s, ((p : ℝ) - 1)) =
        (Nat.totient (s.prod id) : ℝ) := by
    rw [AnalyticNumberTheory.Sieve.totient_eq_prod_primeFactors_of_squarefree hsq,
      hpf]
    push_cast
    apply Finset.prod_congr rfl
    intro p hp
    rw [Nat.cast_sub (hs p hp).one_le]
    norm_num
  have hproduct :
      (∏ p ∈ s, (p : ℝ)) = (s.prod id : ℕ) := by
    rw [← Nat.cast_prod (R := ℝ) (fun p : ℕ => p) s]
    rfl
  calc
    (∏ p ∈ s, (1 - localDensity p)) =
        ∏ p ∈ s, ((p : ℝ) - 1) / (p : ℝ) := by
      apply Finset.prod_congr rfl
      intro p hp
      have hp0 : (p : ℝ) ≠ 0 := by
        exact_mod_cast (hs p hp).ne_zero
      unfold localDensity
      field_simp [hp0]
    _ = (∏ p ∈ s, ((p : ℝ) - 1)) /
        ∏ p ∈ s, (p : ℝ) := by
      rw [Finset.prod_div_distrib]
    _ = (Nat.totient (s.prod id) : ℝ) / (s.prod id : ℕ) := by
      rw [htotient, hproduct]

/-- The completely multiplicative reciprocal used in the geometric Euler
products behind Lemma 3.1 `(3.3)`. -/
noncomputable def natReciprocalMonoidHom : ℕ →* ℝ where
  toFun n := ((n : ℝ))⁻¹
  map_one' := by norm_num
  map_mul' m n := by
    push_cast
    rw [mul_inv]

@[simp]
theorem natReciprocalMonoidHom_apply (n : ℕ) :
    natReciprocalMonoidHom n = 1 / (n : ℝ) := by
  simp [natReciprocalMonoidHom, one_div]

private theorem dvd_of_radical_eq
    {n q : ℕ}
    (h : UniqueFactorizationMonoid.radical n = q) :
    q ∣ n := by
  rw [← h]
  exact UniqueFactorizationMonoid.radical_dvd_self

/-- For a positive integer with squarefree kernel `q`, division by `q`
injects its fiber into the positive integers factored over the primes of
`q`.  This is the source's grouping by the largest squarefree divisor. -/
noncomputable def radicalQuotientEmbedding (q : ℕ) :
    {n : ℕ // 0 < n ∧ UniqueFactorizationMonoid.radical n = q} ↪
      Nat.factoredNumbers q.primeFactors where
  toFun n := by
    have hqDiv : q ∣ (n : ℕ) := dvd_of_radical_eq n.property.2
    refine ⟨n / q, ?_⟩
    rw [Nat.mem_factoredNumbers']
    intro p hpPrime hpDiv
    have hpMemN : p ∈ (n : ℕ).primeFactors :=
      Nat.mem_primeFactors.mpr
        ⟨hpPrime, hpDiv.trans (Nat.div_dvd_of_dvd hqDiv),
          Nat.ne_of_gt n.property.1⟩
    have hpMemRad :
        p ∈ (UniqueFactorizationMonoid.radical (n : ℕ)).primeFactors := by
      rw [Nat.primeFactors_radical]
      exact hpMemN
    exact n.property.2 ▸ hpMemRad
  inj' := by
    intro m n hmn
    apply Subtype.ext
    have hmDiv : q ∣ (m : ℕ) := dvd_of_radical_eq m.property.2
    have hnDiv : q ∣ (n : ℕ) := dvd_of_radical_eq n.property.2
    have hquot : (m : ℕ) / q = (n : ℕ) / q :=
      congrArg Subtype.val hmn
    calc
      (m : ℕ) = q * ((m : ℕ) / q) :=
        (Nat.mul_div_cancel' hmDiv).symm
      _ = q * ((n : ℕ) / q) := congrArg (q * ·) hquot
      _ = (n : ℕ) := Nat.mul_div_cancel' hnDiv

/-- The geometric-series estimate for one squarefree-kernel fiber used in
the proof of Lemma 3.1 `(3.3)`. -/
theorem sum_reciprocal_of_radical_eq_le
    {q : ℕ}
    (hq : Squarefree q)
    (s : Finset ℕ)
    (hsPos : ∀ n ∈ s, 0 < n)
    (hsRadical :
      ∀ n ∈ s, UniqueFactorizationMonoid.radical n = q) :
    ∑ n ∈ s, 1 / (n : ℝ) ≤ 1 / (Nat.totient q : ℝ) := by
  let positiveRadicalEmbedding :
      {n : ℕ // n ∈ s} ↪
        {n : ℕ // 0 < n ∧ UniqueFactorizationMonoid.radical n = q} :=
    { toFun := fun n => ⟨n, hsPos n n.property, hsRadical n n.property⟩
      inj' := fun _ _ hmn =>
        Subtype.ext
          (congrArg
            (fun x :
              {n : ℕ //
                0 < n ∧ UniqueFactorizationMonoid.radical n = q} =>
              (x : ℕ))
            hmn) }
  let quotientEmbedding :
      {n : ℕ // n ∈ s} ↪ Nat.factoredNumbers q.primeFactors :=
    positiveRadicalEmbedding.trans (radicalQuotientEmbedding q)
  have hgeometric :=
    EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric
      (f := natReciprocalMonoidHom)
      (fun {p} hp => by
        rw [natReciprocalMonoidHom_apply, one_div, norm_inv,
          Real.norm_natCast]
        apply inv_lt_one_of_one_lt₀
        exact_mod_cast hp.one_lt)
      q.primeFactors
  have hsummable :
      Summable
        (fun m : Nat.factoredNumbers q.primeFactors =>
          natReciprocalMonoidHom m) :=
    Summable.of_norm hgeometric.1
  have hprimeFactors :
      ∀ p ∈ q.primeFactors, Nat.Prime p :=
    fun p hp => Nat.prime_of_mem_primeFactors hp
  have hproduct :
      ∏ p ∈ q.primeFactors with Nat.Prime p,
          (1 - natReciprocalMonoidHom p)⁻¹ =
        (q : ℝ) / (Nat.totient q : ℝ) := by
    rw [Finset.filter_eq_self.mpr hprimeFactors]
    calc
      ∏ p ∈ q.primeFactors, (1 - natReciprocalMonoidHom p)⁻¹ =
          (∏ p ∈ q.primeFactors, (1 - localDensity p))⁻¹ := by
            simp_rw [natReciprocalMonoidHom_apply, localDensity]
            exact Finset.prod_inv_distrib _
      _ = (((Nat.totient (q.primeFactors.prod id) : ℕ) : ℝ) /
            (q.primeFactors.prod id : ℕ))⁻¹ := by
          rw [prod_one_sub_localDensity_eq_totient_div_prod
            q.primeFactors hprimeFactors]
      _ = (q : ℝ) / (Nat.totient q : ℝ) := by
          have hprodq : q.primeFactors.prod id = q := by
            simpa only [id_eq] using Nat.prod_primeFactors_of_squarefree hq
          rw [hprodq, inv_div]
  have hqPos : 0 < q := Nat.pos_of_ne_zero hq.ne_zero
  calc
    ∑ n ∈ s, 1 / (n : ℝ) =
        ∑ n ∈ s.attach, 1 / ((n : ℕ) : ℝ) :=
      (Finset.sum_attach s (fun n => 1 / (n : ℝ))).symm
    _ = ∑ n ∈ s.attach,
        (1 / (q : ℝ)) * natReciprocalMonoidHom (quotientEmbedding n) := by
      apply Finset.sum_congr rfl
      intro n hn
      have hqDiv : q ∣ (n : ℕ) :=
        dvd_of_radical_eq (hsRadical n n.property)
      simp only [natReciprocalMonoidHom_apply, one_div]
      change
        (((n : ℕ) : ℝ))⁻¹ =
          ((q : ℝ))⁻¹ * ((((n : ℕ) / q : ℕ) : ℝ))⁻¹
      rw [← mul_inv, ← Nat.cast_mul, Nat.mul_div_cancel' hqDiv]
    _ = ∑ m ∈ s.attach.map quotientEmbedding,
        (1 / (q : ℝ)) * natReciprocalMonoidHom m :=
      (Finset.sum_map s.attach quotientEmbedding
        (fun m => (1 / (q : ℝ)) * natReciprocalMonoidHom m)).symm
    _ ≤ ∑' m : Nat.factoredNumbers q.primeFactors,
        (1 / (q : ℝ)) * natReciprocalMonoidHom m :=
      ((hsummable.mul_left (1 / (q : ℝ))).sum_le_tsum
        (s.attach.map quotientEmbedding) (fun m _ => by
          apply mul_nonneg (by positivity)
          rw [natReciprocalMonoidHom_apply]
          exact one_div_nonneg.mpr (Nat.cast_nonneg m)))
    _ = (1 / (q : ℝ)) *
        (∏ p ∈ q.primeFactors with Nat.Prime p,
          (1 - natReciprocalMonoidHom p)⁻¹) := by
      rw [tsum_mul_left, hgeometric.2.tsum_eq]
    _ = 1 / (Nat.totient q : ℝ) := by
      rw [hproduct]
      have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne_zero
      have htotient0 : (Nat.totient q : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.totient_pos.mpr hqPos).ne'
      field_simp

/-- The literal `H_k(M)` source as a `BoundingSieve`, with the exact local
density `ν(d) = 1 / d` and the paper's finite prime carrier. -/
noncomputable def RegularSource.boundingSieve
    (source : RegularSource) (z : ℝ) : BoundingSieve where
  support := source.carrier
  prodPrimes := (siftingPrimes source.k z).prod id
  prodPrimes_squarefree :=
    squarefree_prod_of_primes
      (fun p hp => (mem_siftingPrimes.mp hp).1)
  weights := fun _ => 1
  weights_nonneg := by intro n; norm_num
  totalMass := source.y
  nu := (ζ : ArithmeticFunction ℝ).pdiv .id
  nu_mult := by arith_mult
  nu_pos_of_prime := fun p hp _ => by
    simp [if_neg hp.ne_zero, Nat.pos_of_ne_zero hp.ne_zero]
  nu_lt_one_of_prime := fun p hp _ => by
    simp only [ArithmeticFunction.pdiv_apply,
      ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply,
      hp.ne_zero, ↓reduceIte, Nat.cast_one, ArithmeticFunction.id_apply,
      one_div]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)

/-- The local density of the literal source sieve is exactly `1 / d` away
from `d = 0`. -/
theorem RegularSource.boundingSieve_nu_apply
    (source : RegularSource) (z : ℝ) {d : ℕ} (hd : 0 < d) :
    (source.boundingSieve z).nu d = 1 / (d : ℝ) := by
  simp [RegularSource.boundingSieve, ArithmeticFunction.pdiv_apply,
    Nat.ne_of_gt hd]

/-- The sifted sum of the literal source `BoundingSieve` is the concrete
cardinality `A_k(M; z)`, not a coefficient-density surrogate. -/
theorem RegularSource.boundingSieve_siftedSum_eq
    (source : RegularSource) (z : ℝ) :
    (source.boundingSieve z).siftedSum =
      siftedCount source.carrier source.k z := by
  change
    (∑ n ∈ source.carrier,
      if Nat.Coprime ((siftingPrimes source.k z).prod id) n
      then (1 : ℝ) else 0) =
      (((source.carrier.filter fun n =>
        Nat.Coprime ((siftingPrimes source.k z).prod id) n).card : ℕ) : ℝ)
  rw [Finset.sum_boole]

/-- The Euler product of the literal source `BoundingSieve` is exactly the
paper's `R_k(z)`. -/
theorem RegularSource.boundingSieve_sieveProduct_eq
    (source : RegularSource) (z : ℝ) :
    AnalyticNumberTheory.Sieve.sieveProductPrimeFactors
        (source.boundingSieve z) =
      sieveProduct source.k z := by
  have hprimeFactors :
      ((siftingPrimes source.k z).prod id).primeFactors =
        siftingPrimes source.k z :=
    Nat.primeFactors_prod
      (fun p hp => (mem_siftingPrimes.mp hp).1)
  change
    (∏ p ∈ ((siftingPrimes source.k z).prod id).primeFactors,
      (1 - ((ζ : ArithmeticFunction ℝ).pdiv .id) p)) =
      ∏ p ∈ siftingPrimes source.k z, (1 - localDensity p)
  rw [hprimeFactors]
  apply Finset.prod_congr rfl
  intro p hp
  have hpPrime := (mem_siftingPrimes.mp hp).1
  simp [ArithmeticFunction.pdiv_apply, hpPrime.ne_zero, localDensity]

/-- At one selected prime, the source Selberg denominator has the literal
local factor `1 / (p - 1)` occurring in `S_k(xi, z)`. -/
theorem RegularSource.boundingSieve_selbergTerm_prime
    (source : RegularSource) (z : ℝ) {p : ℕ} (hp : p.Prime) :
    (source.boundingSieve z).selbergTerms p =
      1 / ((p : ℝ) - 1) := by
  rw [AnalyticNumberTheory.Sieve.selbergTerm_prime hp,
    source.boundingSieve_nu_apply z hp.pos]
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hp1 : (p : ℝ) - 1 ≠ 0 :=
    sub_ne_zero.mpr (ne_of_gt (by exact_mod_cast hp.one_lt))
  field_simp

/-- On every divisor of the literal sifting product, the complete Selberg
denominator term is exactly the reciprocal totient appearing in the paper's
`S_k(xi, z)`. -/
theorem RegularSource.boundingSieve_selbergTerm_of_dvd
    (source : RegularSource) (z : ℝ) {d : ℕ}
    (hd : d ∣ (siftingPrimes source.k z).prod id) :
    (source.boundingSieve z).selbergTerms d =
      1 / (Nat.totient d : ℝ) := by
  have hsq : Squarefree d :=
    (source.boundingSieve z).prodPrimes_squarefree.squarefree_of_dvd hd
  calc
    (source.boundingSieve z).selbergTerms d =
        ∏ p ∈ d.primeFactors,
          (source.boundingSieve z).selbergTerms p :=
      (BoundingSieve.selbergTerms_isMultiplicative.prod_primeFactors hsq).symm
    _ = ∏ p ∈ d.primeFactors, 1 / ((p : ℝ) - 1) := by
      apply Finset.prod_congr rfl
      intro p hp
      exact
        source.boundingSieve_selbergTerm_prime z
          (Nat.prime_of_mem_primeFactors hp)
    _ = 1 / ∏ p ∈ d.primeFactors, ((p : ℝ) - 1) := by
      simp only [one_div, Finset.prod_inv_distrib]
    _ = 1 / (Nat.totient d : ℝ) := by
      congr 1
      rw [AnalyticNumberTheory.Sieve.totient_eq_prod_primeFactors_of_squarefree hsq]
      push_cast
      apply Finset.prod_congr rfl
      intro p hp
      rw [Nat.cast_sub (Nat.prime_of_mem_primeFactors hp).one_le]
      norm_num

/-- Every divisor of the paper's sifting product is coprime to the excluded
modulus `k`. -/
theorem coprime_of_dvd_siftingPrimes_prod
    {k d : ℕ} {z : ℝ}
    (hd : d ∣ (siftingPrimes k z).prod id) :
    Nat.Coprime d k := by
  apply Nat.Coprime.of_dvd_left hd
  rw [Nat.coprime_prod_left_iff]
  intro p hp
  have hpData := mem_siftingPrimes.mp hp
  exact hpData.1.coprime_iff_not_dvd.mpr hpData.2.2

/-- If `d` divides the literal sifting product, adjoining `d` to the excluded
modulus removes exactly the prime factors of `d` from the finite prime
carrier. -/
theorem siftingPrimes_mul_eq_sdiff_primeFactors
    {k d : ℕ} {z : ℝ}
    (hd : d ∣ (siftingPrimes k z).prod id) :
    siftingPrimes (k * d) z =
      siftingPrimes k z \ d.primeFactors := by
  have hprodPos : 0 < (siftingPrimes k z).prod id :=
    Finset.prod_pos (fun p hp => (mem_siftingPrimes.mp hp).1.pos)
  have hd0 : d ≠ 0 :=
    Nat.ne_of_gt (Nat.pos_of_dvd_of_pos hd hprodPos)
  ext p
  rw [mem_siftingPrimes, Finset.mem_sdiff, mem_siftingPrimes,
    Nat.mem_primeFactors]
  constructor
  · rintro ⟨hpPrime, hpz, hpkd⟩
    refine ⟨⟨hpPrime, hpz, ?_⟩, ?_⟩
    · intro hpk
      exact hpkd (dvd_mul_of_dvd_left hpk d)
    · rintro ⟨-, hpd, -⟩
      exact hpkd (hpPrime.dvd_mul.mpr (Or.inr hpd))
  · rintro ⟨⟨hpPrime, hpz, hpk⟩, hpdMem⟩
    refine ⟨hpPrime, hpz, ?_⟩
    intro hpkd
    rcases hpPrime.dvd_mul.mp hpkd with hpk' | hpd
    · exact hpk hpk'
    · exact hpdMem ⟨hpPrime, hpd, hd0⟩

/-- Excluding the squarefree omitted-prime factor is the same as excluding
the original modulus `k` from the prime carrier below `z`. -/
theorem siftingPrimes_excludedSiftingFactor
    (k : ℕ) (z : ℝ) :
    siftingPrimes (excludedSiftingFactor k z) z =
      siftingPrimes k z := by
  rw [← one_mul (excludedSiftingFactor k z),
    siftingPrimes_mul_eq_sdiff_primeFactors
      (excludedSiftingFactor_dvd_siftingPrimes_one k z),
    excludedSiftingFactor_primeFactors]
  ext p
  simp only [Finset.mem_sdiff, excludedSiftingPrimes,
    Finset.mem_filter, mem_siftingPrimes]
  constructor
  · rintro ⟨⟨hp, hpz, hp1⟩, hpFilter⟩
    refine ⟨hp, hpz, ?_⟩
    intro hpk
    exact hpFilter ⟨⟨hp, hpz, hp1⟩, hpk⟩
  · rintro ⟨hp, hpz, hpk⟩
    refine ⟨⟨hp, hpz, ?_⟩, ?_⟩
    · intro hp1
      exact hp.ne_one (Nat.dvd_one.mp hp1)
    · intro hpFilter
      exact hpk hpFilter.2

/-- The Euler ratio in Lemma 3.1 `(3.2)`: restoring the primes omitted by
`k` multiplies `R_k(z)` by `phi(d) / d`, where `d` is their squarefree
product. -/
theorem sieveProduct_one_eq_mul_excludedFactor
    (k : ℕ) (z : ℝ) :
    sieveProduct 1 z =
      sieveProduct k z *
        ((Nat.totient (excludedSiftingFactor k z) : ℝ) /
          (excludedSiftingFactor k z : ℝ)) := by
  have hdisjoint :
      Disjoint (siftingPrimes k z) (excludedSiftingPrimes k z) := by
    rw [Finset.disjoint_left]
    intro p hpk hpExcluded
    exact (mem_siftingPrimes.mp hpk).2.2
      (Finset.mem_filter.mp hpExcluded).2
  calc
    sieveProduct 1 z =
        ∏ p ∈ siftingPrimes k z ∪ excludedSiftingPrimes k z,
          (1 - localDensity p) := by
      unfold sieveProduct
      rw [siftingPrimes_union_excluded]
    _ = (∏ p ∈ siftingPrimes k z, (1 - localDensity p)) *
        ∏ p ∈ excludedSiftingPrimes k z,
          (1 - localDensity p) := by
      rw [Finset.prod_union hdisjoint]
    _ = sieveProduct k z *
        ((Nat.totient (excludedSiftingFactor k z) : ℝ) /
          (excludedSiftingFactor k z : ℝ)) := by
      rw [prod_one_sub_localDensity_eq_totient_div_prod
        (excludedSiftingPrimes k z)
        (fun p hp =>
          (mem_siftingPrimes.mp (Finset.mem_filter.mp hp).1).1)]
      rfl

/-- The preceding carrier identity gives the exact product factorization
`P_k(z) = P_(k*d)(z) * d` used in the source's divisor reindexing. -/
theorem siftingPrimes_mul_prod_mul
    {k d : ℕ} {z : ℝ}
    (hd : d ∣ (siftingPrimes k z).prod id) :
    (siftingPrimes (k * d) z).prod id * d =
      (siftingPrimes k z).prod id := by
  have hprodSq : Squarefree ((siftingPrimes k z).prod id) :=
    squarefree_prod_of_primes
      (fun p hp => (mem_siftingPrimes.mp hp).1)
  have hdSq : Squarefree d := hprodSq.squarefree_of_dvd hd
  have hprodNe : (siftingPrimes k z).prod id ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr
      (fun p hp => (mem_siftingPrimes.mp hp).1.ne_zero)
  have hsubset : d.primeFactors ⊆ siftingPrimes k z := by
    intro p hp
    have hpData := Nat.mem_primeFactors.mp hp
    have hpProd : p ∈ ((siftingPrimes k z).prod id).primeFactors :=
      Nat.mem_primeFactors.mpr
        ⟨hpData.1, hpData.2.1.trans hd, hprodNe⟩
    simpa only [id_eq,
      Nat.primeFactors_prod (fun q hq => (mem_siftingPrimes.mp hq).1)] using
      hpProd
  rw [siftingPrimes_mul_eq_sdiff_primeFactors hd]
  simpa only [id_eq, Nat.prod_primeFactors_of_squarefree hdSq] using
    (Finset.prod_sdiff (f := id) hsubset)

/-- On every divisor of the actual sifting product, the `BoundingSieve`
remainder is precisely controlled by the source hypothesis `H_k(M)`. -/
theorem RegularSource.abs_boundingSieve_rem_le_one_of_dvd
    (source : RegularSource) (z : ℝ) {d : ℕ}
    (hd : d ∣ (siftingPrimes source.k z).prod id) :
    |(source.boundingSieve z).rem d| ≤ 1 := by
  have hprodPos : 0 < (siftingPrimes source.k z).prod id :=
    Finset.prod_pos
      (fun p hp => (mem_siftingPrimes.mp hp).1.pos)
  have hdPos : 0 < d := Nat.pos_of_dvd_of_pos hd hprodPos
  have hregular :=
    source.regular d hdPos
      (coprime_of_dvd_siftingPrimes_prod hd)
  rw [BoundingSieve.rem,
    source.boundingSieve_nu_apply z hdPos]
  change
    |(∑ n ∈ source.carrier, if d ∣ n then (1 : ℝ) else 0) -
        1 / (d : ℝ) * source.y| ≤ 1
  rw [Finset.sum_boole]
  simpa [div_eq_mul_inv, mul_comm] using hregular

/-- The complete Selberg error of the literal source is bounded only from
the proved unit remainder `|R_d| ≤ 1`; no analytic source estimate is assumed. -/
theorem RegularSource.boundingSieve_errSum_le
    (source : RegularSource) (z : ℝ) (muPlus : ℕ → ℝ) :
    (source.boundingSieve z).errSum muPlus ≤
      ∑ d ∈ ((siftingPrimes source.k z).prod id).divisors,
        |muPlus d| := by
  unfold BoundingSieve.errSum
  apply Finset.sum_le_sum
  intro d hd
  have hdDvd :
      d ∣ (siftingPrimes source.k z).prod id :=
    (Nat.mem_divisors.mp hd).1
  simpa using
    mul_le_mul_of_nonneg_left
      (source.abs_boundingSieve_rem_le_one_of_dvd z hdDvd)
      (abs_nonneg (muPlus d))

/-- The exact finite Möbius expansion from `(1.1)`, used for the bounded-`z`
branch of Theorem 3.  Its error is bounded by the symbolic divisor count of
the actual finite sifting product; no cutoff values are enumerated. -/
theorem RegularSource.siftedCount_le_moebius_divisorError
    (source : RegularSource) (z : ℝ) :
    siftedCount source.carrier source.k z ≤
      source.y * sieveProduct source.k z +
        (((siftingPrimes source.k z).prod id).divisors.card : ℝ) := by
  let muR : ℕ → ℝ := fun d => ((μ d : ℤ) : ℝ)
  have hUpper : BoundingSieve.IsUpperMoebius muR := by
    intro n
    have hconv := congrArg (fun f : ArithmeticFunction ℝ => f n)
      ArithmeticFunction.coe_moebius_mul_coe_zeta
    rw [ArithmeticFunction.coe_mul_zeta_apply,
      ArithmeticFunction.one_apply] at hconv
    exact hconv.ge
  have hBound :=
    BoundingSieve.siftedSum_le_mainSum_errSum_of_upperMoebius
      (s := source.boundingSieve z) muR hUpper
  rw [source.boundingSieve_siftedSum_eq] at hBound
  have hMain :
      (source.boundingSieve z).mainSum muR =
        sieveProduct source.k z := by
    unfold BoundingSieve.mainSum
    rw [← source.boundingSieve_sieveProduct_eq]
    change
      (∑ d ∈ ((siftingPrimes source.k z).prod id).divisors,
        ((μ d : ℤ) : ℝ) * (source.boundingSieve z).nu d) =
      ∏ p ∈ ((siftingPrimes source.k z).prod id).primeFactors,
        (1 - (source.boundingSieve z).nu p)
    symm
    exact
      ArithmeticFunction.IsMultiplicative.prodPrimeFactors_one_sub_of_squarefree
        (source.boundingSieve z).nu (source.boundingSieve z).nu_mult
        (source.boundingSieve z).prodPrimes_squarefree
  have hErr :
      (source.boundingSieve z).errSum muR ≤
        (((siftingPrimes source.k z).prod id).divisors.card : ℝ) := by
    unfold BoundingSieve.errSum
    change
      (∑ d ∈ ((siftingPrimes source.k z).prod id).divisors,
        |muR d| * |(source.boundingSieve z).rem d|) ≤
      (((siftingPrimes source.k z).prod id).divisors.card : ℝ)
    calc
      (∑ d ∈ ((siftingPrimes source.k z).prod id).divisors,
          |muR d| * |(source.boundingSieve z).rem d|) ≤
          ∑ _d ∈ ((siftingPrimes source.k z).prod id).divisors,
            (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro d hd
        have hdDvd : d ∣ (siftingPrimes source.k z).prod id :=
          (Nat.mem_divisors.mp hd).1
        have hmu : |muR d| ≤ 1 := by
          dsimp [muR]
          exact_mod_cast ArithmeticFunction.abs_moebius_le_one
        have hrem :=
          source.abs_boundingSieve_rem_le_one_of_dvd z hdDvd
        nlinarith [abs_nonneg (muR d),
          abs_nonneg ((source.boundingSieve z).rem d)]
      _ = (((siftingPrimes source.k z).prod id).divisors.card : ℝ) := by
        simp
  rw [hMain] at hBound
  exact hBound.trans (add_le_add le_rfl hErr)

/-- Enlarging the real prime cutoff and restoring primes dividing `k` can
only decrease the source Euler product. -/
theorem sieveProduct_exp_two_le_of_log_le_two
    {k : ℕ} {z : ℝ} (hz : 0 < z) (hlog : Real.log z ≤ 2) :
    sieveProduct 1 (Real.exp 2) ≤ sieveProduct k z := by
  have hzExp : z ≤ Real.exp 2 := by
    rw [← Real.exp_log hz]
    exact Real.exp_le_exp.mpr hlog
  have hsubset :
      siftingPrimes k z ⊆ siftingPrimes 1 (Real.exp 2) := by
    intro p hp
    have hpData := mem_siftingPrimes.mp hp
    exact mem_siftingPrimes.mpr
      ⟨hpData.1, hpData.2.1.trans_le hzExp,
        fun hp1 => hpData.1.ne_one (Nat.dvd_one.mp hp1)⟩
  unfold sieveProduct
  apply Finset.prod_le_prod_of_subset_of_le_one hsubset
  · intro p hp
    have hpPrime := (mem_siftingPrimes.mp hp).1
    have hpReal : (1 : ℝ) < p := by exact_mod_cast hpPrime.one_lt
    have hlt : localDensity p < 1 := by
      simpa [localDensity] using
        ((div_lt_one (by positivity : (0 : ℝ) < p)).2 hpReal)
    exact (sub_pos.mpr hlt).le
  · intro p hp hpNot
    have : 0 ≤ localDensity p := by
      unfold localDensity
      positivity
    linarith

/-- On the bounded-`z` lane, the divisor error in the exact finite Möbius
expansion is bounded by one symbolic absolute constant. -/
theorem RegularSource.exists_siftedCount_le_moebius_bounded_log (b : ℝ) :
    ∃ D > 0, ∀ (source : RegularSource) {z : ℝ},
      0 < z → Real.log z ≤ b →
      siftedCount source.carrier source.k z ≤
        source.y * sieveProduct source.k z + D := by
  let Q := (siftingPrimes 1 (Real.exp b)).prod id
  let D : ℝ := (Q.divisors.card : ℝ) + 1
  have hQPos : 0 < Q := by
    dsimp [Q]
    exact Finset.prod_pos fun p hp => (mem_siftingPrimes.mp hp).1.pos
  refine ⟨D, by dsimp [D]; positivity, fun source z hz hlog => ?_⟩
  have hzExp : z ≤ Real.exp b := by
    rw [← Real.exp_log hz]
    exact Real.exp_le_exp.mpr hlog
  have hsubset :
      siftingPrimes source.k z ⊆ siftingPrimes 1 (Real.exp b) := by
    intro p hp
    have hpData := mem_siftingPrimes.mp hp
    exact mem_siftingPrimes.mpr
      ⟨hpData.1, hpData.2.1.trans_le hzExp,
        fun hp1 => hpData.1.ne_one (Nat.dvd_one.mp hp1)⟩
  have hprodDvd : (siftingPrimes source.k z).prod id ∣ Q := by
    dsimp [Q]
    exact Finset.prod_dvd_prod_of_subset
      (siftingPrimes source.k z) (siftingPrimes 1 (Real.exp b)) id
      hsubset
  have hdivSubset :
      ((siftingPrimes source.k z).prod id).divisors ⊆ Q.divisors := by
    intro d hd
    rw [Nat.mem_divisors] at hd ⊢
    exact ⟨hd.1.trans hprodDvd, hQPos.ne'⟩
  have hcard :
      (((siftingPrimes source.k z).prod id).divisors.card : ℝ) ≤ D := by
    dsimp [D]
    exact_mod_cast
      (Finset.card_mono hdivSubset).trans
        (Nat.le_add_right Q.divisors.card 1)
  exact (source.siftedCount_le_moebius_divisorError z).trans
    (add_le_add le_rfl hcard)

theorem RegularSource.exists_siftedCount_le_moebius_boundedZ :
    ∃ D > 0, ∀ (source : RegularSource) {z : ℝ},
      0 < z → Real.log z ≤ 2 →
      siftedCount source.carrier source.k z ≤
        source.y * sieveProduct source.k z + D :=
  RegularSource.exists_siftedCount_le_moebius_bounded_log 2

/-- The unconditional finite Selberg upper bound specialized to the literal
`H_k(M)` source. The explicit denominator and smooth-number estimates used
for `(3.9)` and `(4.2)` are proved separately, without a generic-density
premise. -/
theorem RegularSource.exists_siftedCount_le_selberg
    (source : RegularSource) (z : ℝ) :
    ∃ w : ℕ → ℝ, w 1 = 1 ∧
      siftedCount source.carrier source.k z ≤
        source.y *
            (∑ l ∈ ((siftingPrimes source.k z).prod id).divisors,
              (source.boundingSieve z).selbergTerms l)⁻¹ +
          ∑ d ∈ ((siftingPrimes source.k z).prod id).divisors,
            |BoundingSieve.lambdaSquared w d| := by
  obtain ⟨w, hw, hSelberg⟩ :=
    AnalyticNumberTheory.Sieve.selberg_upper_bound_optimal
      (source.boundingSieve z)
  refine ⟨w, hw, ?_⟩
  rw [source.boundingSieve_siftedSum_eq z] at hSelberg
  have hErr :=
    source.boundingSieve_errSum_le z
      (BoundingSieve.lambdaSquared w)
  calc
    siftedCount source.carrier source.k z ≤
        source.y *
            (∑ l ∈ ((siftingPrimes source.k z).prod id).divisors,
              (source.boundingSieve z).selbergTerms l)⁻¹ +
          (source.boundingSieve z).errSum
            (BoundingSieve.lambdaSquared w) := by
      simpa only [RegularSource.boundingSieve] using hSelberg
    _ ≤ source.y *
            (∑ l ∈ ((siftingPrimes source.k z).prod id).divisors,
              (source.boundingSieve z).selbergTerms l)⁻¹ +
          ∑ d ∈ ((siftingPrimes source.k z).prod id).divisors,
            |BoundingSieve.lambdaSquared w d| :=
      add_le_add (le_refl _) hErr

/-- The independent finite level in the source's Selberg denominator.  This is
the literal finite `S_k(xi, z)` construction behind Theorem 2, before its
reciprocal-totient and rough-number estimates are applied. -/
noncomputable def RegularSource.levelSelbergDenominator
    (source : RegularSource) (z : ℝ) (xi : ℕ) : ℝ :=
  LiuWeight.truncatedSelbergDenominator (source.boundingSieve z) xi

/-- The divisor carrier in the paper's finite sum `S_k(xi, z)`. -/
def selbergReciprocalTotientCarrier
    (k xi : ℕ) (z : ℝ) : Finset ℕ :=
  ((siftingPrimes k z).prod id).divisors.filter (fun d => d ≤ xi)

/-- The source carrier counted by `Psi(xi, z)`: positive integers at most
`xi` whose greatest prime divisor is below `z`, with the printed convention
that the greatest prime divisor of `1` is `1`. -/
noncomputable def selbergPsiCarrier (xi : ℕ) (z : ℝ) : Finset ℕ :=
  (Finset.Icc 1 xi).filter
    (fun n => (n = 1 → (1 : ℝ) < z) ∧
      ∀ p ∈ n.primeFactors, (p : ℝ) < z)

/-- The finite smooth-number quantity `Psi(xi, z)` in Theorem 2. -/
noncomputable def selbergPsi (xi : ℕ) (z : ℝ) : ℝ :=
  (selbergPsiCarrier xi z).card

/-- The reciprocal smooth-number sum denoted by `T(x,z)` in Lemma 3.1. -/
noncomputable def selbergSmoothReciprocalSum (xi : ℕ) (z : ℝ) : ℝ :=
  ∑ n ∈ selbergPsiCarrier xi z, 1 / (n : ℝ)

/-- The finite Rankin moment of the source's literal smooth-number carrier. -/
noncomputable def selbergSmoothRpowSum
    (xi : ℕ) (z sigma : ℝ) : ℝ :=
  ∑ n ∈ selbergPsiCarrier xi z, (n : ℝ) ^ (-sigma)

/-- The completely multiplicative real power used in the finite-prime Euler
product behind Vinogradov's estimate `(4.3)`. -/
private noncomputable def natRpowMonoidHom (sigma : ℝ) : ℕ →* ℝ where
  toFun n := (n : ℝ) ^ (-sigma)
  map_one' := by simp
  map_mul' m n := by
    rw [Nat.cast_mul,
      Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n)]

/-- The reciprocal map used to expand the finite Euler product in `(4.4)`. -/
private noncomputable def reciprocalNatMonoidHom : ℕ →* ℝ where
  toFun n := (n : ℝ)⁻¹
  map_one' := by norm_num
  map_mul' m n := by
    simp only [Nat.cast_mul]
    rw [mul_inv_rev]
    ring

/-- The exact Euler series identity in `(4.4)`, before passing to the paper's
finite truncations `T(x,z)`. -/
theorem hasSum_selbergSmoothReciprocal (z : ℝ) :
    HasSum
      (fun m : Nat.factoredNumbers (siftingPrimes 1 z) =>
        1 / (m : ℝ))
      (sieveProduct 1 z)⁻¹ := by
  have hPrimeInv {p : ℕ} (hp : p.Prime) :
      ‖reciprocalNatMonoidHom p‖ < 1 := by
    have hpReal : (0 : ℝ) < p := Nat.cast_pos.mpr hp.pos
    change |(p : ℝ)⁻¹| < 1
    rw [abs_inv, abs_of_pos hpReal]
    rw [inv_lt_one₀ hpReal]
    exact_mod_cast hp.one_lt
  have hfilter :
      (siftingPrimes 1 z).filter Nat.Prime = siftingPrimes 1 z :=
    Finset.filter_eq_self.2 fun p hp => (mem_siftingPrimes.mp hp).1
  have hEuler :=
    (EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric
      (f := reciprocalNatMonoidHom) hPrimeInv (siftingPrimes 1 z)).2
  rw [hfilter] at hEuler
  change
    HasSum
      (fun m : Nat.factoredNumbers (siftingPrimes 1 z) =>
        ((m : ℕ) : ℝ)⁻¹)
      (∏ p ∈ siftingPrimes 1 z, (1 - (p : ℝ)⁻¹)⁻¹) at hEuler
  rw [Finset.prod_inv_distrib] at hEuler
  simpa only [one_div, sieveProduct, localDensity] using hEuler

/-- The exact Euler series for every positive Rankin exponent.  This is the
finite-prime product to be estimated in Vinogradov's argument, not an assumed
smooth-number bound. -/
theorem hasSum_selbergSmoothRpow
    (z sigma : ℝ) (hsigma : 0 < sigma) :
    HasSum
      (fun m : Nat.factoredNumbers (siftingPrimes 1 z) =>
        (m : ℝ) ^ (-sigma))
      (∏ p ∈ siftingPrimes 1 z,
        (1 - (p : ℝ) ^ (-sigma))⁻¹) := by
  have hPrimeRpow {p : ℕ} (hp : p.Prime) :
      ‖natRpowMonoidHom sigma p‖ < 1 := by
    have hpReal : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    change |(p : ℝ) ^ (-sigma)| < 1
    rw [abs_of_pos (Real.rpow_pos_of_pos (by positivity) _)]
    exact Real.rpow_lt_one_of_one_lt_of_neg hpReal (neg_neg_of_pos hsigma)
  have hfilter :
      (siftingPrimes 1 z).filter Nat.Prime = siftingPrimes 1 z :=
    Finset.filter_eq_self.2 fun p hp => (mem_siftingPrimes.mp hp).1
  have hEuler :=
    (EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric
      (f := natRpowMonoidHom sigma) hPrimeRpow
      (siftingPrimes 1 z)).2
  rw [hfilter] at hEuler
  exact hEuler

/-- For `z > 1`, the source's finite smooth carrier is exactly the bounded
part of the finite-prime-factor subtype used by the Euler product. -/
theorem mem_selbergPsiCarrier_iff_factoredNumbers
    {xi n : ℕ} {z : ℝ} (hz : 1 < z) :
    n ∈ selbergPsiCarrier xi z ↔
      n ≤ xi ∧ n ∈ Nat.factoredNumbers (siftingPrimes 1 z) := by
  rw [selbergPsiCarrier, Finset.mem_filter, Finset.mem_Icc,
    Nat.mem_factoredNumbers_iff_primeFactors_subset]
  constructor
  · rintro ⟨⟨hnPos, hnXi⟩, -, hnFactors⟩
    refine ⟨hnXi, Nat.ne_of_gt hnPos, ?_⟩
    intro p hp
    have hpPrime := Nat.prime_of_mem_primeFactors hp
    exact
      mem_siftingPrimes.mpr
        ⟨hpPrime, hnFactors p hp,
          fun hp1 => hpPrime.ne_one (Nat.dvd_one.mp hp1)⟩
  · rintro ⟨hnXi, hn0, hnFactors⟩
    refine ⟨⟨Nat.pos_of_ne_zero hn0, hnXi⟩, fun _ => hz, ?_⟩
    intro p hp
    exact (mem_siftingPrimes.mp (hnFactors hp)).2.1

/-- The paper's literal finite `Psi(xi,z)` carrier is exactly Mathlib's
finite smooth-number carrier, including the strict real cutoff through
`ceil z`. -/
theorem selbergPsiCarrier_eq_smoothNumbersUpTo
    {xi : ℕ} {z : ℝ} (hz : 1 < z) :
    selbergPsiCarrier xi z = Nat.smoothNumbersUpTo xi ⌈z⌉₊ := by
  ext n
  rw [mem_selbergPsiCarrier_iff_factoredNumbers hz,
    Nat.mem_smoothNumbersUpTo,
    Nat.smoothNumbers_eq_factoredNumbers_primesBelow,
    siftingPrimes_one_eq_primesBelow]

/-- The literal smooth carrier is monotone jointly in both source cutoffs. -/
theorem selbergPsiCarrier_mono
    {xi₁ xi₂ : ℕ} {z₁ z₂ : ℝ}
    (hxi : xi₁ ≤ xi₂) (hz : z₁ ≤ z₂) :
    selbergPsiCarrier xi₁ z₁ ⊆ selbergPsiCarrier xi₂ z₂ := by
  intro n hn
  rw [selbergPsiCarrier, Finset.mem_filter, Finset.mem_Icc] at hn ⊢
  exact
    ⟨⟨hn.1.1, hn.1.2.trans hxi⟩,
      fun hn1 => (hn.2.1 hn1).trans_le hz,
      fun p hp => (hn.2.2 p hp).trans_le hz⟩

/-- Consequently the source's finite `Psi` count is jointly monotone. -/
theorem selbergPsi_mono
    {xi₁ xi₂ : ℕ} {z₁ z₂ : ℝ}
    (hxi : xi₁ ≤ xi₂) (hz : z₁ ≤ z₂) :
    selbergPsi xi₁ z₁ ≤ selbergPsi xi₂ z₂ := by
  unfold selbergPsi
  exact_mod_cast Finset.card_le_card (selbergPsiCarrier_mono hxi hz)

/-- The strongest smooth-number count currently available from Mathlib,
transported to the exact source carrier.  Its prime-counting factor is the
remaining gap to Vinogradov's uniform estimate `(4.3)`. -/
theorem selbergPsiCarrier_card_le_pow_primeCounting_mul_sqrt
    {xi : ℕ} {z : ℝ} (hz : 1 < z) :
    (selbergPsiCarrier xi z).card ≤
      2 ^ ⌈z⌉₊.primesBelow.card * xi.sqrt := by
  rw [selbergPsiCarrier_eq_smoothNumbersUpTo hz]
  exact Nat.smoothNumbersUpTo_card_le xi ⌈z⌉₊

/-- The source's `T(x,z)` is the ordinary natural partial sum of the exact
Euler series in `(4.4)`. -/
theorem selbergSmoothReciprocalSum_eq_sum_range_indicator
    {xi : ℕ} {z : ℝ} (hz : 1 < z) :
    selbergSmoothReciprocalSum xi z =
      ∑ n ∈ Finset.range (xi + 1),
        (Nat.factoredNumbers (siftingPrimes 1 z)).indicator
          (fun m : ℕ => 1 / (m : ℝ)) n := by
  have hcarrier :
      selbergPsiCarrier xi z =
        (Finset.range (xi + 1)).filter
          (fun n => n ∈ Nat.factoredNumbers (siftingPrimes 1 z)) := by
    ext n
    rw [mem_selbergPsiCarrier_iff_factoredNumbers hz,
      Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hnXi, hSmooth⟩
      exact ⟨Nat.lt_succ_iff.mpr hnXi, hSmooth⟩
    · rintro ⟨hnXi, hSmooth⟩
      exact ⟨Nat.lt_succ_iff.mp hnXi, hSmooth⟩
  rw [selbergSmoothReciprocalSum, hcarrier, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hSmooth : n ∈ Nat.factoredNumbers (siftingPrimes 1 z)
  · simp only [hSmooth, ↓reduceIte, Set.indicator_of_mem]
  · rw [Set.indicator_of_notMem hSmooth]
    simp only [hSmooth, ↓reduceIte]

/-- The `0/1` coefficient whose prefix sum is the literal smooth-number
count. -/
private noncomputable def selbergSmoothIndicator (z : ℝ) (n : ℕ) : ℝ :=
  (Nat.factoredNumbers (siftingPrimes 1 z)).indicator
    (fun _ : ℕ => 1) n

private theorem sum_Icc_selbergSmoothIndicator
    {n : ℕ} {z : ℝ} (hz : 1 < z) :
    ∑ k ∈ Finset.Icc 0 n, selbergSmoothIndicator z k =
      selbergPsi n z := by
  have hcarrier :
      selbergPsiCarrier n z =
        (Finset.range (n + 1)).filter
          (fun k => k ∈ Nat.factoredNumbers (siftingPrimes 1 z)) := by
    ext k
    rw [mem_selbergPsiCarrier_iff_factoredNumbers hz,
      Finset.mem_filter, Finset.mem_range]
    simp only [Nat.lt_succ_iff]
  rw [← Nat.range_succ_eq_Icc_zero]
  unfold selbergSmoothIndicator selbergPsi
  rw [hcarrier]
  calc
    (∑ k ∈ Finset.range (n + 1),
        (Nat.factoredNumbers (siftingPrimes 1 z)).indicator
          (fun _ : ℕ => (1 : ℝ)) k) =
        ∑ k ∈ (Finset.range (n + 1)).filter
          (fun k => k ∈ Nat.factoredNumbers (siftingPrimes 1 z)),
          (1 : ℝ) := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro k hk
      by_cases hs : k ∈ Nat.factoredNumbers (siftingPrimes 1 z)
      · simp [hs]
      · simp [hs]
    _ = _ := by simp

private theorem selbergSmoothReciprocalSum_sub_eq_sum_Ioc
    {n m : ℕ} {z : ℝ} (hz : 1 < z) (hnm : n ≤ m) :
    selbergSmoothReciprocalSum m z -
        selbergSmoothReciprocalSum n z =
      ∑ k ∈ Finset.Ioc n m,
        (k : ℝ)⁻¹ * selbergSmoothIndicator z k := by
  rw [selbergSmoothReciprocalSum_eq_sum_range_indicator hz,
    selbergSmoothReciprocalSum_eq_sum_range_indicator hz]
  rw [show Finset.range (m + 1) = Finset.Icc 0 m by
      rw [Nat.range_succ_eq_Icc_zero],
    show Finset.range (n + 1) = Finset.Icc 0 n by
      rw [Nat.range_succ_eq_Icc_zero]]
  have hsplit :
      (∑ k ∈ Finset.Icc 0 m,
          (Nat.factoredNumbers (siftingPrimes 1 z)).indicator
            (fun q : ℕ => 1 / (q : ℝ)) k) =
        (∑ k ∈ Finset.Icc 0 n,
          (Nat.factoredNumbers (siftingPrimes 1 z)).indicator
            (fun q : ℕ => 1 / (q : ℝ)) k) +
        ∑ k ∈ Finset.Ioc n m,
          (Nat.factoredNumbers (siftingPrimes 1 z)).indicator
            (fun q : ℕ => 1 / (q : ℝ)) k := by
    rw [← Finset.sum_sdiff (Finset.Icc_subset_Icc_right hnm)]
    have hset :
        Finset.Icc 0 m \ Finset.Icc 0 n = Finset.Ioc n m := by
      ext k
      simp only [Finset.mem_sdiff, Finset.mem_Icc, Finset.mem_Ioc]
      omega
    rw [hset]
    ac_rfl
  rw [hsplit]
  ring_nf
  unfold selbergSmoothIndicator
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hs : k ∈ Nat.factoredNumbers (siftingPrimes 1 z)
  · simp [hs]
  · simp [hs]

/-- The finite Rankin moment is the ordinary natural partial sum of its exact
Euler series. -/
theorem selbergSmoothRpowSum_eq_sum_range_indicator
    {xi : ℕ} {z sigma : ℝ} (hz : 1 < z) :
    selbergSmoothRpowSum xi z sigma =
      ∑ n ∈ Finset.range (xi + 1),
        (Nat.factoredNumbers (siftingPrimes 1 z)).indicator
          (fun m : ℕ => (m : ℝ) ^ (-sigma)) n := by
  have hcarrier :
      selbergPsiCarrier xi z =
        (Finset.range (xi + 1)).filter
          (fun n => n ∈ Nat.factoredNumbers (siftingPrimes 1 z)) := by
    ext n
    rw [mem_selbergPsiCarrier_iff_factoredNumbers hz,
      Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hnXi, hSmooth⟩
      exact ⟨Nat.lt_succ_iff.mpr hnXi, hSmooth⟩
    · rintro ⟨hnXi, hSmooth⟩
      exact ⟨Nat.lt_succ_iff.mp hnXi, hSmooth⟩
  rw [selbergSmoothRpowSum, hcarrier, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hSmooth : n ∈ Nat.factoredNumbers (siftingPrimes 1 z)
  · simp only [hSmooth, ↓reduceIte, Set.indicator_of_mem]
  · rw [Set.indicator_of_notMem hSmooth]
    simp only [hSmooth, ↓reduceIte]

/-- The literal finite Rankin moment is bounded by its finite-prime Euler
product.  This is the summation step in the proof of `(4.3)`. -/
theorem selbergSmoothRpowSum_le_eulerProduct
    {xi : ℕ} {z sigma : ℝ} (hz : 1 < z) (hsigma : 0 < sigma) :
    selbergSmoothRpowSum xi z sigma ≤
      ∏ p ∈ siftingPrimes 1 z,
        (1 - (p : ℝ) ^ (-sigma))⁻¹ := by
  let S := Nat.factoredNumbers (siftingPrimes 1 z)
  let g : ℕ → ℝ :=
    S.indicator (fun n : ℕ => (n : ℝ) ^ (-sigma))
  have hHas := hasSum_selbergSmoothRpow z sigma hsigma
  have hSummableSub :
      Summable
        (fun m : Nat.factoredNumbers (siftingPrimes 1 z) =>
          (m : ℝ) ^ (-sigma)) :=
    hHas.summable
  have hSummable : Summable g := by
    dsimp [g, S]
    exact summable_subtype_iff_indicator.mp hSummableSub
  have hTsum :
      ∑' n : ℕ, g n =
        ∏ p ∈ siftingPrimes 1 z,
          (1 - (p : ℝ) ^ (-sigma))⁻¹ := by
    dsimp [g, S]
    rw [← tsum_subtype]
    exact hHas.tsum_eq
  calc
    selbergSmoothRpowSum xi z sigma =
        ∑ n ∈ Finset.range (xi + 1), g n := by
      simp only [g, S,
        selbergSmoothRpowSum_eq_sum_range_indicator hz]
    _ ≤ ∑' n : ℕ, g n := by
      apply hSummable.sum_le_tsum
      intro n hn
      dsimp [g]
      by_cases hSmooth : n ∈ S
      · rw [Set.indicator_of_mem hSmooth]
        exact Real.rpow_nonneg (Nat.cast_nonneg n) _
      · rw [Set.indicator_of_notMem hSmooth]
    _ = ∏ p ∈ siftingPrimes 1 z,
        (1 - (p : ℝ) ^ (-sigma))⁻¹ := hTsum

/-- Rankin's inequality on the paper's actual finite smooth-number carrier. -/
theorem selbergPsi_le_rpow_mul_smoothRpowSum
    {xi : ℕ} {z sigma : ℝ} (hsigma : 0 ≤ sigma) :
    selbergPsi xi z ≤
      (xi : ℝ) ^ sigma * selbergSmoothRpowSum xi z sigma := by
  change ((selbergPsiCarrier xi z).card : ℝ) ≤ _
  calc
    ((selbergPsiCarrier xi z).card : ℝ) =
        ∑ n ∈ selbergPsiCarrier xi z, (1 : ℝ) := by simp
    _ ≤ ∑ n ∈ selbergPsiCarrier xi z,
        (xi : ℝ) ^ sigma * (n : ℝ) ^ (-sigma) := by
      apply Finset.sum_le_sum
      intro n hn
      have hnData :=
        (Finset.mem_filter.mp hn).1
      have hnPos : 0 < n := (Finset.mem_Icc.mp hnData).1
      have hnXi : n ≤ xi := (Finset.mem_Icc.mp hnData).2
      have hnPowPos : 0 < (n : ℝ) ^ sigma :=
        Real.rpow_pos_of_pos (Nat.cast_pos.mpr hnPos) sigma
      have hpow :
          (n : ℝ) ^ sigma ≤ (xi : ℝ) ^ sigma :=
        Real.rpow_le_rpow (Nat.cast_nonneg n)
          (Nat.cast_le.mpr hnXi) hsigma
      have hdiv :
          1 ≤ (xi : ℝ) ^ sigma / (n : ℝ) ^ sigma :=
        (le_div_iff₀ hnPowPos).2 (by simpa using hpow)
      rw [div_eq_mul_inv, ← Real.rpow_neg (Nat.cast_nonneg n) sigma] at hdiv
      exact hdiv
    _ = (xi : ℝ) ^ sigma *
        selbergSmoothRpowSum xi z sigma := by
      rw [selbergSmoothRpowSum, Finset.mul_sum]

/-- The unconditional finite Rankin bound reducing Vinogradov's estimate
`(4.3)` to a finite-prime Euler-product estimate. -/
theorem selbergPsi_le_rpow_mul_eulerProduct
    {xi : ℕ} {z sigma : ℝ} (hz : 1 < z) (hsigma : 0 < sigma) :
    selbergPsi xi z ≤
      (xi : ℝ) ^ sigma *
        ∏ p ∈ siftingPrimes 1 z,
          (1 - (p : ℝ) ^ (-sigma))⁻¹ := by
  exact
    (selbergPsi_le_rpow_mul_smoothRpowSum hsigma.le).trans
      (mul_le_mul_of_nonneg_left
        (selbergSmoothRpowSum_le_eulerProduct hz hsigma)
        (Real.rpow_nonneg (Nat.cast_nonneg xi) sigma))

/-- Formula `(4.4)`: the source's finite reciprocal smooth sums converge
exactly to the reciprocal finite Euler product. -/
theorem tendsto_selbergSmoothReciprocalSum (z : ℝ) (hz : 1 < z) :
    Filter.Tendsto
      (fun xi : ℕ => selbergSmoothReciprocalSum xi z)
      Filter.atTop (nhds (sieveProduct 1 z)⁻¹) := by
  let S := Nat.factoredNumbers (siftingPrimes 1 z)
  let g : ℕ → ℝ :=
    S.indicator (fun n : ℕ => 1 / (n : ℝ))
  have hHas := hasSum_selbergSmoothReciprocal z
  have hSummableSub :
      Summable
        (fun m : Nat.factoredNumbers (siftingPrimes 1 z) =>
          1 / (m : ℝ)) :=
    hHas.summable
  have hSummable : Summable g := by
    dsimp [g, S]
    exact summable_subtype_iff_indicator.mp hSummableSub
  have hTsum : ∑' n : ℕ, g n = (sieveProduct 1 z)⁻¹ := by
    dsimp [g, S]
    rw [← tsum_subtype]
    exact hHas.tsum_eq
  have hgHas : HasSum g (sieveProduct 1 z)⁻¹ := by
    rw [← hTsum]
    exact hSummable.hasSum
  have hTend :
      Filter.Tendsto
        (fun n : ℕ => ∑ i ∈ Finset.range n, g i)
        Filter.atTop (nhds (sieveProduct 1 z)⁻¹) :=
    (hSummable.hasSum_iff_tendsto_nat).mp hgHas
  have hSucc :
      Filter.Tendsto (fun n : ℕ => n + 1)
        Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop.2 fun b =>
      Filter.eventually_atTop.2 ⟨b, fun a ha => by omega⟩
  have hComposed := hTend.comp hSucc
  change
    Filter.Tendsto
      (fun xi : ℕ => ∑ i ∈ Finset.range (xi + 1), g i)
      Filter.atTop (nhds (sieveProduct 1 z)⁻¹) at hComposed
  simpa only [g, S,
    selbergSmoothReciprocalSum_eq_sum_range_indicator hz] using hComposed

/-- Finite-tail form of `(4.4)`. The source obtains a uniform rate from
Vinogradov's `(4.3)`; `ChenTheoremThree` instead proves the required
normalized estimate without that historical input. -/
theorem exists_selbergSmoothReciprocalSum_tail_lt
    {z epsilon : ℝ} (hz : 1 < z) (hepsilon : 0 < epsilon) :
    ∃ X : ℕ, ∀ xi ≥ X,
      |selbergSmoothReciprocalSum xi z - (sieveProduct 1 z)⁻¹| <
        epsilon := by
  exact
    (Metric.tendsto_atTop.1
      (tendsto_selbergSmoothReciprocalSum z hz)) epsilon hepsilon

/-- The squarefree kernel of a smooth integer belongs to the divisor carrier
of the paper's reciprocal-totient sum. -/
theorem radical_mem_selbergReciprocalTotientCarrier
    {xi n : ℕ} {z : ℝ}
    (hn : n ∈ selbergPsiCarrier xi z) :
    UniqueFactorizationMonoid.radical n ∈
      selbergReciprocalTotientCarrier 1 xi z := by
  rw [selbergPsiCarrier, Finset.mem_filter, Finset.mem_Icc] at hn
  rcases hn with ⟨⟨hnPos, hnXi⟩, -, hnSmooth⟩
  rw [selbergReciprocalTotientCarrier, Finset.mem_filter]
  have hprodNe : (siftingPrimes 1 z).prod id ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr
      (fun p hp => (mem_siftingPrimes.mp hp).1.ne_zero)
  refine ⟨?_, (Nat.radical_le_self_iff.mpr (Nat.ne_of_gt hnPos)).trans hnXi⟩
  rw [Nat.mem_divisors]
  refine ⟨?_, hprodNe⟩
  rw [Nat.radical_eq_prod_primeFactors]
  apply Finset.prod_dvd_prod_of_subset _ _ id
  intro p hp
  rw [mem_siftingPrimes]
  have hpPrime := Nat.prime_of_mem_primeFactors hp
  refine ⟨hpPrime, hnSmooth p hp, ?_⟩
  intro hp1
  exact hpPrime.ne_one (Nat.dvd_one.mp hp1)

/-- Every divisor retained in `S_k(xi, z)` is counted by the source's
`Psi(xi, z)`. -/
theorem selbergReciprocalTotientCarrier_subset_psiCarrier
    {k xi : ℕ} {z : ℝ} (hz : 1 < z) :
    selbergReciprocalTotientCarrier k xi z ⊆ selbergPsiCarrier xi z := by
  intro d hd
  rw [selbergReciprocalTotientCarrier, Finset.mem_filter,
    Nat.mem_divisors] at hd
  rcases hd with ⟨⟨hdDiv, hprodNe⟩, hdXi⟩
  rw [selbergPsiCarrier, Finset.mem_filter, Finset.mem_Icc]
  have hprodPos : 0 < (siftingPrimes k z).prod id :=
    Finset.prod_pos (fun p hp => (mem_siftingPrimes.mp hp).1.pos)
  have hdPos : 0 < d := Nat.pos_of_dvd_of_pos hdDiv hprodPos
  refine ⟨⟨hdPos, hdXi⟩, fun _ => hz, ?_⟩
  intro p hp
  have hpData := Nat.mem_primeFactors.mp hp
  have hpProd : p ∈ ((siftingPrimes k z).prod id).primeFactors :=
    Nat.mem_primeFactors.mpr
      ⟨hpData.1, hpData.2.1.trans hdDiv, hprodNe⟩
  have hpSift : p ∈ siftingPrimes k z := by
    simpa only [id_eq,
      Nat.primeFactors_prod (fun q hq => (mem_siftingPrimes.mp hq).1)] using
      hpProd
  exact (mem_siftingPrimes.mp hpSift).2.1

/-- Multiplication by a retained divisor `d` bijects the source carrier for
`S_(k*d)(xi/d, z)` with the retained multiples of `d` in `S_k(xi, z)`. -/
theorem selbergReciprocalTotientCarrier_map_mul
    {k d xi : ℕ} {z : ℝ}
    (hd : d ∣ (siftingPrimes k z).prod id) :
    let mulD : ℕ ↪ ℕ :=
      ⟨fun m => d * m, fun _ _ hab =>
        Nat.eq_of_mul_eq_mul_left
          (Nat.pos_of_dvd_of_pos hd
            (Finset.prod_pos fun _ hp => (mem_siftingPrimes.mp hp).1.pos))
          hab⟩
    (selbergReciprocalTotientCarrier (k * d) (xi / d) z).map mulD =
      (selbergReciprocalTotientCarrier k xi z).filter (fun e => d ∣ e) := by
  have hprodPos : 0 < (siftingPrimes k z).prod id :=
    Finset.prod_pos (fun p hp => (mem_siftingPrimes.mp hp).1.pos)
  have hdPos : 0 < d := Nat.pos_of_dvd_of_pos hd hprodPos
  let mulD : ℕ ↪ ℕ :=
    ⟨fun m => d * m, fun _ _ hab =>
      Nat.eq_of_mul_eq_mul_left hdPos hab⟩
  dsimp only
  change
    (selbergReciprocalTotientCarrier (k * d) (xi / d) z).map mulD =
      (selbergReciprocalTotientCarrier k xi z).filter (fun e => d ∣ e)
  ext e
  rw [Finset.mem_map, Finset.mem_filter]
  constructor
  · rintro ⟨m, hm, rfl⟩
    rw [selbergReciprocalTotientCarrier, Finset.mem_filter,
      Nat.mem_divisors] at hm
    rcases hm with ⟨⟨hmDiv, hmProdNe⟩, hmLe⟩
    have hmPk : m ∣ (siftingPrimes k z).prod id := by
      apply hmDiv.trans
      rw [← siftingPrimes_mul_prod_mul hd]
      exact dvd_mul_right _ _
    have hmCoprimeD : Nat.Coprime d m := by
      have hmCoprimeKD : Nat.Coprime m (k * d) :=
        coprime_of_dvd_siftingPrimes_prod hmDiv
      exact (Nat.coprime_mul_iff_right.mp hmCoprimeKD).2.symm
    refine ⟨?_, dvd_mul_right d m⟩
    rw [selbergReciprocalTotientCarrier, Finset.mem_filter,
      Nat.mem_divisors]
    refine ⟨⟨hmCoprimeD.mul_dvd_of_dvd_of_dvd hd hmPk,
      Nat.ne_of_gt hprodPos⟩, ?_⟩
    have hmMulLe := (Nat.le_div_iff_mul_le hdPos).mp hmLe
    change d * m ≤ xi
    simpa only [Nat.mul_comm] using hmMulLe
  · rintro ⟨he, hdE⟩
    rw [selbergReciprocalTotientCarrier, Finset.mem_filter,
      Nat.mem_divisors] at he
    rcases he with ⟨⟨heDiv, hprodNe⟩, heLe⟩
    let m := e / d
    have hdm : d * m = e := Nat.mul_div_cancel' hdE
    have hmDiv : m ∣ (siftingPrimes (k * d) z).prod id := by
      obtain ⟨c, hc⟩ := heDiv
      refine ⟨c, ?_⟩
      apply Eq.symm
      apply Nat.eq_of_mul_eq_mul_left hdPos
      calc
        d * (m * c) = (d * m) * c := by ring
        _ = e * c := by rw [hdm]
        _ = (siftingPrimes k z).prod id := hc.symm
        _ = (siftingPrimes (k * d) z).prod id * d :=
          (siftingPrimes_mul_prod_mul hd).symm
        _ = d * ((siftingPrimes (k * d) z).prod id) := by ring
    refine ⟨m, ?_, ?_⟩
    · rw [selbergReciprocalTotientCarrier, Finset.mem_filter,
        Nat.mem_divisors]
      refine ⟨⟨hmDiv, ?_⟩, ?_⟩
      · exact Finset.prod_ne_zero_iff.mpr
          (fun p hp => (mem_siftingPrimes.mp hp).1.ne_zero)
      · apply (Nat.le_div_iff_mul_le hdPos).2
        simpa only [Nat.mul_comm, hdm] using heLe
    · exact hdm

/-- Sum form of the preceding bijection: retained multiples of `d` are
reindexed by their unique quotient in the source carrier for `k*d`. -/
theorem sum_selbergReciprocalTotientCarrier_if_dvd
    {k d xi : ℕ} {z : ℝ}
    (hd : d ∣ (siftingPrimes k z).prod id) (f : ℕ → ℝ) :
    (∑ e ∈ selbergReciprocalTotientCarrier k xi z,
        if d ∣ e then f (e / d) else 0) =
      ∑ m ∈ selbergReciprocalTotientCarrier (k * d) (xi / d) z, f m := by
  have hprodPos : 0 < (siftingPrimes k z).prod id :=
    Finset.prod_pos (fun p hp => (mem_siftingPrimes.mp hp).1.pos)
  have hdPos : 0 < d := Nat.pos_of_dvd_of_pos hd hprodPos
  let mulD : ℕ ↪ ℕ :=
    ⟨fun m => d * m, fun _ _ hab =>
      Nat.eq_of_mul_eq_mul_left hdPos hab⟩
  rw [← Finset.sum_filter]
  rw [← selbergReciprocalTotientCarrier_map_mul hd]
  rw [Finset.sum_map]
  apply Finset.sum_congr rfl
  intro m hm
  change f (d * m / d) = f m
  rw [Nat.mul_div_cancel_left m hdPos]

/-- The Möbius factors in a retained multiple `e = d*m` collapse to
`mu(d)`, while the reciprocal totient splits multiplicatively.  This is the
termwise arithmetic identity in the paper's printed `lambda_d`. -/
theorem moebius_mul_moebius_div_totient_of_dvd
    {k d xi e : ℕ} {z : ℝ}
    (hd : d ∣ (siftingPrimes k z).prod id)
    (he : e ∈ selbergReciprocalTotientCarrier k xi z)
    (hde : d ∣ e) :
    (μ (e / d) : ℝ) * (μ e : ℝ) * (1 / (Nat.totient e : ℝ)) =
      (μ d : ℝ) * (1 / (Nat.totient d : ℝ)) *
        (1 / (Nat.totient (e / d) : ℝ)) := by
  have hprodPos : 0 < (siftingPrimes k z).prod id :=
    Finset.prod_pos (fun p hp => (mem_siftingPrimes.mp hp).1.pos)
  have hdPos : 0 < d := Nat.pos_of_dvd_of_pos hd hprodPos
  have heDiv : e ∣ (siftingPrimes k z).prod id :=
    (Nat.mem_divisors.mp
      (Finset.mem_filter.mp he).1).1
  have hePos : 0 < e := Nat.pos_of_dvd_of_pos heDiv hprodPos
  let m := e / d
  have hdm : d * m = e := Nat.mul_div_cancel' hde
  have hmPos : 0 < m := Nat.pos_of_mul_pos_left (hdm ▸ hePos)
  have heSq : Squarefree e :=
    (squarefree_prod_of_primes
      (fun p hp => (mem_siftingPrimes.mp hp).1)).squarefree_of_dvd heDiv
  have hdmSq : Squarefree (d * m) := hdm ▸ heSq
  have hcop : Nat.Coprime d m := Nat.coprime_of_squarefree_mul hdmSq
  have hmSq : Squarefree m := (Nat.squarefree_mul hcop).mp hdmSq |>.2
  have hmu :
      (μ e : ℝ) = (μ d : ℝ) * (μ m : ℝ) := by
    exact_mod_cast
      (show μ e = μ d * μ m by
        rw [← hdm]
        exact
          ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop)
  have hmuSq : (μ m : ℝ) ^ 2 = 1 := by
    exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hmSq
  have hphi :
      (Nat.totient e : ℝ) =
        (Nat.totient d : ℝ) * (Nat.totient m : ℝ) := by
    rw [← hdm, Nat.totient_mul hcop]
    norm_num
  have hphiD : (Nat.totient d : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr hdPos).ne'
  have hphiM : (Nat.totient m : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr hmPos).ne'
  change
    (μ m : ℝ) * (μ e : ℝ) * (1 / (Nat.totient e : ℝ)) =
      (μ d : ℝ) * (1 / (Nat.totient d : ℝ)) *
        (1 / (Nat.totient m : ℝ))
  rw [hmu, hphi]
  field_simp [hphiD, hphiM]
  rw [hmuSq, one_mul]

/-- The paper's finite reciprocal-totient sum
`S_k(xi, z) = sum_{d <= xi, d | P_k(z)} 1 / phi(d)`. -/
noncomputable def selbergReciprocalTotientSum
    (k xi : ℕ) (z : ℝ) : ℝ :=
  ∑ d ∈ selbergReciprocalTotientCarrier k xi z,
    1 / (Nat.totient d : ℝ)

/-- Lemma 3.1 `(3.3)` at a natural cutoff: grouping smooth integers by
their largest squarefree divisor gives `T(x,z) ≤ S₁(x,z)`. -/
theorem selbergSmoothReciprocalSum_le
    (xi : ℕ) (z : ℝ) :
    selbergSmoothReciprocalSum xi z ≤
      selbergReciprocalTotientSum 1 xi z := by
  rw [selbergSmoothReciprocalSum, selbergReciprocalTotientSum]
  rw [← Finset.sum_fiberwise_of_maps_to
    (s := selbergPsiCarrier xi z)
    (t := selbergReciprocalTotientCarrier 1 xi z)
    (g := UniqueFactorizationMonoid.radical)
    (fun n hn => radical_mem_selbergReciprocalTotientCarrier hn)
    (fun n => 1 / (n : ℝ))]
  apply Finset.sum_le_sum
  intro q hq
  apply sum_reciprocal_of_radical_eq_le
  · have hqDiv :
        q ∣ (siftingPrimes 1 z).prod id :=
      (Nat.mem_divisors.mp
        (Finset.mem_filter.mp hq).1).1
    exact
      (squarefree_prod_of_primes
        (fun p hp => (mem_siftingPrimes.mp hp).1)).squarefree_of_dvd hqDiv
  · intro n hn
    have hnCarrier := (Finset.mem_filter.mp hn).1
    exact ((Finset.mem_filter.mp hnCarrier).1 |> Finset.mem_Icc.mp).1
  · intro n hn
    exact (Finset.mem_filter.mp hn).2

theorem selbergReciprocalTotientSum_congr_siftingPrimes
    {k₁ k₂ xi : ℕ} {z : ℝ}
    (h : siftingPrimes k₁ z = siftingPrimes k₂ z) :
    selbergReciprocalTotientSum k₁ xi z =
      selbergReciprocalTotientSum k₂ xi z := by
  simp only [selbergReciprocalTotientSum,
    selbergReciprocalTotientCarrier, h]

/-- Increasing the truncation level only adds nonnegative
reciprocal-totient terms. -/
theorem selbergReciprocalTotientSum_mono
    (k : ℕ) (z : ℝ) {xi₁ xi₂ : ℕ} (hxi : xi₁ ≤ xi₂) :
    selbergReciprocalTotientSum k xi₁ z ≤
      selbergReciprocalTotientSum k xi₂ z := by
  unfold selbergReciprocalTotientSum
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro d hd
    rw [selbergReciprocalTotientCarrier, Finset.mem_filter] at hd ⊢
    exact ⟨hd.1, hd.2.trans hxi⟩
  · intro d hd₂ hd₁
    positivity

/-- A truncated reciprocal-totient divisor sum over a coprime product splits
into disjoint packets indexed by the divisor from the second factor. -/
theorem reciprocalTotientSum_coprime_mul_decomposition
    {P d xi : ℕ} (hcop : Nat.Coprime P d) :
    (∑ n ∈ (P * d).divisors.filter (fun n => n ≤ xi),
        1 / (Nat.totient n : ℝ)) =
      ∑ t ∈ d.divisors, 1 / (Nat.totient t : ℝ) *
        ∑ m ∈ P.divisors.filter (fun m => m ≤ xi / t),
          1 / (Nat.totient m : ℝ) := by
  rw [hcop.divisors_mul, Finset.filter_map, Finset.sum_map]
  calc
    (∑ x ∈ (P.divisors ×ˢ d.divisors).attach with
        x.val.1 * x.val.2 ≤ xi,
        1 / (Nat.totient (x.val.1 * x.val.2) : ℝ)) =
        ∑ x ∈ P.divisors ×ˢ d.divisors,
          if x.1 * x.2 ≤ xi then
            1 / (Nat.totient (x.1 * x.2) : ℝ) else 0 := by
      rw [Finset.sum_filter]
      simpa using
        Finset.sum_attach (P.divisors ×ˢ d.divisors)
          (fun x => if x.1 * x.2 ≤ xi then
            1 / (Nat.totient (x.1 * x.2) : ℝ) else 0)
    _ = ∑ t ∈ d.divisors, ∑ m ∈ P.divisors,
        if m * t ≤ xi then
          1 / (Nat.totient (m * t) : ℝ) else 0 := by
      rw [Finset.sum_product_right]
    _ = ∑ t ∈ d.divisors, 1 / (Nat.totient t : ℝ) *
        ∑ m ∈ P.divisors.filter (fun m => m ≤ xi / t),
          1 / (Nat.totient m : ℝ) := by
      apply Finset.sum_congr rfl
      intro t ht
      have htData := Nat.mem_divisors.mp ht
      have htPos : 0 < t :=
        Nat.pos_of_dvd_of_pos htData.1 (Nat.pos_of_ne_zero htData.2)
      rw [Finset.mul_sum, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro m hm
      have hmData := Nat.mem_divisors.mp hm
      have hmt : Nat.Coprime m t :=
        (hcop.coprime_dvd_left hmData.1).coprime_dvd_right htData.1
      have hcut : m ≤ xi / t ↔ m * t ≤ xi :=
        Nat.le_div_iff_mul_le htPos
      by_cases h : m * t ≤ xi
      · rw [if_pos h, if_pos (hcut.mpr h), Nat.totient_mul hmt]
        push_cast
        ring
      · rw [if_neg h, if_neg (fun hmLe => h (hcut.mp hmLe))]

/-- Reciprocal totient as an arithmetic function, used only to evaluate the
finite divisor packet in Lemma 3.1. -/
noncomputable def reciprocalTotientArithmeticFunction :
    ArithmeticFunction ℝ where
  toFun := fun n => 1 / (Nat.totient n : ℝ)
  map_zero' := by simp

@[simp]
theorem reciprocalTotientArithmeticFunction_apply (n : ℕ) :
    reciprocalTotientArithmeticFunction n =
      1 / (Nat.totient n : ℝ) := rfl

theorem reciprocalTotientArithmeticFunction_isMultiplicative :
    reciprocalTotientArithmeticFunction.IsMultiplicative := by
  refine ⟨by simp, ?_⟩
  intro m n hcop
  rw [reciprocalTotientArithmeticFunction_apply,
    reciprocalTotientArithmeticFunction_apply,
    reciprocalTotientArithmeticFunction_apply, Nat.totient_mul hcop]
  push_cast
  ring

/-- On a squarefree divisor packet, the total reciprocal-totient weight is
exactly `d / phi(d)`. -/
theorem sum_reciprocalTotient_divisors_eq
    {d : ℕ} (hd : Squarefree d) :
    (∑ t ∈ d.divisors, 1 / (Nat.totient t : ℝ)) =
      (d : ℝ) / (Nat.totient d : ℝ) := by
  have hpacket :=
    ArithmeticFunction.IsMultiplicative.prodPrimeFactors_one_add_of_squarefree
      reciprocalTotientArithmeticFunction_isMultiplicative hd
  have htotient :
      (∏ p ∈ d.primeFactors, ((p : ℝ) - 1)) =
        (Nat.totient d : ℝ) := by
    rw [AnalyticNumberTheory.Sieve.totient_eq_prod_primeFactors_of_squarefree hd]
    push_cast
    apply Finset.prod_congr rfl
    intro p hp
    rw [Nat.cast_sub (Nat.prime_of_mem_primeFactors hp).one_le]
    norm_num
  have hproduct :
      (∏ p ∈ d.primeFactors, (p : ℝ)) = (d : ℝ) := by
    rw [← Nat.cast_prod (R := ℝ) (fun p : ℕ => p) d.primeFactors]
    exact_mod_cast Nat.prod_primeFactors_of_squarefree hd
  calc
    (∑ t ∈ d.divisors, 1 / (Nat.totient t : ℝ)) =
        ∏ p ∈ d.primeFactors,
          (1 + reciprocalTotientArithmeticFunction p) := by
      simpa only [reciprocalTotientArithmeticFunction_apply] using
        hpacket.symm
    _ = ∏ p ∈ d.primeFactors, (p : ℝ) / ((p : ℝ) - 1) := by
      apply Finset.prod_congr rfl
      intro p hp
      have hpPrime := Nat.prime_of_mem_primeFactors hp
      rw [reciprocalTotientArithmeticFunction_apply,
        Nat.totient_prime hpPrime, Nat.cast_sub hpPrime.one_le]
      have hpNe : (p : ℝ) - 1 ≠ 0 :=
        sub_ne_zero.mpr (ne_of_gt (by exact_mod_cast hpPrime.one_lt))
      field_simp [hpNe]
      ring
    _ = (∏ p ∈ d.primeFactors, (p : ℝ)) /
        ∏ p ∈ d.primeFactors, ((p : ℝ) - 1) := by
      rw [Finset.prod_div_distrib]
    _ = (d : ℝ) / (Nat.totient d : ℝ) := by
      rw [hproduct, htotient]

/-- The exact divisor-packet decomposition `(3.4)` of Lemma 3.1.  The packet
indexed by `t | d` contains the unique divisor whose `d`-part is `t`. -/
theorem selbergReciprocalTotientSum_eq_divisorPackets
    {k d xi : ℕ} {z : ℝ}
    (hd : d ∣ (siftingPrimes k z).prod id) :
    selbergReciprocalTotientSum k xi z =
      ∑ t ∈ d.divisors, 1 / (Nat.totient t : ℝ) *
        selbergReciprocalTotientSum (k * d) (xi / t) z := by
  have hprodSq : Squarefree ((siftingPrimes k z).prod id) :=
    squarefree_prod_of_primes
      (fun p hp => (mem_siftingPrimes.mp hp).1)
  have hfactor :=
    siftingPrimes_mul_prod_mul (k := k) (d := d) (z := z) hd
  have hfactorSq :
      Squarefree ((siftingPrimes (k * d) z).prod id * d) := by
    rw [hfactor]
    exact hprodSq
  have hcop :
      Nat.Coprime ((siftingPrimes (k * d) z).prod id) d :=
    Nat.coprime_of_squarefree_mul hfactorSq
  simpa only [selbergReciprocalTotientSum,
    selbergReciprocalTotientCarrier, hfactor] using
    reciprocalTotientSum_coprime_mul_decomposition
      (P := (siftingPrimes (k * d) z).prod id)
      (d := d) (xi := xi) hcop

/-- The natural-cutoff form of Lemma 3.1 `(3.1)`.  It follows from the exact
packet decomposition `(3.4)`, monotonicity in the cutoff, and the packet mass
`sum_{t | d} 1 / phi(t) = d / phi(d)`. -/
theorem mul_selbergReciprocalTotientSum_le
    {k d xi : ℕ} {z : ℝ}
    (hd : d ∣ (siftingPrimes k z).prod id) :
    (d : ℝ) / (Nat.totient d : ℝ) *
        selbergReciprocalTotientSum (k * d) (xi / d) z ≤
      selbergReciprocalTotientSum k xi z := by
  have hprodPos : 0 < (siftingPrimes k z).prod id :=
    Finset.prod_pos (fun p hp => (mem_siftingPrimes.mp hp).1.pos)
  have hdPos : 0 < d := Nat.pos_of_dvd_of_pos hd hprodPos
  have hdSq : Squarefree d :=
    (squarefree_prod_of_primes
      (fun p hp => (mem_siftingPrimes.mp hp).1)).squarefree_of_dvd hd
  calc
    (d : ℝ) / (Nat.totient d : ℝ) *
        selbergReciprocalTotientSum (k * d) (xi / d) z =
        (∑ t ∈ d.divisors, 1 / (Nat.totient t : ℝ)) *
          selbergReciprocalTotientSum (k * d) (xi / d) z := by
      rw [sum_reciprocalTotient_divisors_eq hdSq]
    _ = ∑ t ∈ d.divisors, 1 / (Nat.totient t : ℝ) *
          selbergReciprocalTotientSum (k * d) (xi / d) z := by
      rw [Finset.sum_mul]
    _ ≤ ∑ t ∈ d.divisors, 1 / (Nat.totient t : ℝ) *
          selbergReciprocalTotientSum (k * d) (xi / t) z := by
      apply Finset.sum_le_sum
      intro t ht
      have htData := Nat.mem_divisors.mp ht
      have htPos : 0 < t :=
        Nat.pos_of_dvd_of_pos htData.1 hdPos
      have htd : t ≤ d := Nat.le_of_dvd hdPos htData.1
      exact mul_le_mul_of_nonneg_left
        (selbergReciprocalTotientSum_mono (k * d) z
          (Nat.div_le_div_left htd htPos))
        (by positivity)
    _ = selbergReciprocalTotientSum k xi z :=
      (selbergReciprocalTotientSum_eq_divisorPackets hd).symm

/-- Formula `(3.4)` also gives the reverse comparison needed in `(3.2)`:
restoring every prime omitted by `k` costs at most the complete packet factor
`d / phi(d)`. -/
theorem selbergReciprocalTotientSum_one_le_excludedFactor
    (k xi : ℕ) (z : ℝ) :
    selbergReciprocalTotientSum 1 xi z ≤
      (excludedSiftingFactor k z : ℝ) /
          (Nat.totient (excludedSiftingFactor k z) : ℝ) *
        selbergReciprocalTotientSum k xi z := by
  let d := excludedSiftingFactor k z
  have hd :
      d ∣ (siftingPrimes 1 z).prod id :=
    excludedSiftingFactor_dvd_siftingPrimes_one k z
  have hprodPos : 0 < (siftingPrimes 1 z).prod id :=
    Finset.prod_pos (fun p hp => (mem_siftingPrimes.mp hp).1.pos)
  have hdPos : 0 < d := Nat.pos_of_dvd_of_pos hd hprodPos
  have hdSq : Squarefree d :=
    (squarefree_prod_of_primes
      (fun p hp => (mem_siftingPrimes.mp hp).1)).squarefree_of_dvd hd
  calc
    selbergReciprocalTotientSum 1 xi z =
        ∑ t ∈ d.divisors, 1 / (Nat.totient t : ℝ) *
          selbergReciprocalTotientSum (1 * d) (xi / t) z :=
      selbergReciprocalTotientSum_eq_divisorPackets hd
    _ ≤ ∑ t ∈ d.divisors, 1 / (Nat.totient t : ℝ) *
          selbergReciprocalTotientSum (1 * d) xi z := by
      apply Finset.sum_le_sum
      intro t ht
      exact mul_le_mul_of_nonneg_left
        (selbergReciprocalTotientSum_mono (1 * d) z
          (Nat.div_le_self xi t))
        (by positivity)
    _ = (∑ t ∈ d.divisors, 1 / (Nat.totient t : ℝ)) *
          selbergReciprocalTotientSum (1 * d) xi z := by
      rw [Finset.sum_mul]
    _ = (d : ℝ) / (Nat.totient d : ℝ) *
          selbergReciprocalTotientSum (1 * d) xi z := by
      rw [sum_reciprocalTotient_divisors_eq hdSq]
    _ = (excludedSiftingFactor k z : ℝ) /
          (Nat.totient (excludedSiftingFactor k z) : ℝ) *
        selbergReciprocalTotientSum k xi z := by
      dsimp only [d]
      congr 1
      exact selbergReciprocalTotientSum_congr_siftingPrimes
        (by simpa only [one_mul] using
          siftingPrimes_excludedSiftingFactor k z)

/-- The natural-cutoff form of Lemma 3.1 `(3.2)`. -/
theorem sieveProduct_one_mul_selbergReciprocalTotientSum_le
    (k xi : ℕ) (z : ℝ) :
    sieveProduct 1 z * selbergReciprocalTotientSum 1 xi z ≤
      sieveProduct k z * selbergReciprocalTotientSum k xi z := by
  let d := excludedSiftingFactor k z
  have hd :
      d ∣ (siftingPrimes 1 z).prod id :=
    excludedSiftingFactor_dvd_siftingPrimes_one k z
  have hprodPos : 0 < (siftingPrimes 1 z).prod id :=
    Finset.prod_pos (fun p hp => (mem_siftingPrimes.mp hp).1.pos)
  have hdPos : 0 < d := Nat.pos_of_dvd_of_pos hd hprodPos
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast hdPos.ne'
  have hphiPos : 0 < Nat.totient d := Nat.totient_pos.mpr hdPos
  have hphi0 : (Nat.totient d : ℝ) ≠ 0 := by
    exact_mod_cast hphiPos.ne'
  calc
    sieveProduct 1 z * selbergReciprocalTotientSum 1 xi z ≤
        sieveProduct 1 z *
          ((d : ℝ) / (Nat.totient d : ℝ) *
            selbergReciprocalTotientSum k xi z) :=
      mul_le_mul_of_nonneg_left
        (selbergReciprocalTotientSum_one_le_excludedFactor k xi z)
        (sieveProduct_pos 1 z).le
    _ = sieveProduct k z * selbergReciprocalTotientSum k xi z := by
      rw [sieveProduct_one_eq_mul_excludedFactor]
      change
        sieveProduct k z * ((Nat.totient d : ℝ) / (d : ℝ)) *
            ((d : ℝ) / (Nat.totient d : ℝ) *
              selbergReciprocalTotientSum k xi z) =
          sieveProduct k z * selbergReciprocalTotientSum k xi z
      field_simp [hd0, hphi0]

/-- Combining `(3.2)` and `(3.3)` at a natural cutoff gives the normalized
smooth-number comparison at the end of Lemma 3.1. -/
theorem sieveProduct_one_mul_selbergSmoothReciprocalSum_le
    (k xi : ℕ) (z : ℝ) :
    sieveProduct 1 z * selbergSmoothReciprocalSum xi z ≤
      sieveProduct k z * selbergReciprocalTotientSum k xi z := by
  exact
    (mul_le_mul_of_nonneg_left
      (selbergSmoothReciprocalSum_le xi z)
      (sieveProduct_pos 1 z).le).trans
      (sieveProduct_one_mul_selbergReciprocalTotientSum_le k xi z)

/-- The complete finite Möbius packet in the truncated optimizer is the
reciprocal-totient sum for the conditioned modulus `k*d`. -/
theorem selbergMoebiusPacket_eq
    {k d xi : ℕ} {z : ℝ}
    (hd : d ∣ (siftingPrimes k z).prod id) :
    (∑ e ∈ selbergReciprocalTotientCarrier k xi z,
        if d ∣ e then
          (μ (e / d) : ℝ) * (μ e : ℝ) *
            (1 / (Nat.totient e : ℝ))
        else 0) =
      (μ d : ℝ) * (1 / (Nat.totient d : ℝ)) *
        selbergReciprocalTotientSum (k * d) (xi / d) z := by
  calc
    (∑ e ∈ selbergReciprocalTotientCarrier k xi z,
        if d ∣ e then
          (μ (e / d) : ℝ) * (μ e : ℝ) *
            (1 / (Nat.totient e : ℝ))
        else 0) =
        ∑ e ∈ selbergReciprocalTotientCarrier k xi z,
          if d ∣ e then
            (μ d : ℝ) * (1 / (Nat.totient d : ℝ)) *
              (1 / (Nat.totient (e / d) : ℝ))
          else 0 := by
      apply Finset.sum_congr rfl
      intro e he
      split_ifs with hde
      · exact moebius_mul_moebius_div_totient_of_dvd hd he hde
      · rfl
    _ = (μ d : ℝ) * (1 / (Nat.totient d : ℝ)) *
        (∑ e ∈ selbergReciprocalTotientCarrier k xi z,
          if d ∣ e then 1 / (Nat.totient (e / d) : ℝ) else 0) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e he
      split_ifs <;> ring
    _ = (μ d : ℝ) * (1 / (Nat.totient d : ℝ)) *
        selbergReciprocalTotientSum (k * d) (xi / d) z := by
      apply congrArg
        (fun x : ℝ => (μ d : ℝ) * (1 / (Nat.totient d : ℝ)) * x)
      simpa [selbergReciprocalTotientSum] using
        (sum_selbergReciprocalTotientCarrier_if_dvd
          (k := k) (d := d) (xi := xi) (z := z) hd
          (fun m => 1 / (Nat.totient m : ℝ)))

/-- The independently truncated Selberg denominator is literally the source
sum `S_k(xi, z)`. -/
theorem RegularSource.levelSelbergDenominator_eq_reciprocalTotientSum
    (source : RegularSource) (z : ℝ) (xi : ℕ) :
    source.levelSelbergDenominator z xi =
      selbergReciprocalTotientSum source.k xi z := by
  unfold RegularSource.levelSelbergDenominator
    LiuWeight.truncatedSelbergDenominator
    LiuWeight.truncatedSelbergCarrier
    selbergReciprocalTotientSum
    selbergReciprocalTotientCarrier
  apply Finset.sum_congr rfl
  intro d hd
  apply RegularSource.boundingSieve_selbergTerm_of_dvd source z
  simpa [RegularSource.boundingSieve] using
    (Nat.mem_divisors.mp (Finset.mem_filter.mp hd).1).1

/-- The cutoff-supported Selberg weight attached to the literal regular
source.  Its support level `xi` is independent of the sifting cutoff `z`. -/
noncomputable def RegularSource.levelSelbergWeight
    (source : RegularSource) (z : ℝ) (xi : ℕ) : ℕ → ℝ :=
  LiuWeight.truncatedSelbergOptimalLambda (source.boundingSieve z) xi

/-- On its source support, the independently constructed optimizer is exactly
the paper's printed coefficient
`mu(d) * d / phi(d) * S_(k*d)(xi/d,z) / S_k(xi,z)`. -/
theorem RegularSource.levelSelbergWeight_eq_printed
    (source : RegularSource) (z : ℝ) {xi d : ℕ}
    (hd : d ∣ (siftingPrimes source.k z).prod id) (hdxi : d ≤ xi) :
    source.levelSelbergWeight z xi d =
      (μ d : ℝ) * (d : ℝ) / (Nat.totient d : ℝ) *
        (selbergReciprocalTotientSum (source.k * d) (xi / d) z /
          selbergReciprocalTotientSum source.k xi z) := by
  have hprodPos : 0 < (siftingPrimes source.k z).prod id :=
    Finset.prod_pos (fun p hp => (mem_siftingPrimes.mp hp).1.pos)
  have hdPos : 0 < d := Nat.pos_of_dvd_of_pos hd hprodPos
  have hdMem :
      d ∈ LiuWeight.truncatedSelbergCarrier
        (source.boundingSieve z) xi := by
    rw [LiuWeight.truncatedSelbergCarrier, Finset.mem_filter,
      Nat.mem_divisors]
    exact
      ⟨⟨by simpa [RegularSource.boundingSieve] using hd,
        by simpa [RegularSource.boundingSieve] using Nat.ne_of_gt hprodPos⟩,
        hdxi⟩
  have hsum :
      (∑ e ∈ LiuWeight.truncatedSelbergCarrier
          (source.boundingSieve z) xi,
        if d ∣ e then
          (μ (e / d) : ℝ) *
            LiuWeight.truncatedSelbergOptimalX
              (source.boundingSieve z) xi e
        else 0) =
      ((μ d : ℝ) * (1 / (Nat.totient d : ℝ)) *
        selbergReciprocalTotientSum
          (source.k * d) (xi / d) z) /
        selbergReciprocalTotientSum source.k xi z := by
    rw [← selbergMoebiusPacket_eq
      (k := source.k) (d := d) (xi := xi) (z := z) hd]
    rw [Finset.sum_div]
    change
      (∑ e ∈ selbergReciprocalTotientCarrier source.k xi z,
        if d ∣ e then
          (μ (e / d) : ℝ) *
            LiuWeight.truncatedSelbergOptimalX
              (source.boundingSieve z) xi e
        else 0) =
      ∑ e ∈ selbergReciprocalTotientCarrier source.k xi z,
        (if d ∣ e then
          (μ (e / d) : ℝ) * (μ e : ℝ) *
            (1 / (Nat.totient e : ℝ))
        else 0) /
          selbergReciprocalTotientSum source.k xi z
    apply Finset.sum_congr rfl
    intro e he
    by_cases hde : d ∣ e
    · rw [if_pos hde, if_pos hde,
        LiuWeight.truncatedSelbergOptimalX]
      have heMem :
          e ∈ LiuWeight.truncatedSelbergCarrier
            (source.boundingSieve z) xi := by
        simpa [LiuWeight.truncatedSelbergCarrier,
          selbergReciprocalTotientCarrier,
          RegularSource.boundingSieve] using he
      rw [if_pos heMem]
      have heDiv : e ∣ (siftingPrimes source.k z).prod id :=
        (Nat.mem_divisors.mp (Finset.mem_filter.mp he).1).1
      rw [source.boundingSieve_selbergTerm_of_dvd z heDiv]
      change
        (μ (e / d) : ℝ) *
            ((μ e : ℝ) * (1 / (Nat.totient e : ℝ)) /
              source.levelSelbergDenominator z xi) =
          (μ (e / d) : ℝ) * (μ e : ℝ) *
            (1 / (Nat.totient e : ℝ)) /
              selbergReciprocalTotientSum source.k xi z
      rw [source.levelSelbergDenominator_eq_reciprocalTotientSum z xi]
      ring
    · simp [hde]
  rw [RegularSource.levelSelbergWeight,
    LiuWeight.truncatedSelbergOptimalLambda, if_pos hdMem, hsum,
    source.boundingSieve_nu_apply z hdPos]
  field_simp

/-- The level denominator is positive as soon as the source cutoff contains
the divisor `1`. -/
theorem RegularSource.levelSelbergDenominator_pos
    (source : RegularSource) (z : ℝ) {xi : ℕ} (hxi : 1 ≤ xi) :
    0 < source.levelSelbergDenominator z xi := by
  exact
    LiuWeight.truncatedSelbergDenominator_pos
      (source.boundingSieve z) hxi

/-- The source's finite level weight has the normalization `lambda_1 = 1`. -/
theorem RegularSource.levelSelbergWeight_one
    (source : RegularSource) (z : ℝ) {xi : ℕ} (hxi : 1 ≤ xi) :
    source.levelSelbergWeight z xi 1 = 1 := by
  exact
    LiuWeight.truncatedSelbergOptimalLambda_one
      (source.boundingSieve z) hxi

/-- Every nonzero source weight is a divisor of the actual sifting product and
is supported at the independent level `d ≤ xi`. -/
theorem RegularSource.levelSelbergWeight_support
    (source : RegularSource) (z : ℝ) {xi d : ℕ}
    (hd : source.levelSelbergWeight z xi d ≠ 0) :
    d ∣ (siftingPrimes source.k z).prod id ∧ d ≤ xi := by
  exact LiuWeight.truncatedSelbergOptimalLambda_support hd

/-- Off the literal divisor carrier or beyond `xi`, the source weight is
identically zero. -/
theorem RegularSource.levelSelbergWeight_eq_zero_of_not_support
    (source : RegularSource) (z : ℝ) {xi d : ℕ}
    (hd : ¬(d ∣ (siftingPrimes source.k z).prod id ∧ d ≤ xi)) :
    source.levelSelbergWeight z xi d = 0 := by
  by_contra hne
  exact hd (source.levelSelbergWeight_support z hne)

/-- The source's explicit finite Selberg weight satisfies the classical
coefficient bound `|lambda_d| ≤ 1`. -/
theorem RegularSource.abs_levelSelbergWeight_le_one
    (source : RegularSource) (z : ℝ) {xi : ℕ} (hxi : 1 ≤ xi) (d : ℕ) :
    |source.levelSelbergWeight z xi d| ≤ 1 := by
  exact
    LiuWeight.abs_truncatedSelbergOptimalLambda_le_one
      (source.boundingSieve z) hxi

/-- Enlarging each `Lambda^2` fiber to the complete divisor carrier and then
collapsing the unique least-common-multiple fiber bounds its coefficient mass
by the square of the `lambda` mass. -/
private theorem sum_abs_lambdaSquared_le_sq
    {P : ℕ} (hP : P ≠ 0) (w : ℕ → ℝ) :
    (∑ d ∈ P.divisors, |BoundingSieve.lambdaSquared w d|) ≤
      (∑ d ∈ P.divisors, |w d|) ^ 2 := by
  have largerSum (f : ℕ → ℕ → ℕ → ℝ) :
      (∑ d ∈ P.divisors, ∑ d1 ∈ d.divisors, ∑ d2 ∈ d.divisors,
        if d = Nat.lcm d1 d2 then f d1 d2 d else 0) =
      ∑ d ∈ P.divisors, ∑ d1 ∈ P.divisors, ∑ d2 ∈ P.divisors,
        if d = Nat.lcm d1 d2 then f d1 d2 d else 0 := by
    congr! 1 with d hd
    rw [Nat.mem_divisors] at hd
    suffices ∀ d1 d2,
        (d1 ∣ d ∧ d2 ∣ d ∧ d = d1.lcm d2) = (d = d1.lcm d2) by
      simp_rw [← Nat.divisors_filter_dvd_of_dvd hd.2 hd.1,
        Finset.sum_filter, Finset.ite_sum_zero, ← ite_and, this]
    simp +contextual [← and_assoc, Nat.dvd_lcm_left, Nat.dvd_lcm_right]
  have habs (d : ℕ) :
      |∑ d1 ∈ d.divisors, ∑ d2 ∈ d.divisors,
          if d = Nat.lcm d1 d2 then w d1 * w d2 else 0| ≤
        ∑ d1 ∈ d.divisors, ∑ d2 ∈ d.divisors,
          if d = Nat.lcm d1 d2 then |w d1 * w d2| else 0 := by
    calc
      |∑ d1 ∈ d.divisors, ∑ d2 ∈ d.divisors,
          if d = Nat.lcm d1 d2 then w d1 * w d2 else 0| ≤
          ∑ d1 ∈ d.divisors,
            |∑ d2 ∈ d.divisors,
              if d = Nat.lcm d1 d2 then w d1 * w d2 else 0| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ d1 ∈ d.divisors, ∑ d2 ∈ d.divisors,
          |if d = Nat.lcm d1 d2 then w d1 * w d2 else 0| := by
        apply Finset.sum_le_sum
        intro d1 hd1
        exact Finset.abs_sum_le_sum_abs _ _
      _ = ∑ d1 ∈ d.divisors, ∑ d2 ∈ d.divisors,
          if d = Nat.lcm d1 d2 then |w d1 * w d2| else 0 := by
        apply Finset.sum_congr rfl
        intro d1 hd1
        apply Finset.sum_congr rfl
        intro d2 hd2
        split_ifs <;> simp [abs_mul]
  unfold BoundingSieve.lambdaSquared
  calc
    (∑ d ∈ P.divisors,
      |∑ d1 ∈ d.divisors, ∑ d2 ∈ d.divisors,
          if d = Nat.lcm d1 d2 then w d1 * w d2 else 0|) ≤
        ∑ d ∈ P.divisors, ∑ d1 ∈ d.divisors, ∑ d2 ∈ d.divisors,
          if d = Nat.lcm d1 d2 then |w d1 * w d2| else 0 := by
      apply Finset.sum_le_sum
      intro d hd
      exact habs d
    _ = ∑ d ∈ P.divisors, ∑ d1 ∈ P.divisors, ∑ d2 ∈ P.divisors,
        if d = Nat.lcm d1 d2 then |w d1 * w d2| else 0 :=
      largerSum (fun d1 d2 _ => |w d1 * w d2|)
    _ = ∑ d1 ∈ P.divisors, ∑ d2 ∈ P.divisors, |w d1 * w d2| := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro d1 hd1
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro d2 hd2
      rw [Finset.sum_ite_eq_of_mem']
      rw [Nat.mem_divisors, Nat.lcm_dvd_iff]
      exact
        ⟨⟨Nat.dvd_of_mem_divisors hd1, Nat.dvd_of_mem_divisors hd2⟩, hP⟩
    _ = (∑ d ∈ P.divisors, |w d|) ^ 2 := by
      simp_rw [abs_mul, sq, Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro d1 hd1
      apply Finset.sum_congr rfl
      intro d2 hd2
      ring

/-- The total absolute mass of the printed level weight is bounded by the
source smooth-number count `Psi(xi, z)`. -/
theorem RegularSource.sum_abs_levelSelbergWeight_le_psi
    (source : RegularSource) {z : ℝ} (hz : 1 < z)
    {xi : ℕ} (hxi : 1 ≤ xi) :
    (∑ d ∈ ((siftingPrimes source.k z).prod id).divisors,
      |source.levelSelbergWeight z xi d|) ≤ selbergPsi xi z := by
  have hsumRestrict :
      (∑ d ∈ ((siftingPrimes source.k z).prod id).divisors,
        |source.levelSelbergWeight z xi d|) =
      ∑ d ∈ selbergReciprocalTotientCarrier source.k xi z,
        |source.levelSelbergWeight z xi d| := by
    symm
    apply Finset.sum_subset
    · intro d hd
      exact (Finset.mem_filter.mp hd).1
    · intro d hdDiv hdNot
      have hdNotLe : ¬d ≤ xi := by
        intro hdLe
        exact hdNot (Finset.mem_filter.mpr ⟨hdDiv, hdLe⟩)
      rw [source.levelSelbergWeight_eq_zero_of_not_support z]
      · simp
      · intro hdSupport
        exact hdNotLe hdSupport.2
  rw [hsumRestrict]
  calc
    (∑ d ∈ selbergReciprocalTotientCarrier source.k xi z,
      |source.levelSelbergWeight z xi d|) ≤
        ∑ _d ∈ selbergReciprocalTotientCarrier source.k xi z, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro d hd
      exact source.abs_levelSelbergWeight_le_one z hxi d
    _ = (selbergReciprocalTotientCarrier source.k xi z).card := by simp
    _ ≤ (selbergPsiCarrier xi z).card := by
      exact_mod_cast
        Finset.card_le_card
          (selbergReciprocalTotientCarrier_subset_psiCarrier hz)
    _ = selbergPsi xi z := rfl

/-- The exact coefficient-mass estimate in the proof of Theorem 2:
`sum |Lambda^2(d)| <= Psi(xi, z)^2`. -/
theorem RegularSource.levelSelbergLambdaSquared_mass_le_psi_sq
    (source : RegularSource) {z : ℝ} (hz : 1 < z)
    {xi : ℕ} (hxi : 1 ≤ xi) :
    (∑ d ∈ ((siftingPrimes source.k z).prod id).divisors,
      |BoundingSieve.lambdaSquared
        (source.levelSelbergWeight z xi) d|) ≤
      selbergPsi xi z ^ 2 := by
  have hprodNe : (siftingPrimes source.k z).prod id ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr
      (fun p hp => (mem_siftingPrimes.mp hp).1.ne_zero)
  calc
    (∑ d ∈ ((siftingPrimes source.k z).prod id).divisors,
      |BoundingSieve.lambdaSquared
        (source.levelSelbergWeight z xi) d|) ≤
        (∑ d ∈ ((siftingPrimes source.k z).prod id).divisors,
          |source.levelSelbergWeight z xi d|) ^ 2 :=
      sum_abs_lambdaSquared_le_sq hprodNe _
    _ ≤ selbergPsi xi z ^ 2 :=
      pow_le_pow_left₀
        (Finset.sum_nonneg fun _ _ => abs_nonneg _)
        (source.sum_abs_levelSelbergWeight_le_psi hz hxi) 2

/-- Squaring the level-`xi` weight enlarges support only to `xi^2`, and the
resulting modulus still divides the literal sifting product. -/
theorem RegularSource.levelSelbergLambdaSquared_support
    (source : RegularSource) (z : ℝ) {xi d : ℕ}
    (hd :
      BoundingSieve.lambdaSquared
        (source.levelSelbergWeight z xi) d ≠ 0) :
    d ∣ (siftingPrimes source.k z).prod id ∧ d ≤ xi ^ 2 := by
  by_contra hsupport
  apply hd
  unfold BoundingSieve.lambdaSquared
  apply Finset.sum_eq_zero
  intro d1 hd1
  apply Finset.sum_eq_zero
  intro d2 hd2
  by_cases heq : d = Nat.lcm d1 d2
  · rw [if_pos heq]
    by_cases h1 : source.levelSelbergWeight z xi d1 = 0
    · simp [h1]
    by_cases h2 : source.levelSelbergWeight z xi d2 = 0
    · simp [h2]
    have hs1 := source.levelSelbergWeight_support z h1
    have hs2 := source.levelSelbergWeight_support z h2
    have hprodPos : 0 < (siftingPrimes source.k z).prod id :=
      Finset.prod_pos
        (fun p hp => (mem_siftingPrimes.mp hp).1.pos)
    have hd1Pos : 0 < d1 :=
      Nat.pos_of_dvd_of_pos hs1.1 hprodPos
    have hd2Pos : 0 < d2 :=
      Nat.pos_of_dvd_of_pos hs2.1 hprodPos
    have hdDvd : d ∣ (siftingPrimes source.k z).prod id := by
      rw [heq]
      exact Nat.lcm_dvd hs1.1 hs2.1
    have hdLe : d ≤ xi ^ 2 := by
      calc
        d = Nat.lcm d1 d2 := heq
        _ ≤ d1 * d2 := Nat.lcm_le_mul hd1Pos hd2Pos
        _ ≤ xi * xi := Nat.mul_le_mul hs1.2 hs2.2
        _ = xi ^ 2 := by ring
    exact (hsupport ⟨hdDvd, hdLe⟩).elim
  · simp [heq]

/-- The exact level-`xi` Selberg upper bound for the literal source.  Unlike
the full-divisor optimizer above, both the main denominator and the weight are
cut off independently of `z`; no form of `(3.9)` or `(4.2)` is assumed. -/
theorem RegularSource.siftedCount_le_levelSelberg
    (source : RegularSource) (z : ℝ) {xi : ℕ} (hxi : 1 ≤ xi) :
    siftedCount source.carrier source.k z ≤
      source.y * (source.levelSelbergDenominator z xi)⁻¹ +
        ∑ d ∈ ((siftingPrimes source.k z).prod id).divisors,
          |BoundingSieve.lambdaSquared
            (source.levelSelbergWeight z xi) d| := by
  have hUpper :=
    AnalyticNumberTheory.Sieve.omega_upper_bound_via_mathlib
      (source.boundingSieve z) (source.levelSelbergWeight z xi)
      (source.levelSelbergWeight_one z hxi)
  have hErr :=
    source.boundingSieve_errSum_le z
      (BoundingSieve.lambdaSquared (source.levelSelbergWeight z xi))
  rw [source.boundingSieve_siftedSum_eq z] at hUpper
  change
    siftedCount source.carrier source.k z ≤
      (source.boundingSieve z).totalMass *
          (source.boundingSieve z).mainSum
            (BoundingSieve.lambdaSquared
              (LiuWeight.truncatedSelbergOptimalLambda
                (source.boundingSieve z) xi)) +
        (source.boundingSieve z).errSum
          (BoundingSieve.lambdaSquared
            (source.levelSelbergWeight z xi)) at hUpper
  rw [LiuWeight.mainSum_truncatedSelbergOptimalLambda
    (source.boundingSieve z) hxi] at hUpper
  calc
    siftedCount source.carrier source.k z ≤
        source.y * (source.levelSelbergDenominator z xi)⁻¹ +
          (source.boundingSieve z).errSum
            (BoundingSieve.lambdaSquared
              (source.levelSelbergWeight z xi)) := by
      simpa [RegularSource.levelSelbergDenominator,
        RegularSource.levelSelbergWeight, RegularSource.boundingSieve,
        one_div] using hUpper
    _ ≤ source.y * (source.levelSelbergDenominator z xi)⁻¹ +
          ∑ d ∈ ((siftingPrimes source.k z).prod id).divisors,
            |BoundingSieve.lambdaSquared
              (source.levelSelbergWeight z xi) d| := by
      exact add_le_add (le_refl _) hErr

/-- The source-faithful finite Selberg estimate before the analytic lower
bound for `S_k(xi, z)`: its error is exactly bounded by `Psi(xi, z)^2`. -/
theorem RegularSource.siftedCount_le_levelSelberg_psi
    (source : RegularSource) {z : ℝ} (hz : 1 < z)
    {xi : ℕ} (hxi : 1 ≤ xi) :
    siftedCount source.carrier source.k z ≤
      source.y * (source.levelSelbergDenominator z xi)⁻¹ +
        selbergPsi xi z ^ 2 := by
  exact
    (source.siftedCount_le_levelSelberg z hxi).trans
      (add_le_add (le_refl _)
        (source.levelSelbergLambdaSquared_mass_le_psi_sq hz hxi))

/-- The divisor carrier with the paper's real cutoff `d <= xi`. -/
noncomputable def selbergRealReciprocalTotientCarrier
    (k : ℕ) (xi z : ℝ) : Finset ℕ :=
  ((siftingPrimes k z).prod id).divisors.filter (fun d => (d : ℝ) ≤ xi)

/-- The paper's reciprocal-totient sum at a real cutoff. -/
noncomputable def selbergRealReciprocalTotientSum
    (k : ℕ) (xi z : ℝ) : ℝ :=
  ∑ d ∈ selbergRealReciprocalTotientCarrier k xi z,
    1 / (Nat.totient d : ℝ)

/-- The source's `Psi(xi, z)` carrier at a real cutoff. -/
noncomputable def selbergRealPsiCarrier (xi z : ℝ) : Finset ℕ :=
  selbergPsiCarrier ⌊xi⌋₊ z

/-- The source's smooth-number count at a real cutoff. -/
noncomputable def selbergRealPsi (xi z : ℝ) : ℝ :=
  (selbergRealPsiCarrier xi z).card

/-- The source's reciprocal smooth-number sum `T(xi,z)` at a real cutoff. -/
noncomputable def selbergRealSmoothReciprocalSum (xi z : ℝ) : ℝ :=
  selbergSmoothReciprocalSum ⌊xi⌋₊ z

/-- A nonnegative real cutoff selects exactly the divisors selected by its
natural floor. -/
theorem selbergRealReciprocalTotientCarrier_eq_floor
    (k : ℕ) {xi z : ℝ} (hxi : 0 ≤ xi) :
    selbergRealReciprocalTotientCarrier k xi z =
      selbergReciprocalTotientCarrier k ⌊xi⌋₊ z := by
  ext d
  simp only [selbergRealReciprocalTotientCarrier,
    selbergReciprocalTotientCarrier, Finset.mem_filter]
  rw [Nat.le_floor_iff hxi]

/-- Consequently the real-cutoff denominator is the proved natural-cutoff
denominator at `floor xi`. -/
theorem selbergRealReciprocalTotientSum_eq_floor
    (k : ℕ) {xi z : ℝ} (hxi : 0 ≤ xi) :
    selbergRealReciprocalTotientSum k xi z =
      selbergReciprocalTotientSum k ⌊xi⌋₊ z := by
  rw [selbergRealReciprocalTotientSum,
    selbergRealReciprocalTotientCarrier_eq_floor k hxi]
  rfl

/-- Lemma 3.1 `(3.3)` at the paper's real cutoff. -/
theorem selbergRealSmoothReciprocalSum_le
    {xi z : ℝ} (hxi : 0 ≤ xi) :
    selbergRealSmoothReciprocalSum xi z ≤
      selbergRealReciprocalTotientSum 1 xi z := by
  rw [selbergRealSmoothReciprocalSum,
    selbergRealReciprocalTotientSum_eq_floor 1 hxi]
  exact selbergSmoothReciprocalSum_le ⌊xi⌋₊ z

/-- The paper's real-cutoff divisor-packet identity `(3.4)`. -/
theorem selbergRealReciprocalTotientSum_eq_divisorPackets
    {k d : ℕ} {xi z : ℝ} (hxi : 0 ≤ xi)
    (hd : d ∣ (siftingPrimes k z).prod id) :
    selbergRealReciprocalTotientSum k xi z =
      ∑ t ∈ d.divisors, 1 / (Nat.totient t : ℝ) *
        selbergRealReciprocalTotientSum
          (k * d) (xi / (t : ℝ)) z := by
  rw [selbergRealReciprocalTotientSum_eq_floor k hxi,
    selbergReciprocalTotientSum_eq_divisorPackets hd]
  apply Finset.sum_congr rfl
  intro t ht
  have htData := Nat.mem_divisors.mp ht
  have htPos : 0 < t :=
    Nat.pos_of_dvd_of_pos htData.1 (Nat.pos_of_ne_zero htData.2)
  have hxiDiv : 0 ≤ xi / (t : ℝ) :=
    div_nonneg hxi (Nat.cast_nonneg t)
  rw [selbergRealReciprocalTotientSum_eq_floor (k * d) hxiDiv,
    Nat.floor_div_natCast]

/-- The source's real-cutoff Lemma 3.1 inequality `(3.1)`. -/
theorem mul_selbergRealReciprocalTotientSum_le
    {k d : ℕ} {xi z : ℝ} (hxi : 0 ≤ xi)
    (hd : d ∣ (siftingPrimes k z).prod id) :
    (d : ℝ) / (Nat.totient d : ℝ) *
        selbergRealReciprocalTotientSum
          (k * d) (xi / (d : ℝ)) z ≤
      selbergRealReciprocalTotientSum k xi z := by
  have hxiDiv : 0 ≤ xi / (d : ℝ) :=
    div_nonneg hxi (Nat.cast_nonneg d)
  rw [selbergRealReciprocalTotientSum_eq_floor k hxi,
    selbergRealReciprocalTotientSum_eq_floor (k * d) hxiDiv,
    Nat.floor_div_natCast]
  exact mul_selbergReciprocalTotientSum_le hd

/-- The source's real-cutoff Lemma 3.1 comparison `(3.2)`. -/
theorem sieveProduct_one_mul_selbergRealReciprocalTotientSum_le
    (k : ℕ) {xi z : ℝ} (hxi : 0 ≤ xi) :
    sieveProduct 1 z * selbergRealReciprocalTotientSum 1 xi z ≤
      sieveProduct k z * selbergRealReciprocalTotientSum k xi z := by
  rw [selbergRealReciprocalTotientSum_eq_floor 1 hxi,
    selbergRealReciprocalTotientSum_eq_floor k hxi]
  exact sieveProduct_one_mul_selbergReciprocalTotientSum_le k ⌊xi⌋₊ z

/-- The real-cutoff normalized smooth-number comparison obtained by combining
Lemma 3.1 `(3.2)` and `(3.3)`. -/
theorem sieveProduct_one_mul_selbergRealSmoothReciprocalSum_le
    (k : ℕ) {xi z : ℝ} (hxi : 0 ≤ xi) :
    sieveProduct 1 z * selbergRealSmoothReciprocalSum xi z ≤
      sieveProduct k z * selbergRealReciprocalTotientSum k xi z := by
  exact
    (mul_le_mul_of_nonneg_left
      (selbergRealSmoothReciprocalSum_le hxi)
      (sieveProduct_pos 1 z).le).trans
      (sieveProduct_one_mul_selbergRealReciprocalTotientSum_le k hxi)

/-- Membership in the real `Psi` carrier has the literal source inequalities
`1 <= n <= xi` and greatest prime divisor below `z`. -/
theorem mem_selbergRealPsiCarrier
    {n : ℕ} {xi z : ℝ} (hxi : 0 ≤ xi) :
    n ∈ selbergRealPsiCarrier xi z ↔
      1 ≤ n ∧ (n : ℝ) ≤ xi ∧
        (n = 1 → (1 : ℝ) < z) ∧
        ∀ p ∈ n.primeFactors, (p : ℝ) < z := by
  simp only [selbergRealPsiCarrier, selbergPsiCarrier,
    Finset.mem_filter, Finset.mem_Icc]
  rw [Nat.le_floor_iff hxi]
  tauto

/-- The real smooth-number count is exactly the natural count at `floor xi`. -/
theorem selbergRealPsi_eq_floor (xi z : ℝ) :
    selbergRealPsi xi z = selbergPsi ⌊xi⌋₊ z := rfl

/-- The exact finite partial-summation identity used immediately after `(4.4)`
in the source. Both endpoint terms are retained, and the step-function prefix
inside the integral is the literal real `Psi`. -/
theorem selbergSmoothReciprocalSum_sub_eq_psi_div_add_integral
    {n m : ℕ} {z : ℝ} (hz : 1 < z) (hn : 1 ≤ n) (hnm : n ≤ m) :
    selbergSmoothReciprocalSum m z -
        selbergSmoothReciprocalSum n z =
      (selbergPsi m z) / (m : ℝ) -
        (selbergPsi n z) / (n : ℝ) +
        ∫ t in Set.Ioc (n : ℝ) m,
          selbergRealPsi t z / t ^ 2 := by
  rw [selbergSmoothReciprocalSum_sub_eq_sum_Ioc hz hnm]
  have hdiff : ∀ t ∈ Set.Icc (n : ℝ) m,
      DifferentiableAt ℝ (fun u : ℝ => u⁻¹) t := by
    intro t ht
    exact (hasDerivAt_inv (ne_of_gt (lt_of_lt_of_le
      (by exact_mod_cast hn) ht.1))).differentiableAt
  have hpos : ∀ t ∈ Set.Icc (n : ℝ) m, 0 < t := by
    intro t ht
    exact lt_of_lt_of_le (by exact_mod_cast hn) ht.1
  have hgInt : MeasureTheory.IntegrableOn (fun t : ℝ => -(t ^ 2)⁻¹)
      (Set.Icc (n : ℝ) m) :=
    (((continuousOn_pow 2).inv₀ fun t ht =>
      pow_ne_zero 2 (hpos t ht).ne').neg).integrableOn_Icc
  have hint : MeasureTheory.IntegrableOn
      (deriv (fun u : ℝ => u⁻¹)) (Set.Icc (n : ℝ) m) := by
    apply hgInt.congr_fun
    · intro t ht
      exact (hasDerivAt_inv (hpos t ht).ne').deriv.symm
    · exact measurableSet_Icc
  have hAbel := sum_mul_eq_sub_sub_integral_mul'
    (c := selbergSmoothIndicator z) hnm hdiff hint
  rw [sum_Icc_selbergSmoothIndicator hz,
    sum_Icc_selbergSmoothIndicator hz] at hAbel
  rw [hAbel]
  have hderiv : ∀ t ∈ Set.Ioc (n : ℝ) m,
      deriv (fun u : ℝ => u⁻¹) t = -(t ^ 2)⁻¹ := by
    intro t ht
    exact (hasDerivAt_inv (ne_of_gt (lt_of_lt_of_le
      (by exact_mod_cast hn) (le_of_lt ht.1)))).deriv
  have hpref : ∀ t ∈ Set.Ioc (n : ℝ) m,
      ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, selbergSmoothIndicator z k =
        selbergRealPsi t z := by
    intro t ht
    rw [sum_Icc_selbergSmoothIndicator hz, selbergRealPsi_eq_floor]
  have hintegral :
      (∫ t in Set.Ioc (n : ℝ) m,
          deriv (fun u : ℝ => u⁻¹) t *
            ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, selbergSmoothIndicator z k) =
        -(∫ t in Set.Ioc (n : ℝ) m,
          selbergRealPsi t z / t ^ 2) := by
    rw [← MeasureTheory.integral_neg]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    dsimp only
    rw [hderiv t ht, hpref t ht]
    ring
  rw [hintegral]
  ring

/-- The finite Rankin reduction at the source's literal real cutoff.  This
retains the full joint dependence on `xi` and `z`; estimating the displayed
finite-prime product uniformly is the remaining content of `(4.3)`. -/
theorem selbergRealPsi_le_rpow_mul_eulerProduct
    {xi z sigma : ℝ} (hxi : 0 ≤ xi) (hz : 1 < z)
    (hsigma : 0 < sigma) :
    selbergRealPsi xi z ≤
      xi ^ sigma *
        ∏ p ∈ siftingPrimes 1 z,
          (1 - (p : ℝ) ^ (-sigma))⁻¹ := by
  rw [selbergRealPsi_eq_floor]
  have hNatural :=
    selbergPsi_le_rpow_mul_eulerProduct
      (xi := ⌊xi⌋₊) hz hsigma
  refine hNatural.trans ?_
  exact
    mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow (Nat.cast_nonneg ⌊xi⌋₊)
        (Nat.floor_le hxi) hsigma.le)
      (Finset.prod_nonneg fun p hp => by
        have hpPrime := (mem_siftingPrimes.mp hp).1
        have hpReal : (1 : ℝ) < p := by
          exact_mod_cast hpPrime.one_lt
        have hpow : (p : ℝ) ^ (-sigma) < 1 :=
          Real.rpow_lt_one_of_one_lt_of_neg hpReal
            (neg_neg_of_pos hsigma)
        exact inv_nonneg.mpr (sub_nonneg.mpr hpow.le))

/-- A local logarithmic estimate for the finite Euler product. -/
private lemma inv_one_sub_le_exp_four_mul
    {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 3 / 4) :
    (1 - t)⁻¹ ≤ Real.exp (4 * t) := by
  have ht1 : |t| < 1 := by
    rw [abs_of_nonneg ht0]
    linarith
  have hpos : 0 < 1 - t := by linarith
  have hseries := Real.abs_log_sub_add_sum_range_le ht1 0
  simp only [Finset.sum_range_zero, zero_add, pow_one,
    abs_of_nonneg ht0] at hseries
  have hlog : -Real.log (1 - t) ≤ 4 * t := by
    calc
      -Real.log (1 - t) ≤ |Real.log (1 - t)| := neg_le_abs _
      _ ≤ t / (1 - t) := hseries
      _ ≤ 4 * t := by
        rw [div_le_iff₀ hpos]
        nlinarith
  rw [← Real.exp_log (inv_pos.mpr hpos), Real.log_inv]
  exact Real.exp_le_exp.mpr hlog

/-- A finite Euler product is controlled by its first logarithmic moment when
all local terms are at most `3/4`. -/
theorem selbergEulerProduct_le_exp_four_mul
    {z sigma : ℝ}
    (hsmall : ∀ p ∈ siftingPrimes 1 z,
      (p : ℝ) ^ (-sigma) ≤ 3 / 4) :
    (∏ p ∈ siftingPrimes 1 z,
        (1 - (p : ℝ) ^ (-sigma))⁻¹) ≤
      Real.exp (4 * ∑ p ∈ siftingPrimes 1 z,
        (p : ℝ) ^ (-sigma)) := by
  calc
    (∏ p ∈ siftingPrimes 1 z,
        (1 - (p : ℝ) ^ (-sigma))⁻¹) ≤
        ∏ p ∈ siftingPrimes 1 z,
          Real.exp (4 * (p : ℝ) ^ (-sigma)) := by
      apply Finset.prod_le_prod
      · intro p hp
        exact inv_nonneg.mpr (sub_nonneg.mpr (by
          have := hsmall p hp
          linarith))
      · intro p hp
        exact inv_one_sub_le_exp_four_mul
          (Real.rpow_nonneg (Nat.cast_nonneg p) _) (hsmall p hp)
    _ = Real.exp (4 * ∑ p ∈ siftingPrimes 1 z,
        (p : ℝ) ^ (-sigma)) := by
      rw [← Real.exp_sum]
      congr 1
      rw [Finset.mul_sum]

/-- The reciprocal-prime mass on the literal sifting carrier is bounded by
the ordinary harmonic integral estimate. -/
theorem sum_inv_siftingPrimes_le_one_add_log
    {z : ℝ} (hz : 1 ≤ z) :
    ∑ p ∈ siftingPrimes 1 z, 1 / (p : ℝ) ≤ 1 + Real.log z := by
  calc
    ∑ p ∈ siftingPrimes 1 z, 1 / (p : ℝ) ≤
        ∑ n ∈ Finset.Icc 1 ⌊z⌋₊, 1 / (n : ℝ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro p hp
        have hpData := mem_siftingPrimes.mp hp
        exact Finset.mem_Icc.mpr
          ⟨hpData.1.one_le, Nat.le_floor (le_of_lt hpData.2.1)⟩
      · intro n _hnIcc _hnNot
        positivity
    _ = (harmonic ⌊z⌋₊ : ℝ) := by
      rw [harmonic_eq_sum_Icc]
      push_cast
      simp [one_div]
    _ ≤ 1 + Real.log z := by
      exact_mod_cast harmonic_floor_le_one_add_log z hz

/-- Moving the Rankin exponent from `1` by `delta` costs at most `z^delta`
on every prime in the literal sifting carrier. -/
theorem sum_siftingPrimes_rpow_one_sub_le
    {z delta : ℝ} (hz : 1 ≤ z) (hdelta : 0 ≤ delta) :
    (∑ p ∈ siftingPrimes 1 z,
        (p : ℝ) ^ (-(1 - delta))) ≤
      z ^ delta * (1 + Real.log z) := by
  calc
    (∑ p ∈ siftingPrimes 1 z,
        (p : ℝ) ^ (-(1 - delta))) ≤
        z ^ delta *
          ∑ p ∈ siftingPrimes 1 z, 1 / (p : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro p hp
      have hpData := mem_siftingPrimes.mp hp
      have hpPos : (0 : ℝ) < p := by exact_mod_cast hpData.1.pos
      have hpz : (p : ℝ) ≤ z := le_of_lt hpData.2.1
      have hrpow :=
        Real.rpow_le_rpow (le_of_lt hpPos) hpz hdelta
      calc
        (p : ℝ) ^ (-(1 - delta)) =
            (p : ℝ) ^ delta / (p : ℝ) := by
          rw [show -(1 - delta) = delta - 1 by ring,
            Real.rpow_sub_one (ne_of_gt hpPos)]
        _ ≤ z ^ delta / (p : ℝ) :=
          div_le_div_of_nonneg_right hrpow (le_of_lt hpPos)
        _ = z ^ delta * (1 / (p : ℝ)) := by ring
    _ ≤ z ^ delta * (1 + Real.log z) :=
      mul_le_mul_of_nonneg_left
        (sum_inv_siftingPrimes_le_one_add_log hz)
        (Real.rpow_nonneg (le_trans zero_le_one hz) _)

private lemma vinogradov_rankin_prime_power_le
    {z : ℝ} (hlog : 2 ≤ Real.log z)
    {p : ℕ} (hp : p.Prime) :
    (p : ℝ) ^ (-(1 - 1 / Real.log z)) ≤ 3 / 4 := by
  have hlogPos : 0 < Real.log z := lt_of_lt_of_le (by norm_num) hlog
  have hdelta : 1 / Real.log z ≤ 1 / 2 := by
    rw [div_le_div_iff₀ hlogPos (by norm_num : (0 : ℝ) < 2)]
    nlinarith
  have hsigma : (1 / 2 : ℝ) ≤ 1 - 1 / Real.log z := by linarith
  have hsigma0 : 0 ≤ 1 - 1 / Real.log z :=
    le_trans (by norm_num) hsigma
  have hpTwo : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hsqrt : (4 / 3 : ℝ) ≤ Real.sqrt 2 := by
    have hsqrt0 := Real.sqrt_nonneg 2
    have hsqrtSq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    nlinarith
  have hpow : (4 / 3 : ℝ) ≤
      (p : ℝ) ^ (1 - 1 / Real.log z) := by
    calc
      (4 / 3 : ℝ) ≤ Real.sqrt 2 := hsqrt
      _ = (2 : ℝ) ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow 2
      _ ≤ (2 : ℝ) ^ (1 - 1 / Real.log z) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hsigma
      _ ≤ (p : ℝ) ^ (1 - 1 / Real.log z) :=
        Real.rpow_le_rpow (by norm_num) hpTwo hsigma0
  have hpPos : (0 : ℝ) < p := by exact_mod_cast hp.pos
  rw [Real.rpow_neg (le_of_lt hpPos)]
  rw [inv_le_iff_one_le_mul₀ (Real.rpow_pos_of_pos hpPos _)]
  nlinarith

/-- The finite-prime Euler-product estimate at the Vinogradov Rankin exponent
`sigma = 1 - 1 / log z`. This is an unconditional finite estimate; no
smooth-number asymptotic is used in its proof. -/
theorem vinogradovRankinEulerProduct_le
    {z : ℝ} (hz : 1 ≤ z) (hlog : 2 ≤ Real.log z) :
    (∏ p ∈ siftingPrimes 1 z,
        (1 - (p : ℝ) ^ (-(1 - 1 / Real.log z)))⁻¹) ≤
      Real.exp
        (4 * (z ^ (1 / Real.log z) * (1 + Real.log z))) := by
  refine
    (selbergEulerProduct_le_exp_four_mul
      (sigma := 1 - 1 / Real.log z) ?_).trans ?_
  · intro p hp
    exact
      vinogradov_rankin_prime_power_le hlog
        (mem_siftingPrimes.mp hp).1
  · apply Real.exp_le_exp.mpr
    gcongr
    exact sum_siftingPrimes_rpow_one_sub_le hz (by positivity)

/-- The literal real smooth-number count after inserting the Vinogradov
Rankin exponent and the unconditional finite-prime product estimate. -/
theorem selbergRealPsi_le_vinogradovRankin
    {xi z : ℝ} (hxi : 0 ≤ xi) (hz : 1 ≤ z)
    (hlog : 2 ≤ Real.log z) :
    selbergRealPsi xi z ≤
      xi ^ (1 - 1 / Real.log z) *
        Real.exp
          (4 * (z ^ (1 / Real.log z) * (1 + Real.log z))) := by
  have hlogPos : 0 < Real.log z := lt_of_lt_of_le (by norm_num) hlog
  have hdelta : 1 / Real.log z ≤ 1 / 2 := by
    rw [div_le_div_iff₀ hlogPos (by norm_num : (0 : ℝ) < 2)]
    nlinarith
  have hsigma : 0 < 1 - 1 / Real.log z := by linarith
  have hz1 : 1 < z :=
    (Real.log_pos_iff (le_trans zero_le_one hz)).mp hlogPos
  exact
    (selbergRealPsi_le_rpow_mul_eulerProduct hxi hz1 hsigma).trans
      (mul_le_mul_of_nonneg_left
        (vinogradovRankinEulerProduct_le hz hlog)
        (Real.rpow_nonneg hxi _))

/-- The real smooth-number count never exceeds its ambient real cutoff. -/
theorem selbergRealPsi_le_self
    {xi z : ℝ} (hxi : 0 ≤ xi) :
    selbergRealPsi xi z ≤ xi := by
  calc
    selbergRealPsi xi z =
        ((Finset.Icc 1 ⌊xi⌋₊).filter
          (fun n : ℕ => (n = 1 → (1 : ℝ) < z) ∧
            ∀ p : ℕ, p ∈ n.primeFactors → (p : ℝ) < z)).card := rfl
    _ ≤ (Finset.Icc 1 ⌊xi⌋₊).card := by
      exact_mod_cast Finset.card_filter_le
        (Finset.Icc 1 ⌊xi⌋₊)
        (fun n : ℕ => (n = 1 → (1 : ℝ) < z) ∧
          ∀ p : ℕ, p ∈ n.primeFactors → (p : ℝ) < z)
    _ ≤ ⌊xi⌋₊ := by simp
    _ ≤ xi := Nat.floor_le hxi

private lemma vinogradovRankin_expr_eq
    {xi z : ℝ} (hxi : 0 < xi) (hz : 0 < z)
    (hlog : Real.log z ≠ 0) :
    xi ^ (1 - 1 / Real.log z) *
        Real.exp
          (4 * (z ^ (1 / Real.log z) * (1 + Real.log z))) =
      Real.exp
        ((1 - 1 / Real.log z) * Real.log xi +
          4 * (Real.exp 1 * (1 + Real.log z))) := by
  rw [Real.rpow_def_of_pos hxi, Real.rpow_def_of_pos hz]
  have hzexp : Real.log z * (1 / Real.log z) = 1 := by
    field_simp
  rw [hzexp, ← Real.exp_add]
  congr 1
  ring

private lemma rankinLogSq_target_eq
    {xi z : ℝ} (hxi : 0 < xi) :
    Real.exp (24 * Real.exp 1) *
        (xi * Real.exp (-2 * Real.log xi / (Real.log z) ^ 2)) =
      Real.exp
        (24 * Real.exp 1 +
          (Real.log xi + (-2 * Real.log xi / (Real.log z) ^ 2))) := by
  calc
    Real.exp (24 * Real.exp 1) *
        (xi * Real.exp (-2 * Real.log xi / (Real.log z) ^ 2)) =
      Real.exp (24 * Real.exp 1) *
        (Real.exp (Real.log xi) *
          Real.exp (-2 * Real.log xi / (Real.log z) ^ 2)) := by
        rw [Real.exp_log hxi]
    _ = _ := by rw [← Real.exp_add, ← Real.exp_add]

/-- An unconditional logarithmic-square smooth-number estimate on the source's
literal real-cutoff carrier, with an explicit absolute constant.  This is the
weaker Rankin consequence sufficient below; it is not the sharper printed
Vinogradov estimate `(4.3)`, whose denominator is `log z`. -/
theorem selbergRealPsi_le_rankin_logSq
    {xi z : ℝ} (hxi : 1 ≤ xi) (hz : 1 ≤ z)
    (hlog : 2 ≤ Real.log z) :
    selbergRealPsi xi z ≤
      Real.exp (24 * Real.exp 1) *
        (xi * Real.exp (-2 * Real.log xi / (Real.log z) ^ 2)) := by
  have hxiPos : 0 < xi := lt_of_lt_of_le zero_lt_one hxi
  have hzPos : 0 < z := lt_of_lt_of_le zero_lt_one hz
  have hlogPos : 0 < Real.log z := lt_of_lt_of_le (by norm_num) hlog
  have hlogNe : Real.log z ≠ 0 := ne_of_gt hlogPos
  have hlogXi : 0 ≤ Real.log xi := Real.log_nonneg hxi
  by_cases hzFive : Real.log z ≤ 5
  · refine
      (selbergRealPsi_le_vinogradovRankin hxiPos.le hz hlog).trans ?_
    rw [vinogradovRankin_expr_eq hxiPos hzPos hlogNe,
      rankinLogSq_target_eq hxiPos]
    apply Real.exp_le_exp.mpr
    have hcoef : 0 ≤
        1 / Real.log z - 2 / (Real.log z) ^ 2 := by
      rw [show 1 / Real.log z - 2 / (Real.log z) ^ 2 =
        (Real.log z - 2) / (Real.log z) ^ 2 by field_simp]
      positivity
    have hdiff :
        24 * Real.exp 1 +
            (Real.log xi + -2 * Real.log xi / (Real.log z) ^ 2) -
          ((1 - 1 / Real.log z) * Real.log xi +
            4 * (Real.exp 1 * (1 + Real.log z))) =
          4 * Real.exp 1 * (5 - Real.log z) +
            Real.log xi *
              (1 / Real.log z - 2 / (Real.log z) ^ 2) := by ring
    rw [← sub_nonneg, hdiff]
    positivity
  · have hzFive' : 5 ≤ Real.log z := le_of_not_ge hzFive
    by_cases hxiSmall :
        Real.log xi ≤ 8 * Real.exp 1 * (Real.log z) ^ 2
    · refine (selbergRealPsi_le_self hxiPos.le).trans ?_
      rw [rankinLogSq_target_eq hxiPos]
      have hsqPos : 0 < (Real.log z) ^ 2 := sq_pos_of_pos hlogPos
      have hquot :
          2 * Real.log xi / (Real.log z) ^ 2 ≤
            16 * Real.exp 1 := by
        rw [div_le_iff₀ hsqPos]
        nlinarith
      have hmargin :
          0 ≤ 24 * Real.exp 1 -
            2 * Real.log xi / (Real.log z) ^ 2 := by
        nlinarith [Real.exp_pos 1]
      calc
        xi = Real.exp (Real.log xi) := (Real.exp_log hxiPos).symm
        _ ≤ Real.exp
            (24 * Real.exp 1 +
              (Real.log xi +
                (-2 * Real.log xi / (Real.log z) ^ 2))) := by
          apply Real.exp_le_exp.mpr
          rw [show
            24 * Real.exp 1 +
                (Real.log xi +
                  (-2 * Real.log xi / (Real.log z) ^ 2)) =
              Real.log xi +
                (24 * Real.exp 1 -
                  2 * Real.log xi / (Real.log z) ^ 2) by ring]
          linarith
    · refine
        (selbergRealPsi_le_vinogradovRankin hxiPos.le hz hlog).trans ?_
      rw [vinogradovRankin_expr_eq hxiPos hzPos hlogNe,
        rankinLogSq_target_eq hxiPos]
      apply Real.exp_le_exp.mpr
      have hxiLarge :
          8 * Real.exp 1 * (Real.log z) ^ 2 ≤ Real.log xi :=
        le_of_not_ge hxiSmall
      have hcoef : 0 ≤
          1 / Real.log z - 2 / (Real.log z) ^ 2 := by
        rw [show 1 / Real.log z - 2 / (Real.log z) ^ 2 =
          (Real.log z - 2) / (Real.log z) ^ 2 by field_simp]
        positivity
      have hcoefLower :
          8 * Real.exp 1 * (Real.log z - 2) ≤
            Real.log xi *
              (1 / Real.log z - 2 / (Real.log z) ^ 2) := by
        calc
          8 * Real.exp 1 * (Real.log z - 2) =
              (8 * Real.exp 1 * (Real.log z) ^ 2) *
                (1 / Real.log z - 2 / (Real.log z) ^ 2) := by
            field_simp
          _ ≤ Real.log xi *
                (1 / Real.log z - 2 / (Real.log z) ^ 2) :=
            mul_le_mul_of_nonneg_right hxiLarge hcoef
      have hdiff :
          24 * Real.exp 1 +
              (Real.log xi + -2 * Real.log xi / (Real.log z) ^ 2) -
            ((1 - 1 / Real.log z) * Real.log xi +
              4 * (Real.exp 1 * (1 + Real.log z))) =
            4 * Real.exp 1 * (5 - Real.log z) +
              Real.log xi *
                (1 / Real.log z - 2 / (Real.log z) ^ 2) := by ring
      rw [← sub_nonneg, hdiff]
      nlinarith [Real.exp_pos 1]

/-- Dividing the logarithmic-square Rankin estimate by the square from partial
summation gives the power majorant used below. -/
theorem selbergRealPsi_div_sq_le_rankin_logSq
    {t z : ℝ} (ht : 1 ≤ t) (hz : 1 ≤ z)
    (hlog : 2 ≤ Real.log z) :
    selbergRealPsi t z / t ^ 2 ≤
      Real.exp (24 * Real.exp 1) *
        t ^ (-1 - 2 / (Real.log z) ^ 2) := by
  have htPos : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hPsi := selbergRealPsi_le_rankin_logSq ht hz hlog
  have hexp :
      Real.exp (-2 * Real.log t / (Real.log z) ^ 2) =
        t ^ (-2 / (Real.log z) ^ 2) := by
    rw [Real.rpow_def_of_pos htPos]
    congr 1
    ring
  calc
    selbergRealPsi t z / t ^ 2 ≤
        (Real.exp (24 * Real.exp 1) *
          (t * Real.exp (-2 * Real.log t / (Real.log z) ^ 2))) /
            t ^ 2 := div_le_div_of_nonneg_right hPsi (sq_nonneg t)
    _ = Real.exp (24 * Real.exp 1) *
        t ^ (-1 - 2 / (Real.log z) ^ 2) := by
      rw [hexp]
      calc
        Real.exp (24 * Real.exp 1) *
              (t * t ^ (-2 / Real.log z ^ 2)) / t ^ 2 =
            Real.exp (24 * Real.exp 1) *
              (t⁻¹ * t ^ (-2 / Real.log z ^ 2)) := by
                field_simp [htPos.ne']
        _ = _ := by
          rw [← Real.rpow_neg_one, ← Real.rpow_add htPos]
          congr 2
          ring

private lemma integral_rankinLogSqMajorant
    {n m : ℕ} {z : ℝ} (hn : 1 ≤ n) (hnm : n ≤ m)
    (hlog : 2 ≤ Real.log z) :
    (∫ t in Set.Ioc (n : ℝ) m,
        Real.exp (24 * Real.exp 1) *
          t ^ (-1 - 2 / (Real.log z) ^ 2)) =
      Real.exp (24 * Real.exp 1) *
        (((m : ℝ) ^ (-2 / (Real.log z) ^ 2) -
          (n : ℝ) ^ (-2 / (Real.log z) ^ 2)) /
            (-2 / (Real.log z) ^ 2)) := by
  have hnPos : (0 : ℝ) < n := by exact_mod_cast hn
  have hnmReal : (n : ℝ) ≤ m := by exact_mod_cast hnm
  have hlogPos : 0 < Real.log z := lt_of_lt_of_le (by norm_num) hlog
  have hexponent :
      -1 - 2 / (Real.log z) ^ 2 + 1 =
        -2 / (Real.log z) ^ 2 := by ring
  rw [← intervalIntegral.integral_of_le hnmReal,
    intervalIntegral.integral_const_mul,
    integral_rpow, hexponent]
  · refine Or.inr ⟨?_, Set.notMem_uIcc_of_lt hnPos
      (hnPos.trans_le hnmReal)⟩
    have : 0 < 2 / (Real.log z) ^ 2 := by positivity
    linarith

/-- The finite Stieltjes correction after `(4.4)` is bounded by integrating
the logarithmic-square Rankin majorant, with both endpoints present. -/
theorem integral_selbergRealPsi_div_sq_le_rankin_logSq
    {n m : ℕ} {z : ℝ}
    (hn : 1 ≤ n) (hnm : n ≤ m) (hz : 1 ≤ z)
    (hlog : 2 ≤ Real.log z) :
    (∫ t in Set.Ioc (n : ℝ) m, selbergRealPsi t z / t ^ 2) ≤
      Real.exp (24 * Real.exp 1) *
        (((m : ℝ) ^ (-2 / (Real.log z) ^ 2) -
          (n : ℝ) ^ (-2 / (Real.log z) ^ 2)) /
            (-2 / (Real.log z) ^ 2)) := by
  have hnPos : (0 : ℝ) < n := by exact_mod_cast hn
  have hnmReal : (n : ℝ) ≤ m := by exact_mod_cast hnm
  have hnotzero :
      (0 : ℝ) ∉ Set.uIcc (n : ℝ) m :=
    Set.notMem_uIcc_of_lt hnPos (hnPos.trans_le hnmReal)
  have hRpowInt : IntervalIntegrable
      (fun t : ℝ => t ^ (-1 - 2 / (Real.log z) ^ 2))
      MeasureTheory.volume (n : ℝ) m :=
    intervalIntegral.intervalIntegrable_rpow
      (r := -1 - 2 / (Real.log z) ^ 2) (Or.inr hnotzero)
  have hRhsInt : MeasureTheory.IntegrableOn
      (fun t : ℝ => Real.exp (24 * Real.exp 1) *
        t ^ (-1 - 2 / (Real.log z) ^ 2))
      (Set.Ioc (n : ℝ) m) :=
    hRpowInt.const_mul _ |>.1
  have hPsiMeas : Measurable (fun t : ℝ => selbergRealPsi t z) := by
    change Measurable (fun t : ℝ => selbergPsi ⌊t⌋₊ z)
    exact (measurable_of_countable (fun q : ℕ => selbergPsi q z)).comp
      Nat.measurable_floor
  have hLhsMeas : Measurable
      (fun t : ℝ => selbergRealPsi t z / t ^ 2) :=
    hPsiMeas.div (measurable_id.pow_const 2)
  have hLhsInt : MeasureTheory.IntegrableOn
      (fun t : ℝ => selbergRealPsi t z / t ^ 2)
      (Set.Ioc (n : ℝ) m) := by
    refine hRhsInt.mono_nonneg hLhsMeas.aestronglyMeasurable.restrict
      (Filter.Eventually.of_forall fun t => by
        apply div_nonneg
        · unfold selbergRealPsi
          positivity
        · positivity) ?_
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioc] with t ht
    exact selbergRealPsi_div_sq_le_rankin_logSq (by
      exact (show (n : ℝ) < t from ht.1).le.trans'
        (by exact_mod_cast hn)) hz hlog
  calc
    (∫ t in Set.Ioc (n : ℝ) m, selbergRealPsi t z / t ^ 2) ≤
        ∫ t in Set.Ioc (n : ℝ) m,
          Real.exp (24 * Real.exp 1) *
            t ^ (-1 - 2 / (Real.log z) ^ 2) :=
      MeasureTheory.setIntegral_mono_on hLhsInt hRhsInt measurableSet_Ioc
        (fun t ht => selbergRealPsi_div_sq_le_rankin_logSq
          ((show (n : ℝ) < t from ht.1).le.trans'
            (by exact_mod_cast hn))
          hz hlog)
    _ = _ := integral_rankinLogSqMajorant hn hnm hlog

private lemma integral_selbergRealPsi_div_sq_le_rankin_logSq_coarse
    {n m : ℕ} {z : ℝ}
    (hn : 1 ≤ n) (hnm : n ≤ m) (hz : 1 ≤ z)
    (hlog : 2 ≤ Real.log z) :
    (∫ t in Set.Ioc (n : ℝ) m, selbergRealPsi t z / t ^ 2) ≤
      Real.exp (24 * Real.exp 1) * (Real.log z) ^ 2 *
        (n : ℝ) ^ (-2 / (Real.log z) ^ 2) := by
  have hlogPos : 0 < Real.log z := lt_of_lt_of_le (by norm_num) hlog
  have hsPos : 0 < (Real.log z) ^ 2 := sq_pos_of_pos hlogPos
  let x : ℝ := (n : ℝ) ^ (-2 / (Real.log z) ^ 2)
  let y : ℝ := (m : ℝ) ^ (-2 / (Real.log z) ^ 2)
  have hx : 0 ≤ x := by
    dsimp [x]
    positivity
  have hy : 0 ≤ y := by
    dsimp [y]
    positivity
  have hratio :
      (y - x) / (-2 / (Real.log z) ^ 2) ≤
        (Real.log z) ^ 2 * x := by
    have hdiv :
        (y - x) / (-2 / (Real.log z) ^ 2) =
          ((Real.log z) ^ 2 / 2) * (x - y) := by
      field_simp [hlogPos.ne']
      ring
    rw [hdiv]
    calc
      (Real.log z) ^ 2 / 2 * (x - y) ≤
          (Real.log z) ^ 2 / 2 * x :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ ≤ (Real.log z) ^ 2 * x :=
        mul_le_mul_of_nonneg_right (by linarith) hx
  calc
    (∫ t in Set.Ioc (n : ℝ) m, selbergRealPsi t z / t ^ 2) ≤
        Real.exp (24 * Real.exp 1) *
          ((y - x) / (-2 / (Real.log z) ^ 2)) := by
      simpa only [x, y] using
        integral_selbergRealPsi_div_sq_le_rankin_logSq hn hnm hz hlog
    _ ≤ Real.exp (24 * Real.exp 1) *
        ((Real.log z) ^ 2 * x) :=
      mul_le_mul_of_nonneg_left hratio (Real.exp_pos _).le
    _ = _ := by ring

private lemma selbergPsi_div_le_rankin_logSq
    {n m : ℕ} {z : ℝ}
    (hn : 1 ≤ n) (hnm : n ≤ m) (hz : 1 ≤ z)
    (hlog : 2 ≤ Real.log z) :
    selbergPsi m z / (m : ℝ) ≤
      Real.exp (24 * Real.exp 1) *
        (n : ℝ) ^ (-2 / (Real.log z) ^ 2) := by
  have hnPos : (0 : ℝ) < n := by exact_mod_cast hn
  have hmPos : (0 : ℝ) < m := hnPos.trans_le (by exact_mod_cast hnm)
  have hnmReal : (n : ℝ) ≤ m := by exact_mod_cast hnm
  have hPsi :=
    selbergRealPsi_le_rankin_logSq
      (xi := (m : ℝ)) (by exact_mod_cast hn.trans hnm) hz hlog
  rw [selbergRealPsi_eq_floor, Nat.floor_natCast] at hPsi
  have hexp :
      Real.exp (-2 * Real.log (m : ℝ) / (Real.log z) ^ 2) =
        (m : ℝ) ^ (-2 / (Real.log z) ^ 2) := by
    rw [Real.rpow_def_of_pos hmPos]
    congr 1
    ring
  calc
    selbergPsi m z / (m : ℝ) ≤
        (Real.exp (24 * Real.exp 1) *
          ((m : ℝ) * Real.exp
            (-2 * Real.log (m : ℝ) / (Real.log z) ^ 2))) /
              (m : ℝ) :=
      div_le_div_of_nonneg_right hPsi (Nat.cast_nonneg m)
    _ = Real.exp (24 * Real.exp 1) *
        (m : ℝ) ^ (-2 / (Real.log z) ^ 2) := by
      rw [hexp]
      field_simp [hmPos.ne']
    _ ≤ Real.exp (24 * Real.exp 1) *
        (n : ℝ) ^ (-2 / (Real.log z) ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      exact Real.rpow_le_rpow_of_nonpos hnPos hnmReal
        (div_nonpos_of_nonpos_of_nonneg (by norm_num) (sq_nonneg _))

/-- The finite quantitative form of the partial-summation tail. The upper
endpoint from the exact identity is estimated rather than discarded. -/
theorem selbergSmoothReciprocalSum_sub_le_rankin_logSq
    {n m : ℕ} {z : ℝ}
    (hn : 1 ≤ n) (hnm : n ≤ m) (hz : 1 ≤ z)
    (hlog : 2 ≤ Real.log z) :
    selbergSmoothReciprocalSum m z -
        selbergSmoothReciprocalSum n z ≤
      2 * Real.exp (24 * Real.exp 1) * (Real.log z) ^ 2 *
        (n : ℝ) ^ (-2 / (Real.log z) ^ 2) := by
  have hzStrict : 1 < z := by
    exact (Real.log_pos_iff (zero_le_one.trans hz)).mp
      (lt_of_lt_of_le (by norm_num) hlog)
  rw [selbergSmoothReciprocalSum_sub_eq_psi_div_add_integral
    hzStrict hn hnm]
  have hnNonneg :
      0 ≤ selbergPsi n z / (n : ℝ) := by
    apply div_nonneg
    · unfold selbergPsi
      positivity
    · positivity
  have hEndpoint := selbergPsi_div_le_rankin_logSq hn hnm hz hlog
  have hIntegral :=
    integral_selbergRealPsi_div_sq_le_rankin_logSq_coarse
      hn hnm hz hlog
  have hsq : 1 ≤ (Real.log z) ^ 2 := by
    nlinarith [sq_nonneg (Real.log z)]
  let x : ℝ := (n : ℝ) ^ (-2 / (Real.log z) ^ 2)
  have hx : 0 ≤ x := by
    dsimp [x]
    positivity
  calc
    selbergPsi m z / (m : ℝ) - selbergPsi n z / (n : ℝ) +
          ∫ t in Set.Ioc (n : ℝ) m, selbergRealPsi t z / t ^ 2 ≤
        selbergPsi m z / (m : ℝ) +
          ∫ t in Set.Ioc (n : ℝ) m,
            selbergRealPsi t z / t ^ 2 := by linarith
    _ ≤ Real.exp (24 * Real.exp 1) * x +
          Real.exp (24 * Real.exp 1) * (Real.log z) ^ 2 * x := by
      simpa only [x] using add_le_add hEndpoint hIntegral
    _ = Real.exp (24 * Real.exp 1) *
          (1 + (Real.log z) ^ 2) * x := by ring
    _ ≤ Real.exp (24 * Real.exp 1) *
          (2 * (Real.log z) ^ 2) * x := by
      apply mul_le_mul_of_nonneg_right _ hx
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      linarith
    _ = _ := by ring

/-- The uniform reciprocal smooth-number tail deduced after `(4.4)`. This is
the source-scale `O(log(z)^2 exp(-2 log(n)/log(z)^2))` estimate, obtained from
the finite identity before passing to the Euler-product limit. -/
theorem sieveProduct_inv_sub_selbergSmoothReciprocalSum_le_rankin_logSq
    {n : ℕ} {z : ℝ}
    (hn : 1 ≤ n) (hz : 1 ≤ z) (hlog : 2 ≤ Real.log z) :
    0 ≤ (sieveProduct 1 z)⁻¹ - selbergSmoothReciprocalSum n z ∧
      (sieveProduct 1 z)⁻¹ - selbergSmoothReciprocalSum n z ≤
        2 * Real.exp (24 * Real.exp 1) * (Real.log z) ^ 2 *
          Real.exp (-2 * Real.log n / (Real.log z) ^ 2) := by
  have hzStrict : 1 < z := by
    exact (Real.log_pos_iff (zero_le_one.trans hz)).mp
      (lt_of_lt_of_le (by norm_num) hlog)
  have hTend := tendsto_selbergSmoothReciprocalSum z hzStrict
  have hMono : ∀ m ≥ n,
      selbergSmoothReciprocalSum n z ≤
        selbergSmoothReciprocalSum m z := by
    intro m hnm
    unfold selbergSmoothReciprocalSum
    apply Finset.sum_le_sum_of_subset_of_nonneg
      (selbergPsiCarrier_mono hnm le_rfl)
    intro q _hq _hqNot
    positivity
  have hLower :
      selbergSmoothReciprocalSum n z ≤ (sieveProduct 1 z)⁻¹ := by
    apply ge_of_tendsto hTend
    filter_upwards [Filter.eventually_ge_atTop n] with m hm
    exact hMono m hm
  constructor
  · exact sub_nonneg.mpr hLower
  · have hUpperRpow :
        (sieveProduct 1 z)⁻¹ - selbergSmoothReciprocalSum n z ≤
          2 * Real.exp (24 * Real.exp 1) * (Real.log z) ^ 2 *
            (n : ℝ) ^ (-2 / (Real.log z) ^ 2) := by
      apply le_of_tendsto (hTend.sub_const
        (selbergSmoothReciprocalSum n z))
      filter_upwards [Filter.eventually_ge_atTop n] with m hm
      exact selbergSmoothReciprocalSum_sub_le_rankin_logSq
        hn hm hz hlog
    rw [Real.rpow_def_of_pos
      (by exact_mod_cast hn : (0 : ℝ) < n)] at hUpperRpow
    convert hUpperRpow using 1 <;> ring

/-- Before weakening the elementary Rankin estimate to logarithmic-square
decay, the same finite Abel identity retains the sharper decay
`exp (-log n / log z)`.  This is the estimate used in the genuinely
large-`y` branch of the auxiliary logarithmic-square bound; retaining it prevents the
`log z` factor from surviving after division by the harmonic lower bound. -/
theorem sieveProduct_inv_sub_selbergSmoothReciprocalSum_le_rankin
    {n : ℕ} {z : ℝ}
    (hn : 1 ≤ n) (hz : 1 ≤ z) (hlog : 2 ≤ Real.log z) :
    0 ≤ (sieveProduct 1 z)⁻¹ - selbergSmoothReciprocalSum n z ∧
      (sieveProduct 1 z)⁻¹ - selbergSmoothReciprocalSum n z ≤
        2 * Real.log z *
          Real.exp (4 * (Real.exp 1 * (1 + Real.log z))) *
          Real.exp (-Real.log n / Real.log z) := by
  have hzStrict : 1 < z := by
    exact (Real.log_pos_iff (zero_le_one.trans hz)).mp
      (lt_of_lt_of_le (by norm_num) hlog)
  have hlogPos : 0 < Real.log z :=
    lt_of_lt_of_le (by norm_num) hlog
  have hlogNe : Real.log z ≠ 0 := ne_of_gt hlogPos
  have hTend := tendsto_selbergSmoothReciprocalSum z hzStrict
  have hMono : ∀ m ≥ n,
      selbergSmoothReciprocalSum n z ≤
        selbergSmoothReciprocalSum m z := by
    intro m hnm
    unfold selbergSmoothReciprocalSum
    apply Finset.sum_le_sum_of_subset_of_nonneg
      (selbergPsiCarrier_mono hnm le_rfl)
    intro q _hq _hqNot
    positivity
  have hLower :
      selbergSmoothReciprocalSum n z ≤ (sieveProduct 1 z)⁻¹ := by
    apply ge_of_tendsto hTend
    filter_upwards [Filter.eventually_ge_atTop n] with m hm
    exact hMono m hm
  constructor
  · exact sub_nonneg.mpr hLower
  · have hFinite : ∀ m ≥ n,
        selbergSmoothReciprocalSum m z -
            selbergSmoothReciprocalSum n z ≤
          2 * Real.log z *
            Real.exp (4 * (Real.exp 1 * (1 + Real.log z))) *
            (n : ℝ) ^ (-1 / Real.log z) := by
      intro m hnm
      have hnPos : (0 : ℝ) < n := by exact_mod_cast hn
      have hmPos : (0 : ℝ) < m :=
        hnPos.trans_le (by exact_mod_cast hnm)
      have hnmReal : (n : ℝ) ≤ m := by exact_mod_cast hnm
      have hPsiMeas :
          Measurable (fun t : ℝ => selbergRealPsi t z) := by
        change Measurable (fun t : ℝ => selbergPsi ⌊t⌋₊ z)
        exact
          (measurable_of_countable (fun q : ℕ => selbergPsi q z)).comp
            Nat.measurable_floor
      have hMajorant : ∀ t : ℝ, 1 ≤ t →
          selbergRealPsi t z / t ^ 2 ≤
            Real.exp (4 * (Real.exp 1 * (1 + Real.log z))) *
              t ^ (-1 - 1 / Real.log z) := by
        intro t ht
        have htPos : 0 < t := zero_lt_one.trans_le ht
        have hPsi :=
          selbergRealPsi_le_vinogradovRankin htPos.le hz hlog
        calc
          selbergRealPsi t z / t ^ 2 ≤
              (t ^ (1 - 1 / Real.log z) *
                Real.exp (4 * (z ^ (1 / Real.log z) *
                  (1 + Real.log z)))) / t ^ 2 :=
            div_le_div_of_nonneg_right hPsi (sq_nonneg t)
          _ = Real.exp (4 * (Real.exp 1 * (1 + Real.log z))) *
                t ^ (-1 - 1 / Real.log z) := by
            have hzPos : 0 < z := zero_lt_one.trans hzStrict
            rw [Real.rpow_def_of_pos hzPos]
            have hzexp : Real.log z * (1 / Real.log z) = 1 := by
              field_simp
            rw [hzexp]
            field_simp [htPos.ne']
            calc
              t ^ ((Real.log z - 1) / Real.log z) =
                  t ^ (2 + ((-Real.log z - 1) / Real.log z)) := by
                congr 1
                field_simp [hlogNe]
                ring
              _ = t ^ 2 *
                  t ^ ((-Real.log z - 1) / Real.log z) :=
                by simpa using
                  (Real.rpow_add htPos 2
                    ((-Real.log z - 1) / Real.log z))
      have hnotzero :
          (0 : ℝ) ∉ Set.uIcc (n : ℝ) m :=
        Set.notMem_uIcc_of_lt hnPos (hnPos.trans_le hnmReal)
      have hRpowInt : IntervalIntegrable
          (fun t : ℝ => t ^ (-1 - 1 / Real.log z))
          MeasureTheory.volume (n : ℝ) m :=
        intervalIntegral.intervalIntegrable_rpow
          (r := -1 - 1 / Real.log z) (Or.inr hnotzero)
      have hRhsInt : MeasureTheory.IntegrableOn
          (fun t : ℝ =>
            Real.exp (4 * (Real.exp 1 * (1 + Real.log z))) *
              t ^ (-1 - 1 / Real.log z))
          (Set.Ioc (n : ℝ) m) :=
        hRpowInt.const_mul _ |>.1
      have hLhsMeas : Measurable
          (fun t : ℝ => selbergRealPsi t z / t ^ 2) :=
        hPsiMeas.div (measurable_id.pow_const 2)
      have hLhsInt : MeasureTheory.IntegrableOn
          (fun t : ℝ => selbergRealPsi t z / t ^ 2)
          (Set.Ioc (n : ℝ) m) := by
        refine hRhsInt.mono_nonneg
          hLhsMeas.aestronglyMeasurable.restrict
          (Filter.Eventually.of_forall fun t => by
            apply div_nonneg
            · unfold selbergRealPsi
              positivity
            · positivity) ?_
        filter_upwards
          [MeasureTheory.self_mem_ae_restrict measurableSet_Ioc] with t ht
        exact hMajorant t
          ((show (n : ℝ) < t from ht.1).le.trans'
            (by exact_mod_cast hn))
      have hIntegral :
          (∫ t in Set.Ioc (n : ℝ) m,
              selbergRealPsi t z / t ^ 2) ≤
            Real.exp (4 * (Real.exp 1 * (1 + Real.log z))) *
              Real.log z * (n : ℝ) ^ (-1 / Real.log z) := by
        have hexponent :
            -1 - 1 / Real.log z + 1 = -1 / Real.log z := by ring
        calc
          (∫ t in Set.Ioc (n : ℝ) m,
              selbergRealPsi t z / t ^ 2) ≤
              ∫ t in Set.Ioc (n : ℝ) m,
                Real.exp (4 * (Real.exp 1 * (1 + Real.log z))) *
                  t ^ (-1 - 1 / Real.log z) :=
            MeasureTheory.setIntegral_mono_on hLhsInt hRhsInt
              measurableSet_Ioc (fun t ht => hMajorant t
                ((show (n : ℝ) < t from ht.1).le.trans'
                  (by exact_mod_cast hn)))
          _ = Real.exp (4 * (Real.exp 1 * (1 + Real.log z))) *
                (((m : ℝ) ^ (-1 / Real.log z) -
                  (n : ℝ) ^ (-1 / Real.log z)) /
                    (-1 / Real.log z)) := by
            rw [← intervalIntegral.integral_of_le hnmReal,
              intervalIntegral.integral_const_mul, integral_rpow,
              hexponent]
            · refine Or.inr ⟨?_, hnotzero⟩
              intro heq
              field_simp [hlogNe] at heq
              linarith
          _ ≤ Real.exp (4 * (Real.exp 1 * (1 + Real.log z))) *
                Real.log z * (n : ℝ) ^ (-1 / Real.log z) := by
            have hmRpow : 0 ≤
                (m : ℝ) ^ (-1 / Real.log z) := by positivity
            have hnRpow : 0 ≤
                (n : ℝ) ^ (-1 / Real.log z) := by positivity
            have hquotEq :
                ((m : ℝ) ^ (-1 / Real.log z) -
                    (n : ℝ) ^ (-1 / Real.log z)) /
                    (-1 / Real.log z) =
                  Real.log z *
                    ((n : ℝ) ^ (-1 / Real.log z) -
                      (m : ℝ) ^ (-1 / Real.log z)) := by
              field_simp [hlogNe]
              ring
            have hquot :
                ((m : ℝ) ^ (-1 / Real.log z) -
                    (n : ℝ) ^ (-1 / Real.log z)) /
                    (-1 / Real.log z) ≤
                  Real.log z * (n : ℝ) ^ (-1 / Real.log z) := by
              rw [hquotEq]
              nlinarith
            nlinarith [Real.exp_pos
              (4 * (Real.exp 1 * (1 + Real.log z)))]
      have hEndpoint :
          selbergPsi m z / (m : ℝ) ≤
            Real.exp (4 * (Real.exp 1 * (1 + Real.log z))) *
              (n : ℝ) ^ (-1 / Real.log z) := by
        have hPsi :=
          selbergRealPsi_le_vinogradovRankin
            (xi := (m : ℝ)) hmPos.le hz hlog
        rw [selbergRealPsi_eq_floor, Nat.floor_natCast] at hPsi
        have hRewrite :
            (m : ℝ) ^ (1 - 1 / Real.log z) *
                Real.exp (4 * (z ^ (1 / Real.log z) *
                  (1 + Real.log z))) / (m : ℝ) =
              Real.exp (4 * (Real.exp 1 * (1 + Real.log z))) *
                (m : ℝ) ^ (-1 / Real.log z) := by
          have hzPos : 0 < z := zero_lt_one.trans hzStrict
          rw [Real.rpow_def_of_pos hzPos]
          have hzexp : Real.log z * (1 / Real.log z) = 1 := by
            field_simp
          rw [hzexp]
          field_simp [hmPos.ne']
          calc
            (m : ℝ) ^ ((Real.log z - 1) / Real.log z) =
                (m : ℝ) ^ (1 + (-(1 / Real.log z))) := by
              congr 1
              field_simp [hlogNe]
              ring
            _ = (m : ℝ) ^ (1 : ℝ) *
                (m : ℝ) ^ (-(1 / Real.log z)) :=
              Real.rpow_add hmPos (1 : ℝ) (-(1 / Real.log z))
            _ = (m : ℝ) *
                (m : ℝ) ^ (-(1 / Real.log z)) := by
              rw [Real.rpow_one]
        calc
          selbergPsi m z / (m : ℝ) ≤
              (m : ℝ) ^ (1 - 1 / Real.log z) *
                  Real.exp (4 * (z ^ (1 / Real.log z) *
                    (1 + Real.log z))) / (m : ℝ) :=
            div_le_div_of_nonneg_right hPsi (Nat.cast_nonneg m)
          _ = Real.exp (4 * (Real.exp 1 * (1 + Real.log z))) *
                (m : ℝ) ^ (-1 / Real.log z) := hRewrite
          _ ≤ Real.exp (4 * (Real.exp 1 * (1 + Real.log z))) *
                (n : ℝ) ^ (-1 / Real.log z) := by
            apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
            exact Real.rpow_le_rpow_of_nonpos hnPos hnmReal
              (div_nonpos_of_nonpos_of_nonneg (by norm_num) hlogPos.le)
      rw [selbergSmoothReciprocalSum_sub_eq_psi_div_add_integral
        hzStrict hn hnm]
      have hnEndpoint :
          0 ≤ selbergPsi n z / (n : ℝ) := by
        exact div_nonneg (by unfold selbergPsi; positivity) hnPos.le
      have hlogTwo : 1 ≤ Real.log z := by linarith
      have hRpowNonneg :
          0 ≤ (n : ℝ) ^ (-1 / Real.log z) := by positivity
      calc
        selbergPsi m z / (m : ℝ) - selbergPsi n z / (n : ℝ) +
              ∫ t in Set.Ioc (n : ℝ) m,
                selbergRealPsi t z / t ^ 2 ≤
            selbergPsi m z / (m : ℝ) +
              ∫ t in Set.Ioc (n : ℝ) m,
                selbergRealPsi t z / t ^ 2 := by linarith
        _ ≤ Real.exp (4 * (Real.exp 1 * (1 + Real.log z))) *
              (n : ℝ) ^ (-1 / Real.log z) +
            Real.exp (4 * (Real.exp 1 * (1 + Real.log z))) *
              Real.log z * (n : ℝ) ^ (-1 / Real.log z) :=
          add_le_add hEndpoint hIntegral
        _ ≤ 2 * Real.log z *
              Real.exp (4 * (Real.exp 1 * (1 + Real.log z))) *
              (n : ℝ) ^ (-1 / Real.log z) := by
          calc
            Real.exp (4 * (Real.exp 1 * (1 + Real.log z))) *
                  (n : ℝ) ^ (-1 / Real.log z) +
                Real.exp (4 * (Real.exp 1 * (1 + Real.log z))) *
                  Real.log z * (n : ℝ) ^ (-1 / Real.log z) =
                (1 + Real.log z) *
                  (Real.exp (4 * (Real.exp 1 * (1 + Real.log z))) *
                    (n : ℝ) ^ (-1 / Real.log z)) := by ring
            _ ≤ (2 * Real.log z) *
                  (Real.exp (4 * (Real.exp 1 * (1 + Real.log z))) *
                    (n : ℝ) ^ (-1 / Real.log z)) :=
              mul_le_mul_of_nonneg_right (by linarith)
                (mul_nonneg (Real.exp_pos _).le hRpowNonneg)
            _ = _ := by ring
    have hUpperRpow :
        (sieveProduct 1 z)⁻¹ - selbergSmoothReciprocalSum n z ≤
          2 * Real.log z *
            Real.exp (4 * (Real.exp 1 * (1 + Real.log z))) *
            (n : ℝ) ^ (-1 / Real.log z) := by
      apply le_of_tendsto (hTend.sub_const
        (selbergSmoothReciprocalSum n z))
      filter_upwards [Filter.eventually_ge_atTop n] with m hm
      exact hFinite m hm
    rw [Real.rpow_def_of_pos
      (by exact_mod_cast hn : (0 : ℝ) < n)] at hUpperRpow
    convert hUpperRpow using 1 <;> ring

/-- Below the sifting cutoff every positive integer is smooth, so the source's
real `Psi` carrier is the full interval through `floor xi`. -/
theorem selbergRealPsiCarrier_eq_Icc
    {xi z : ℝ} (hxi : 0 ≤ xi) (hxiZ : xi < z) :
    selbergRealPsiCarrier xi z = Finset.Icc 1 ⌊xi⌋₊ := by
  ext n
  rw [mem_selbergRealPsiCarrier hxi]
  simp only [Finset.mem_Icc]
  constructor
  · rintro ⟨hn1, hnxi, -, -⟩
    exact ⟨hn1, Nat.le_floor hnxi⟩
  · rintro ⟨hn1, hnFloor⟩
    have hnxi : (n : ℝ) ≤ xi :=
      (Nat.cast_le.mpr hnFloor).trans (Nat.floor_le hxi)
    refine ⟨hn1, hnxi, ?_, ?_⟩
    · intro hn
      subst n
      simpa using hnxi.trans_lt hxiZ
    · intro p hp
      have hpn : p ≤ n := Nat.le_of_mem_primeFactors hp
      exact (Nat.cast_le.mpr hpn).trans_lt (hnxi.trans_lt hxiZ)

/-- In the large-cutoff regime used for `(3.9)`, the source's smooth-number
count is exactly `floor xi`. -/
theorem selbergRealPsi_eq_floor_of_lt
    {xi z : ℝ} (hxi : 0 ≤ xi) (hxiZ : xi < z) :
    selbergRealPsi xi z = ⌊xi⌋₊ := by
  rw [selbergRealPsi, selbergRealPsiCarrier_eq_Icc hxi hxiZ]
  simp

/-- The smooth-number error in Theorem 2 is bounded by the square of the
chosen real level whenever that level lies below `z`. -/
theorem selbergRealPsi_sq_le
    {xi z : ℝ} (hxi : 0 ≤ xi) (hxiZ : xi < z) :
    selbergRealPsi xi z ^ 2 ≤ xi ^ 2 := by
  rw [selbergRealPsi_eq_floor_of_lt hxi hxiZ]
  exact pow_le_pow_left₀ (Nat.cast_nonneg ⌊xi⌋₊) (Nat.floor_le hxi) 2

/-- When `xi < z`, the reciprocal smooth-number sum in Theorem 2 is the
ordinary harmonic sum through `floor xi`. -/
theorem selbergRealSmoothReciprocalSum_eq_harmonic
    {xi z : ℝ} (hxi : 0 ≤ xi) (hxiZ : xi < z) :
    selbergRealSmoothReciprocalSum xi z = (harmonic ⌊xi⌋₊ : ℝ) := by
  rw [selbergRealSmoothReciprocalSum, selbergSmoothReciprocalSum]
  have hcarrier :
      selbergPsiCarrier ⌊xi⌋₊ z = Finset.Icc 1 ⌊xi⌋₊ := by
    simpa [selbergRealPsiCarrier] using
      selbergRealPsiCarrier_eq_Icc hxi hxiZ
  rw [hcarrier]
  rw [harmonic_eq_sum_Icc]
  push_cast
  simp [one_div]

/-- The harmonic integral bound gives the explicit denominator input used in
the source derivation of `(3.9)`. -/
theorem log_le_selbergRealSmoothReciprocalSum
    {xi z : ℝ} (hxi : 0 ≤ xi) (hxiZ : xi < z) :
    Real.log xi ≤ selbergRealSmoothReciprocalSum xi z := by
  rw [selbergRealSmoothReciprocalSum_eq_harmonic hxi hxiZ]
  exact log_le_harmonic_floor xi hxi

/-- The real smooth reciprocal sum is monotone in its level. -/
theorem selbergRealSmoothReciprocalSum_mono
    {xi eta z : ℝ} (hxi : xi ≤ eta) :
    selbergRealSmoothReciprocalSum xi z ≤
      selbergRealSmoothReciprocalSum eta z := by
  unfold selbergRealSmoothReciprocalSum selbergSmoothReciprocalSum
  apply Finset.sum_le_sum_of_subset_of_nonneg
    (selbergPsiCarrier_mono (Nat.floor_mono hxi) le_rfl)
  intro n hn hnNot
  positivity

/-- The level chosen on printed p. 225:
`xi^2 = y / log z`. -/
noncomputable def fourOneCutoff (y z : ℝ) : ℝ :=
  Real.sqrt (y / Real.log z)

/-- The defining square identity for the level on printed p. 225. -/
theorem fourOneCutoff_sq {y z : ℝ} (hy : 0 ≤ y)
    (hlog : 0 < Real.log z) :
    fourOneCutoff y z ^ 2 = y / Real.log z := by
  unfold fourOneCutoff
  rw [Real.sq_sqrt]
  positivity

/-- Logarithmic form of the defining level identity on printed p. 225. -/
theorem log_fourOneCutoff {y z : ℝ} (hy : 0 < y)
    (hlog : 0 < Real.log z) :
    Real.log (fourOneCutoff y z) =
      (Real.log y - Real.log (Real.log z)) / 2 := by
  unfold fourOneCutoff
  rw [Real.log_sqrt, Real.log_div hy.ne' hlog.ne']
  positivity

/-- Passing from a real Selberg level at least two to its natural floor costs
at most `log 2`, the floor loss used in the auxiliary large-ratio bound. -/
theorem log_sub_log_two_le_log_floor
    {xi : ℝ} (hxi : 2 ≤ xi) :
    Real.log xi - Real.log 2 ≤ Real.log (⌊xi⌋₊ : ℕ) := by
  have hxi0 : 0 ≤ xi := zero_le_two.trans hxi
  have hfloorHalf : xi / 2 ≤ (⌊xi⌋₊ : ℝ) := by
    have hFloor := Nat.lt_floor_add_one xi
    linarith
  have hhalfPos : 0 < xi / 2 := by positivity
  have hfloorPos : (0 : ℝ) < ⌊xi⌋₊ :=
    hhalfPos.trans_le hfloorHalf
  calc
    Real.log xi - Real.log 2 = Real.log (xi / 2) := by
      rw [Real.log_div (by positivity) (by norm_num)]
    _ ≤ Real.log (⌊xi⌋₊ : ℕ) :=
      Real.strictMonoOn_log.monotoneOn hhalfPos hfloorPos hfloorHalf

/-- For positive `y`, its logarithm is at most its square root.  This
elementary estimate verifies the source's displayed
`z^(1/4) ≤ fourOneCutoff y z`. -/
private theorem log_le_sqrt_of_pos {y : ℝ} (hy : 0 < y) :
    Real.log y ≤ Real.sqrt y := by
  have hs : 0 < Real.sqrt y := Real.sqrt_pos.2 hy
  have hsDiv : 0 < Real.sqrt y / 2 := by positivity
  have hLogDiv := Real.log_le_sub_one_of_pos hsDiv
  have hLogTwo :=
    Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  norm_num at hLogTwo
  have hLogMul :
      Real.log (Real.sqrt y) =
        Real.log 2 + Real.log (Real.sqrt y / 2) := by
    rw [← Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hsDiv.ne']
    congr 1
    ring
  have hHalf : 2 * Real.log (Real.sqrt y) ≤ Real.sqrt y := by
    rw [hLogMul]
    linarith
  rw [Real.log_sqrt hy.le] at hHalf
  linarith

/-- The source's auxiliary lower range
`n ≤ z^(1/4) ≤ fourOneCutoff y z`. -/
theorem rpow_quarter_le_fourOneCutoff
    {y z : ℝ} (hy : 0 < y) (hz : 0 < z)
    (hlog : 2 ≤ Real.log z) (hzy : Real.log z ≤ Real.log y) :
    z ^ (1 / 4 : ℝ) ≤ fourOneCutoff y z := by
  let Z := Real.log z
  let xi := fourOneCutoff y z
  let w := z ^ (1 / 4 : ℝ)
  have hZ : 0 < Z := by
    dsimp [Z]
    linarith
  have hzY : z ≤ y := by
    rw [← Real.exp_log hz, ← Real.exp_log hy]
    exact Real.exp_le_exp.mpr hzy
  have hZsqrtY : Z ≤ Real.sqrt y := by
    exact hzy.trans (log_le_sqrt_of_pos hy)
  have hSqrtZ : Real.sqrt z ≤ Real.sqrt y :=
    Real.sqrt_le_sqrt hzY
  have hXiSq : xi ^ 2 = y / Z := by
    dsimp [xi, fourOneCutoff]
    rw [Real.sq_sqrt]
    positivity
  have hWSq : w ^ 2 = Real.sqrt z := by
    dsimp [w]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hz.le,
      Real.sqrt_eq_rpow]
    norm_num
  have hProduct : Real.sqrt z * Z ≤ y := by
    calc
      Real.sqrt z * Z ≤ Real.sqrt y * Z :=
        mul_le_mul_of_nonneg_right hSqrtZ hZ.le
      _ ≤ Real.sqrt y * Real.sqrt y :=
        mul_le_mul_of_nonneg_left hZsqrtY (Real.sqrt_nonneg y)
      _ = y := by rw [← pow_two, Real.sq_sqrt hy.le]
  have hWSqLe : w ^ 2 ≤ xi ^ 2 := by
    rw [hWSq, hXiSq]
    exact (le_div_iff₀ hZ).2 hProduct
  have hw0 : 0 ≤ w := by
    unfold w
    positivity
  have hxi0 : 0 ≤ xi := by
    unfold xi fourOneCutoff
    positivity
  exact (sq_le_sq₀ hw0 hxi0).mp hWSqLe

/-- The harmonic lower bound through the literal `z^(1/4)` range on printed
p. 225. -/
theorem quarter_log_le_fourOneSmoothReciprocalSum
    {y z : ℝ} (hy : 0 < y) (hz : 0 < z)
    (hlog : 2 ≤ Real.log z) (hzy : Real.log z ≤ Real.log y) :
    Real.log z / 4 ≤
      selbergRealSmoothReciprocalSum (fourOneCutoff y z) z := by
  let w := z ^ (1 / 4 : ℝ)
  have hzOne : 1 < z := by
    rw [← Real.exp_zero, ← Real.exp_log hz]
    exact Real.exp_lt_exp.mpr (by linarith)
  have hwOne : 1 ≤ w := by
    dsimp [w]
    exact Real.one_le_rpow hzOne.le (by norm_num)
  have hw0 : 0 ≤ w := zero_le_one.trans hwOne
  have hwZ : w < z := by
    dsimp [w]
    simpa only [Real.rpow_one] using
      Real.rpow_lt_rpow_of_exponent_lt hzOne
        (by norm_num : (1 / 4 : ℝ) < 1)
  have hlogw : Real.log w = Real.log z / 4 := by
    dsimp [w]
    rw [Real.log_rpow hz]
    ring
  have hbase :=
    log_le_selbergRealSmoothReciprocalSum hw0 hwZ
  have hmono :=
    selbergRealSmoothReciprocalSum_mono (z := z)
      (rpow_quarter_le_fourOneCutoff hy hz hlog hzy)
  rw [hlogw] at hbase
  exact hbase.trans hmono

/-- The literal source denominator at real level `xi`. -/
noncomputable def RegularSource.realLevelSelbergDenominator
    (source : RegularSource) (z xi : ℝ) : ℝ :=
  source.levelSelbergDenominator z ⌊xi⌋₊

/-- The literal source Selberg weight at real level `xi`. -/
noncomputable def RegularSource.realLevelSelbergWeight
    (source : RegularSource) (z xi : ℝ) : ℕ → ℝ :=
  source.levelSelbergWeight z ⌊xi⌋₊

/-- The real-level denominator is the source's real reciprocal-totient sum. -/
theorem RegularSource.realLevelSelbergDenominator_eq
    (source : RegularSource) {z xi : ℝ} (hxi : 0 ≤ xi) :
    source.realLevelSelbergDenominator z xi =
      selbergRealReciprocalTotientSum source.k xi z := by
  rw [RegularSource.realLevelSelbergDenominator,
    source.levelSelbergDenominator_eq_reciprocalTotientSum,
    selbergRealReciprocalTotientSum_eq_floor source.k hxi]

/-- At every real level `xi > 1`, the constructed optimizer is exactly the
paper's printed coefficient with the real quotient cutoff `xi / d`. -/
theorem RegularSource.realLevelSelbergWeight_eq_printed
    (source : RegularSource) (z : ℝ) {xi : ℝ} {d : ℕ}
    (hxi : 1 < xi)
    (hd : d ∣ (siftingPrimes source.k z).prod id)
    (hdxi : (d : ℝ) ≤ xi) :
    source.realLevelSelbergWeight z xi d =
      (μ d : ℝ) * (d : ℝ) / (Nat.totient d : ℝ) *
        (selbergRealReciprocalTotientSum
            (source.k * d) (xi / (d : ℝ)) z /
          selbergRealReciprocalTotientSum source.k xi z) := by
  have hxi0 : 0 ≤ xi :=
    (by norm_num : (0 : ℝ) ≤ 1).trans hxi.le
  have hdFloor : d ≤ ⌊xi⌋₊ := Nat.le_floor hdxi
  rw [RegularSource.realLevelSelbergWeight,
    source.levelSelbergWeight_eq_printed z hd hdFloor,
    selbergRealReciprocalTotientSum_eq_floor source.k hxi0]
  have hxiDiv0 : 0 ≤ xi / (d : ℝ) := div_nonneg hxi0 (Nat.cast_nonneg d)
  rw [selbergRealReciprocalTotientSum_eq_floor (source.k * d) hxiDiv0,
    Nat.floor_div_natCast]

/-- The real-level denominator is positive throughout the source range
`xi > 1`. -/
theorem RegularSource.realLevelSelbergDenominator_pos
    (source : RegularSource) (z : ℝ) {xi : ℝ} (hxi : 1 < xi) :
    0 < source.realLevelSelbergDenominator z xi := by
  apply source.levelSelbergDenominator_pos
  exact (Nat.one_le_floor_iff xi).2 hxi.le

/-- Nonzero real-level weights satisfy the literal support inequalities. -/
theorem RegularSource.realLevelSelbergWeight_support
    (source : RegularSource) (z : ℝ) {xi : ℝ} {d : ℕ}
    (hxi : 0 ≤ xi)
    (hd : source.realLevelSelbergWeight z xi d ≠ 0) :
    d ∣ (siftingPrimes source.k z).prod id ∧ (d : ℝ) ≤ xi := by
  have hs :=
    source.levelSelbergWeight_support z
      (xi := ⌊xi⌋₊) (d := d) hd
  exact
    ⟨hs.1, (Nat.cast_le.mpr hs.2).trans (Nat.floor_le hxi)⟩

/-- The complete `Lambda^2` mass estimate at every real source level. -/
theorem RegularSource.realLevelSelbergLambdaSquared_mass_le_psi_sq
    (source : RegularSource) {z xi : ℝ} (hz : 1 < z) (hxi : 1 < xi) :
    (∑ d ∈ ((siftingPrimes source.k z).prod id).divisors,
      |BoundingSieve.lambdaSquared
        (source.realLevelSelbergWeight z xi) d|) ≤
      selbergRealPsi xi z ^ 2 := by
  exact
    source.levelSelbergLambdaSquared_mass_le_psi_sq hz
      ((Nat.one_le_floor_iff xi).2 hxi.le)

/-- The real-cutoff form of the source-faithful finite Selberg estimate. -/
theorem RegularSource.siftedCount_le_realLevelSelberg_psi
    (source : RegularSource) {z xi : ℝ} (hz : 1 < z) (hxi : 1 < xi) :
    siftedCount source.carrier source.k z ≤
      source.y * (source.realLevelSelbergDenominator z xi)⁻¹ +
        selbergRealPsi xi z ^ 2 := by
  exact
    source.siftedCount_le_levelSelberg_psi hz
      ((Nat.one_le_floor_iff xi).2 hxi.le)

/-- Theorem 2 `(3.5)` for the literal `gamma(p)=1`, `q=1` source.  Lemma 3.1
replaces the Selberg denominator by the normalized reciprocal smooth-number
sum without introducing a generic-density estimate premise. -/
theorem RegularSource.siftedCount_le_theoremTwo
    (source : RegularSource) {z xi : ℝ} (hz : 1 < z) (hxi : 1 < xi) :
    siftedCount source.carrier source.k z ≤
      source.y * sieveProduct source.k z /
          (sieveProduct 1 z * selbergRealSmoothReciprocalSum xi z) +
        selbergRealPsi xi z ^ 2 := by
  have hxi0 : 0 ≤ xi := le_trans (by norm_num) hxi.le
  have hfloor : 1 ≤ ⌊xi⌋₊ := (Nat.one_le_floor_iff xi).2 hxi.le
  have hone : 1 ∈ selbergPsiCarrier ⌊xi⌋₊ z := by
    simp [selbergPsiCarrier, hfloor, hz]
  have hTge :
      1 ≤ selbergSmoothReciprocalSum ⌊xi⌋₊ z := by
    rw [selbergSmoothReciprocalSum]
    simpa using
      (Finset.single_le_sum
        (s := selbergPsiCarrier ⌊xi⌋₊ z)
        (f := fun n : ℕ => 1 / (n : ℝ))
        (fun n _ => one_div_nonneg.mpr (Nat.cast_nonneg n)) hone)
  have hTpos : 0 < selbergRealSmoothReciprocalSum xi z := by
    rw [selbergRealSmoothReciprocalSum]
    exact zero_lt_one.trans_le hTge
  have hSpos :
      0 < selbergRealReciprocalTotientSum source.k xi z := by
    rw [← source.realLevelSelbergDenominator_eq hxi0]
    exact source.realLevelSelbergDenominator_pos z hxi
  have hnormalized :=
    sieveProduct_one_mul_selbergRealSmoothReciprocalSum_le
      source.k (xi := xi) (z := z) hxi0
  have hdenominatorPos :
      0 < sieveProduct 1 z * selbergRealSmoothReciprocalSum xi z :=
    mul_pos (sieveProduct_pos 1 z) hTpos
  have hinverse :
      (selbergRealReciprocalTotientSum source.k xi z)⁻¹ ≤
        sieveProduct source.k z /
          (sieveProduct 1 z * selbergRealSmoothReciprocalSum xi z) := by
    rw [inv_eq_one_div]
    apply (div_le_div_iff₀ hSpos hdenominatorPos).2
    simpa only [one_mul] using hnormalized
  have hselberg :=
    source.siftedCount_le_realLevelSelberg_psi hz hxi
  rw [source.realLevelSelbergDenominator_eq hxi0] at hselberg
  calc
    siftedCount source.carrier source.k z ≤
        source.y *
            (selbergRealReciprocalTotientSum source.k xi z)⁻¹ +
          selbergRealPsi xi z ^ 2 :=
      hselberg
    _ ≤ source.y *
          (sieveProduct source.k z /
            (sieveProduct 1 z * selbergRealSmoothReciprocalSum xi z)) +
          selbergRealPsi xi z ^ 2 :=
      add_le_add
        (mul_le_mul_of_nonneg_left hinverse
          (le_trans (by norm_num) source.one_lt_y.le))
        le_rfl
    _ = source.y * sieveProduct source.k z /
          (sieveProduct 1 z * selbergRealSmoothReciprocalSum xi z) +
        selbergRealPsi xi z ^ 2 := by
      ring

/-- The large-cutoff form of Theorem 2 before Mertens is substituted: when
`xi < z`, its denominator is bounded below by the literal harmonic integral
and its complete Selberg error is at most `xi^2`. -/
theorem RegularSource.siftedCount_le_theoremTwo_log
    (source : RegularSource) {z xi : ℝ}
    (hz : 1 < z) (hxi : 1 < xi) (hxiZ : xi < z) :
    siftedCount source.carrier source.k z ≤
      source.y * sieveProduct source.k z /
          (sieveProduct 1 z * Real.log xi) + xi ^ 2 := by
  have hlog : 0 < Real.log xi := Real.log_pos hxi
  have hdenominator :
      sieveProduct 1 z * Real.log xi ≤
        sieveProduct 1 z * selbergRealSmoothReciprocalSum xi z :=
    mul_le_mul_of_nonneg_left
      (log_le_selbergRealSmoothReciprocalSum
        (le_trans (by norm_num) hxi.le) hxiZ)
      (sieveProduct_pos 1 z).le
  have hmain :
      source.y * sieveProduct source.k z /
          (sieveProduct 1 z * selbergRealSmoothReciprocalSum xi z) ≤
        source.y * sieveProduct source.k z /
          (sieveProduct 1 z * Real.log xi) := by
    exact
      div_le_div_of_nonneg_left
        (mul_nonneg (le_trans (by norm_num) source.one_lt_y.le)
          (sieveProduct_pos source.k z).le)
        (mul_pos (sieveProduct_pos 1 z) hlog) hdenominator
  exact
    (source.siftedCount_le_theoremTwo hz hxi).trans
      (add_le_add hmain
        (selbergRealPsi_sq_le (le_trans (by norm_num) hxi.le) hxiZ))

/-- Theorem 2 after the exact uniform Mertens inversion.  This is the analytic
form immediately preceding the source's optimization
`xi^2 = y / (1 + log(y)^2)` in `(3.9)`. -/
theorem RegularSource.exists_siftedCount_le_theoremTwo_mertens :
    ∃ B > 0, ∀ (source : RegularSource) {z xi : ℝ},
      1 < z → 1 < xi → xi < z →
      siftedCount source.carrier source.k z ≤
        source.y * sieveProduct source.k z *
            ((Real.exp Real.eulerMascheroniConstant * Real.log z + B) /
              Real.log xi) +
          xi ^ 2 := by
  obtain ⟨B, hB, hInv⟩ :=
    exists_sieveProduct_one_inv_le_exp_mul_log_add
  refine ⟨B, hB, fun source z xi hz hxi hxiZ => ?_⟩
  have hbase :=
    source.siftedCount_le_theoremTwo_log hz hxi hxiZ
  have hsourceFactorNonneg :
      0 ≤ source.y * sieveProduct source.k z :=
    mul_nonneg
      (le_trans (by norm_num) source.one_lt_y.le)
      (sieveProduct_pos source.k z).le
  have hscaled :
      source.y * sieveProduct source.k z * (sieveProduct 1 z)⁻¹ ≤
        source.y * sieveProduct source.k z *
          (Real.exp Real.eulerMascheroniConstant * Real.log z + B) :=
    mul_le_mul_of_nonneg_left (hInv z hz) hsourceFactorNonneg
  have hLogXi : 0 < Real.log xi := Real.log_pos hxi
  have hdivided :
      (source.y * sieveProduct source.k z * (sieveProduct 1 z)⁻¹) /
          Real.log xi ≤
        (source.y * sieveProduct source.k z *
          (Real.exp Real.eulerMascheroniConstant * Real.log z + B)) /
          Real.log xi :=
    (div_le_div_iff_of_pos_right hLogXi).2 hscaled
  calc
    siftedCount source.carrier source.k z ≤
        source.y * sieveProduct source.k z /
            (sieveProduct 1 z * Real.log xi) + xi ^ 2 :=
      hbase
    _ =
        (source.y * sieveProduct source.k z *
            (sieveProduct 1 z)⁻¹) /
              Real.log xi + xi ^ 2 := by
      field_simp [(sieveProduct_pos 1 z).ne', hLogXi.ne']
    _ ≤
        (source.y * sieveProduct source.k z *
          (Real.exp Real.eulerMascheroniConstant * Real.log z + B)) /
              Real.log xi + xi ^ 2 :=
      add_le_add hdivided le_rfl
    _ =
        source.y * sieveProduct source.k z *
            ((Real.exp Real.eulerMascheroniConstant * Real.log z + B) /
              Real.log xi) +
          xi ^ 2 := by
      ring

/-- Omitting the primes dividing `k` can only increase the literal Euler
product. -/
theorem sieveProduct_one_le (k : ℕ) (z : ℝ) :
    sieveProduct 1 z ≤ sieveProduct k z := by
  let d := excludedSiftingFactor k z
  have hd :
      d ∣ (siftingPrimes 1 z).prod id :=
    excludedSiftingFactor_dvd_siftingPrimes_one k z
  have hprodPos : 0 < (siftingPrimes 1 z).prod id :=
    Finset.prod_pos (fun p hp => (mem_siftingPrimes.mp hp).1.pos)
  have hdPos : 0 < d := Nat.pos_of_dvd_of_pos hd hprodPos
  have hratio :
      (Nat.totient d : ℝ) / (d : ℝ) ≤ 1 := by
    exact (div_le_one (by exact_mod_cast hdPos)).2
      (by exact_mod_cast Nat.totient_le d)
  rw [sieveProduct_one_eq_mul_excludedFactor]
  exact
    (mul_le_mul_of_nonneg_left hratio
      (sieveProduct_pos k z).le).trans_eq (mul_one _)

/-- The complementary-ratio branch of the auxiliary logarithmic-square bound.
Theorem 2, the source cutoff `xi^2 = y / log z`, and the harmonic denominator
give a uniform multiple of the main term; bounded
`log y / log(z)^2` converts that multiple to the required exponential scale. -/
theorem RegularSource.exists_siftedCount_le_rankin_logSq_of_ratio_le :
    ∃ C > 0, ∀ (source : RegularSource) {z : ℝ},
      0 < z → 2 ≤ Real.log z → Real.log z ≤ Real.log source.y →
      Real.log source.y / Real.log z ^ 2 ≤ 32 * Real.exp 1 + 2 →
      siftedCount source.carrier source.k z ≤
        source.y * sieveProduct source.k z *
          (1 + C * Real.exp
            (-Real.log source.y / Real.log z ^ 2)) := by
  obtain ⟨B, hB, hInv⟩ :=
    exists_sieveProduct_one_inv_le_exp_mul_log_add
  let E := Real.exp Real.eulerMascheroniConstant
  let K := 32 * Real.exp 1 + 2
  let Q := 5 * E + 5 * B / 2
  let C := Q * Real.exp K
  have hE : 0 < E := by
    dsimp [E]
    positivity
  have hK : 0 < K := by
    dsimp [K]
    positivity
  have hQ : 0 < Q := by
    dsimp [Q]
    positivity
  refine
    ⟨C, by dsimp [C]; positivity,
      fun source z hzPos hlog hzy hratio => ?_⟩
  let Z := Real.log z
  let L := Real.log source.y
  let xi := fourOneCutoff source.y z
  let T := selbergRealSmoothReciprocalSum xi z
  let R := sieveProduct source.k z
  have hZ : 0 < Z := by
    dsimp [Z]
    linarith
  have hzOne : 1 < z := by
    exact (Real.log_pos_iff hzPos.le).mp (by
      dsimp [Z] at hZ
      exact hZ)
  have hyPos : 0 < source.y := zero_lt_one.trans source.one_lt_y
  have hXiLower :
      z ^ (1 / 4 : ℝ) ≤ xi := by
    exact rpow_quarter_le_fourOneCutoff hyPos hzPos hlog hzy
  have hPowOne : 1 < z ^ (1 / 4 : ℝ) := by
    simpa only [Real.rpow_zero] using
      Real.rpow_lt_rpow_of_exponent_lt hzOne
        (by norm_num : (0 : ℝ) < 1 / 4)
  have hXiOne : 1 < xi := hPowOne.trans_le hXiLower
  have hXiNonneg : 0 ≤ xi := zero_le_one.trans hXiOne.le
  have hTLower : Z / 4 ≤ T := by
    simpa [Z, xi, T] using
      quarter_log_le_fourOneSmoothReciprocalSum
        hyPos hzPos hlog hzy
  have hTPos : 0 < T := (by positivity : 0 < Z / 4).trans_le hTLower
  have hRPos : 0 < R := by
    dsimp [R]
    exact sieveProduct_pos source.k z
  have hInvOne :
      (sieveProduct 1 z)⁻¹ ≤ E * Z + B := by
    simpa [E, Z] using hInv z hzOne
  have hRatioMain :
      (sieveProduct 1 z)⁻¹ / T ≤ 4 * E + 2 * B := by
    apply (div_le_iff₀ hTPos).2
    calc
      (sieveProduct 1 z)⁻¹ ≤ E * Z + B := hInvOne
      _ ≤ (4 * E + 2 * B) * (Z / 4) := by
        nlinarith [hB.le, hE.le]
      _ ≤ (4 * E + 2 * B) * T :=
        mul_le_mul_of_nonneg_left hTLower (by positivity)
  have hBase := source.siftedCount_le_theoremTwo hzOne hXiOne
  have hMain :
      source.y * R /
          (sieveProduct 1 z * T) ≤
        source.y * R * (4 * E + 2 * B) := by
    calc
      source.y * R /
            (sieveProduct 1 z * T) =
          source.y * R * ((sieveProduct 1 z)⁻¹ / T) := by
        field_simp [(sieveProduct_pos 1 z).ne', hTPos.ne']
      _ ≤ source.y * R * (4 * E + 2 * B) :=
        mul_le_mul_of_nonneg_left hRatioMain
          (mul_nonneg hyPos.le hRPos.le)
  have hRInv :
      R⁻¹ ≤ E * Z + B := by
    have hProduct :=
      one_div_le_one_div_of_le (sieveProduct_pos 1 z)
        (sieveProduct_one_le source.k z)
    rw [inv_eq_one_div]
    exact hProduct.trans (by
      simpa only [inv_eq_one_div] using hInvOne)
  have hRPay :
      1 ≤ R * (E * Z + B) := by
    simpa [mul_comm] using
      (inv_le_iff_one_le_mul₀ hRPos).mp hRInv
  have hCoeff :
      E * Z + B ≤ Z * (E + B / 2) := by
    nlinarith [hB.le]
  have hPay :
      source.y / Z ≤ source.y * R * (E + B / 2) := by
    apply (div_le_iff₀ hZ).2
    have hRPay' : 1 ≤ R * (Z * (E + B / 2)) :=
      hRPay.trans
        (mul_le_mul_of_nonneg_left hCoeff hRPos.le)
    calc
      source.y = source.y * 1 := by ring
      _ ≤ source.y * (R * (Z * (E + B / 2))) :=
        mul_le_mul_of_nonneg_left hRPay' hyPos.le
      _ = source.y * R * (E + B / 2) * Z := by ring
  have hXiSq : xi ^ 2 = source.y / Z := by
    simpa [xi, Z] using fourOneCutoff_sq hyPos.le hZ
  have hPsi :
      selbergRealPsi xi z ^ 2 ≤
        source.y * R * (E + B / 2) := by
    have hPsiSelf := selbergRealPsi_le_self (z := z) hXiNonneg
    have hPsiNonneg : 0 ≤ selbergRealPsi xi z := by
      unfold selbergRealPsi
      exact Nat.cast_nonneg _
    calc
      selbergRealPsi xi z ^ 2 ≤ xi ^ 2 := by nlinarith
      _ = source.y / Z := hXiSq
      _ ≤ source.y * R * (E + B / 2) := hPay
  have hUniform :
      siftedCount source.carrier source.k z ≤ source.y * R * Q := by
    calc
      siftedCount source.carrier source.k z ≤
          source.y * R /
              (sieveProduct 1 z * T) +
            selbergRealPsi xi z ^ 2 := by
        simpa [xi, T, R] using hBase
      _ ≤ source.y * R * (4 * E + 2 * B) +
          source.y * R * (E + B / 2) :=
        add_le_add hMain hPsi
      _ = source.y * R * Q := by
        dsimp [Q]
        ring
  have hExp :
      Q ≤ C * Real.exp (-L / Z ^ 2) := by
    have hExpMono :
        Real.exp (-K) ≤ Real.exp (-L / Z ^ 2) :=
      Real.exp_le_exp.mpr (by
        have hratio' : L / Z ^ 2 ≤ K := by
          simpa only [L, Z, K] using hratio
        calc
          -K ≤ -(L / Z ^ 2) := neg_le_neg hratio'
          _ = -L / Z ^ 2 := by ring)
    calc
      Q = C * Real.exp (-K) := by
        dsimp [C]
        rw [mul_assoc, ← Real.exp_add]
        simp
      _ ≤ C * Real.exp (-L / Z ^ 2) :=
        mul_le_mul_of_nonneg_left hExpMono (by
          dsimp [C]
          positivity)
  calc
    siftedCount source.carrier source.k z ≤ source.y * R * Q :=
      hUniform
    _ ≤ source.y * R *
        (1 + C * Real.exp (-L / Z ^ 2)) := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hyPos.le hRPos.le)
      linarith
    _ = source.y * sieveProduct source.k z *
        (1 + C * Real.exp
          (-Real.log source.y / Real.log z ^ 2)) := by
      rfl

set_option maxHeartbeats 800000

/-- The genuinely large-ratio branch of the auxiliary logarithmic-square bound.
Here the finite Rankin tail controls the Selberg denominator and a
logarithmic-square Rankin consequence controls the complete Selberg error,
both at the source cutoff
`xi^2 = y / log z`. -/
theorem RegularSource.exists_siftedCount_le_rankin_logSq_of_ratio_ge :
    ∃ C > 0, ∀ (source : RegularSource) {z : ℝ},
      0 < z → 2 ≤ Real.log z → Real.log z ≤ Real.log source.y →
      32 * Real.exp 1 + 2 ≤
        Real.log source.y / Real.log z ^ 2 →
      siftedCount source.carrier source.k z ≤
        source.y * sieveProduct source.k z *
          (1 + C * Real.exp
            (-Real.log source.y / Real.log z ^ 2)) := by
  obtain ⟨B, hB, hInv⟩ :=
    exists_sieveProduct_one_inv_le_exp_mul_log_add
  let E := Real.exp Real.eulerMascheroniConstant
  let K := 32 * Real.exp 1 + 2
  let A := Real.exp (24 * Real.exp 1)
  let Ctail := 8 * Real.exp (12 * Real.exp 1 + 1)
  let Cpsi := (E + B / 2) * A ^ 2 * Real.exp 1
  let C := Ctail + Cpsi
  have hE : 0 < E := by
    dsimp [E]
    positivity
  have hA : 0 < A := by
    dsimp [A]
    positivity
  have hCtail : 0 < Ctail := by
    dsimp [Ctail]
    positivity
  have hCpsi : 0 < Cpsi := by
    dsimp [Cpsi]
    positivity
  refine
    ⟨C, by dsimp [C]; positivity,
      fun source z hzPos hlog hzy hratio => ?_⟩
  let Z := Real.log z
  let L := Real.log source.y
  let xi := fourOneCutoff source.y z
  let n := ⌊xi⌋₊
  let T := selbergRealSmoothReciprocalSum xi z
  let R := sieveProduct source.k z
  have hZ : 0 < Z := by
    dsimp [Z]
    linarith
  have hZTwo : 2 ≤ Z := by simpa only [Z] using hlog
  have hZsq : 0 < Z ^ 2 := sq_pos_of_pos hZ
  have hzOne : 1 < z :=
    (Real.log_pos_iff hzPos.le).mp (by simpa only [Z] using hZ)
  have hyPos : 0 < source.y := zero_lt_one.trans source.one_lt_y
  have hLlarge : K * Z ^ 2 ≤ L := by
    apply (le_div_iff₀ hZsq).mp
    simpa only [K, L, Z] using hratio
  have hLogZSub : Real.log Z ≤ Z - 1 :=
    Real.log_le_sub_one_of_pos hZ
  have hLogZ : Real.log Z ≤ Z := by linarith
  have hLogTwo : Real.log 2 ≤ 1 := by
    have h :=
      Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h.le
  have hXiPos : 0 < xi := by
    dsimp [xi, fourOneCutoff]
    positivity
  have hLogXi :
      Real.log xi = (L - Real.log Z) / 2 := by
    simpa only [xi, L, Z] using log_fourOneCutoff hyPos hZ
  have hLogXiOne : 1 ≤ Real.log xi := by
    rw [hLogXi]
    have hKOne : 1 ≤ K := by
      dsimp [K]
      nlinarith [Real.exp_pos 1]
    have hTwoZ : 2 * Z ≤ Z ^ 2 := by nlinarith
    have hTwoZL : 2 * Z ≤ L := by
      calc
        2 * Z ≤ Z ^ 2 := hTwoZ
        _ ≤ K * Z ^ 2 := by
          simpa only [one_mul] using
            mul_le_mul_of_nonneg_right hKOne (sq_nonneg Z)
        _ ≤ L := hLlarge
    nlinarith
  have hXiTwo : 2 ≤ xi := by
    have hExp :
        Real.exp 1 ≤ Real.exp (Real.log xi) :=
      Real.exp_le_exp.mpr hLogXiOne
    rw [Real.exp_log hXiPos] at hExp
    nlinarith [Real.exp_one_gt_d9]
  have hn : 1 ≤ n := by
    dsimp [n]
    exact (by omega : 1 ≤ 2).trans (Nat.le_floor hXiTwo)
  have hLogFloor :
      Real.log xi - Real.log 2 ≤ Real.log n := by
    simpa only [n] using log_sub_log_two_le_log_floor hXiTwo
  have hTLower : Z / 4 ≤ T := by
    simpa [Z, xi, T] using
      quarter_log_le_fourOneSmoothReciprocalSum
        hyPos hzPos hlog hzy
  have hTPos : 0 < T := (by positivity : 0 < Z / 4).trans_le hTLower
  have hRPos : 0 < R := by
    dsimp [R]
    exact sieveProduct_pos source.k z
  have hRankinExponent :
      4 * (Real.exp 1 * (1 + Z)) -
          Real.log n / Z ≤
        12 * Real.exp 1 + 1 - L / Z ^ 2 := by
    have hFloorMul :
        (Real.log xi - Real.log 2) * Z ≤ Real.log n * Z :=
      mul_le_mul_of_nonneg_right hLogFloor hZ.le
    rw [hLogXi] at hFloorMul
    have hLogZMul :
        Real.log Z * Z ≤ Z ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_right hLogZ hZ.le]
    have hLogTwoMul :
        Real.log 2 * Z ≤ Z := by
      nlinarith [mul_le_mul_of_nonneg_right hLogTwo hZ.le]
    have hEight :
        8 * Real.exp 1 * Z ^ 2 ≤ L := by
      have hK :
          8 * Real.exp 1 ≤ K := by
        dsimp [K]
        nlinarith [Real.exp_pos 1]
      exact
        (mul_le_mul_of_nonneg_right hK (sq_nonneg Z)).trans hLlarge
    have hAbsorb :
        8 * Real.exp 1 * Z ^ 2 * (Z - 2) ≤ L * (Z - 2) :=
      mul_le_mul_of_nonneg_right hEight (by linarith)
    rw [show
      4 * (Real.exp 1 * (1 + Z)) - Real.log n / Z =
        (4 * (Real.exp 1 * (1 + Z)) * Z ^ 2 -
          Real.log n * Z) / Z ^ 2 by
            field_simp [hZ.ne']]
    rw [show
      12 * Real.exp 1 + 1 - L / Z ^ 2 =
        ((12 * Real.exp 1 + 1) * Z ^ 2 - L) / Z ^ 2 by
            field_simp [hZ.ne']]
    apply (div_le_div_iff_of_pos_right hZsq).2
    nlinarith
  have hTailRaw :=
    sieveProduct_inv_sub_selbergSmoothReciprocalSum_le_rankin
      hn hzOne.le hlog
  have hTail :
      ((sieveProduct 1 z)⁻¹ - T) / T ≤
        Ctail * Real.exp (-L / Z ^ 2) := by
    have hRaw :
        (sieveProduct 1 z)⁻¹ - T ≤
          2 * Z *
            Real.exp (4 * (Real.exp 1 * (1 + Z))) *
            Real.exp (-Real.log n / Z) := by
      simpa only [T, selbergRealSmoothReciprocalSum, n, Z] using hTailRaw.2
    have hDiv :
        ((sieveProduct 1 z)⁻¹ - T) / T ≤
          8 * Real.exp (4 * (Real.exp 1 * (1 + Z))) *
            Real.exp (-Real.log n / Z) := by
      apply (div_le_iff₀ hTPos).2
      calc
        (sieveProduct 1 z)⁻¹ - T ≤
            2 * Z *
              Real.exp (4 * (Real.exp 1 * (1 + Z))) *
              Real.exp (-Real.log n / Z) := hRaw
        _ = (8 * Real.exp (4 * (Real.exp 1 * (1 + Z))) *
              Real.exp (-Real.log n / Z)) * (Z / 4) := by ring
        _ ≤ (8 * Real.exp (4 * (Real.exp 1 * (1 + Z))) *
              Real.exp (-Real.log n / Z)) * T :=
          mul_le_mul_of_nonneg_left hTLower (by positivity)
    calc
      ((sieveProduct 1 z)⁻¹ - T) / T ≤
          8 * Real.exp (4 * (Real.exp 1 * (1 + Z))) *
            Real.exp (-Real.log n / Z) := hDiv
      _ = 8 * Real.exp
          (4 * (Real.exp 1 * (1 + Z)) - Real.log n / Z) := by
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ ≤ 8 * Real.exp
          (12 * Real.exp 1 + 1 - L / Z ^ 2) := by
        gcongr
      _ = Ctail * Real.exp (-L / Z ^ 2) := by
        dsimp [Ctail]
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        ring
  have hBase :=
    source.siftedCount_le_theoremTwo hzOne (by linarith : 1 < xi)
  have hMainIdentity :
      source.y * R / (sieveProduct 1 z * T) =
        source.y * R *
          (1 + ((sieveProduct 1 z)⁻¹ - T) / T) := by
    field_simp [(sieveProduct_pos 1 z).ne', hTPos.ne']
    ring
  have hMain :
      source.y * R / (sieveProduct 1 z * T) ≤
        source.y * R *
          (1 + Ctail * Real.exp (-L / Z ^ 2)) := by
    rw [hMainIdentity]
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg hyPos.le hRPos.le)
    linarith
  have hInvOne :
      (sieveProduct 1 z)⁻¹ ≤ E * Z + B := by
    simpa [E, Z] using hInv z hzOne
  have hRInv :
      R⁻¹ ≤ E * Z + B := by
    have hProduct :=
      one_div_le_one_div_of_le (sieveProduct_pos 1 z)
        (sieveProduct_one_le source.k z)
    rw [inv_eq_one_div]
    exact hProduct.trans (by
      simpa only [inv_eq_one_div] using hInvOne)
  have hRPay :
      1 ≤ R * (E * Z + B) := by
    simpa [mul_comm] using
      (inv_le_iff_one_le_mul₀ hRPos).mp hRInv
  have hCoeff :
      E * Z + B ≤ Z * (E + B / 2) := by
    nlinarith [hB.le]
  have hPay :
      source.y / Z ≤ source.y * R * (E + B / 2) := by
    apply (div_le_iff₀ hZ).2
    have hRPay' : 1 ≤ R * (Z * (E + B / 2)) :=
      hRPay.trans
        (mul_le_mul_of_nonneg_left hCoeff hRPos.le)
    nlinarith [mul_le_mul_of_nonneg_left hRPay' hyPos.le]
  have hXiSq : xi ^ 2 = source.y / Z := by
    simpa [xi, Z] using fourOneCutoff_sq hyPos.le hZ
  have hPsiExponent :
      -4 * Real.log xi / Z ^ 2 ≤ 1 - L / Z ^ 2 := by
    rw [hLogXi]
    have hRatioNonneg : 0 ≤ L / Z ^ 2 :=
      le_trans (by positivity : 0 ≤ K) (by
        simpa only [K, L, Z] using hratio)
    rw [show
      -4 * ((L - Real.log Z) / 2) / Z ^ 2 =
        (-2 * L + 2 * Real.log Z) / Z ^ 2 by ring]
    rw [show
      1 - L / Z ^ 2 = (Z ^ 2 - L) / Z ^ 2 by
        field_simp [hZ.ne']]
    apply (div_le_div_iff_of_pos_right hZsq).2
    have hLogBound : 2 * Real.log Z ≤ Z ^ 2 := by
      nlinarith [sq_nonneg (Z - 1)]
    nlinarith
  have hPsiExp :
      Real.exp (-4 * Real.log xi / Z ^ 2) ≤
        Real.exp 1 * Real.exp (-L / Z ^ 2) := by
    calc
      Real.exp (-4 * Real.log xi / Z ^ 2) ≤
          Real.exp (1 - L / Z ^ 2) :=
        Real.exp_le_exp.mpr hPsiExponent
      _ = Real.exp 1 * Real.exp (-L / Z ^ 2) := by
        rw [← Real.exp_add]
        congr 1
        ring
  have hVinogradov :=
    selbergRealPsi_le_rankin_logSq
      (by linarith : 1 ≤ xi) hzOne.le hlog
  have hPsiNonneg : 0 ≤ selbergRealPsi xi z := by
    unfold selbergRealPsi
    exact Nat.cast_nonneg _
  have hVinogradovNonneg :
      0 ≤ A * (xi * Real.exp (-2 * Real.log xi / Z ^ 2)) := by
    positivity
  have hVinogradov' :
      selbergRealPsi xi z ≤
        A * (xi * Real.exp (-2 * Real.log xi / Z ^ 2)) := by
    simpa only [A, Z] using hVinogradov
  have hPsiSq :
      selbergRealPsi xi z ^ 2 ≤
        A ^ 2 * xi ^ 2 *
          Real.exp (-4 * Real.log xi / Z ^ 2) := by
    calc
      selbergRealPsi xi z ^ 2 ≤
          (A * (xi * Real.exp
            (-2 * Real.log xi / Z ^ 2))) ^ 2 :=
        (sq_le_sq₀ hPsiNonneg hVinogradovNonneg).2 hVinogradov'
      _ = A ^ 2 * xi ^ 2 *
          Real.exp (-4 * Real.log xi / Z ^ 2) := by
        have hExpSq :
          Real.exp (-2 * Real.log xi / Z ^ 2) ^ 2 =
            Real.exp (-4 * Real.log xi / Z ^ 2) := by
          rw [pow_two, ← Real.exp_add]
          congr 1
          ring
        calc
          (A * (xi * Real.exp
              (-2 * Real.log xi / Z ^ 2))) ^ 2 =
              A ^ 2 * xi ^ 2 *
                Real.exp (-2 * Real.log xi / Z ^ 2) ^ 2 := by ring
          _ = _ := by rw [hExpSq]
  have hPsi :
      selbergRealPsi xi z ^ 2 ≤
        source.y * R * Cpsi * Real.exp (-L / Z ^ 2) := by
    calc
      selbergRealPsi xi z ^ 2 ≤
          A ^ 2 * xi ^ 2 *
            Real.exp (-4 * Real.log xi / Z ^ 2) := hPsiSq
      _ ≤ A ^ 2 * xi ^ 2 *
            (Real.exp 1 * Real.exp (-L / Z ^ 2)) :=
        mul_le_mul_of_nonneg_left hPsiExp (by positivity)
      _ = A ^ 2 * (source.y / Z) *
            (Real.exp 1 * Real.exp (-L / Z ^ 2)) := by
        rw [hXiSq]
      _ ≤ A ^ 2 * (source.y * R * (E + B / 2)) *
            (Real.exp 1 * Real.exp (-L / Z ^ 2)) := by
        gcongr
      _ = source.y * R * Cpsi * Real.exp (-L / Z ^ 2) := by
        dsimp [Cpsi]
        ring
  calc
    siftedCount source.carrier source.k z ≤
        source.y * R /
            (sieveProduct 1 z * T) +
          selbergRealPsi xi z ^ 2 := by
      simpa [xi, T, R] using hBase
    _ ≤ source.y * R *
          (1 + Ctail * Real.exp (-L / Z ^ 2)) +
        source.y * R * Cpsi * Real.exp (-L / Z ^ 2) :=
      add_le_add hMain hPsi
    _ = source.y * R *
        (1 + C * Real.exp (-L / Z ^ 2)) := by
      dsimp [C]
      ring
    _ = source.y * sieveProduct source.k z *
        (1 + C * Real.exp
          (-Real.log source.y / Real.log z ^ 2)) := by
      rfl

set_option maxHeartbeats 200000

/-- An auxiliary upper bound for the literal `gamma(p)=1`, `q=1` source.
This is not printed `(4.1)`: the scan has denominator `log z`, not
`(log z)^2`.  The weaker rate here does not imply `(4.2)` on its printed
range.  The proof separates bounded `z` by finite Möbius expansion, then
combines the Rankin tail with the harmonic/trivial-`Psi` estimate. -/
theorem RegularSource.exists_siftedCount_le_rankin_logSq :
    ∃ C > 0, ∀ (source : RegularSource) {z : ℝ},
      0 < z → 1 ≤ Real.log z →
      Real.log z ≤ Real.log source.y →
      siftedCount source.carrier source.k z ≤
        source.y * sieveProduct source.k z *
          (1 + C * Real.exp
            (-Real.log source.y / Real.log z ^ 2)) := by
  obtain ⟨D, hD, hBounded⟩ :=
    RegularSource.exists_siftedCount_le_moebius_boundedZ
  obtain ⟨Csmall, hCsmall, hSmall⟩ :=
    RegularSource.exists_siftedCount_le_rankin_logSq_of_ratio_le
  obtain ⟨Clarge, hClarge, hLarge⟩ :=
    RegularSource.exists_siftedCount_le_rankin_logSq_of_ratio_ge
  let R₀ := sieveProduct 1 (Real.exp 2)
  let Cbounded := D / R₀
  let C := Cbounded + Csmall + Clarge
  have hR₀ : 0 < R₀ := by
    dsimp [R₀]
    exact sieveProduct_pos 1 (Real.exp 2)
  have hCbounded : 0 < Cbounded := by
    dsimp [Cbounded]
    positivity
  refine
    ⟨C, by dsimp [C]; positivity,
      fun source z hzPos hlogOne hzy => ?_⟩
  let Z := Real.log z
  let L := Real.log source.y
  let R := sieveProduct source.k z
  let e := Real.exp (-L / Z ^ 2)
  have hZ : 0 < Z := by
    dsimp [Z]
    linarith
  have hZsq : 0 < Z ^ 2 := sq_pos_of_pos hZ
  have hyPos : 0 < source.y := zero_lt_one.trans source.one_lt_y
  have hRPos : 0 < R := by
    dsimp [R]
    exact sieveProduct_pos source.k z
  have hePos : 0 < e := by
    dsimp [e]
    positivity
  by_cases hBound : Z ≤ 2
  · have hMobius := hBounded source hzPos (by
      simpa only [Z] using hBound)
    have hR₀R : R₀ ≤ R := by
      simpa only [R₀, R, Z] using
        sieveProduct_exp_two_le_of_log_le_two
          (k := source.k) hzPos hBound
    have hL : 0 ≤ L := by
      dsimp [L]
      exact (Real.log_pos source.one_lt_y).le
    have hZsqOne : 1 ≤ Z ^ 2 := by nlinarith
    have hInv : 1 / Z ^ 2 ≤ 1 := by
      exact (div_le_one hZsq).2 hZsqOne
    have hExponent : 0 ≤ L + (-L / Z ^ 2) := by
      rw [show L + (-L / Z ^ 2) = L * (1 - 1 / Z ^ 2) by ring]
      positivity
    have hYe : 1 ≤ source.y * e := by
      dsimp [e]
      rw [← Real.exp_log hyPos, ← Real.exp_add, ← Real.exp_zero]
      exact Real.exp_le_exp.mpr (by simpa only [L] using hExponent)
    have hCboundedC : Cbounded ≤ C := by
      dsimp [C]
      linarith [hCsmall, hClarge]
    have hAbsorb : D ≤ source.y * R * C * e := by
      calc
        D = 1 * R₀ * Cbounded := by
          dsimp [Cbounded]
          field_simp [hR₀.ne']
        _ ≤ (source.y * e) * R * C := by
          gcongr
        _ = source.y * R * C * e := by ring
    calc
      siftedCount source.carrier source.k z ≤
          source.y * R + D := by simpa only [R] using hMobius
      _ ≤ source.y * R + source.y * R * C * e :=
        add_le_add le_rfl hAbsorb
      _ = source.y * R * (1 + C * e) := by ring
      _ = source.y * sieveProduct source.k z *
          (1 + C * Real.exp
            (-Real.log source.y / Real.log z ^ 2)) := by
        rfl
  · have hZTwo : 2 ≤ Z := le_of_not_ge hBound
    by_cases hRatio :
        L / Z ^ 2 ≤ 32 * Real.exp 1 + 2
    · have hCase :=
        hSmall source hzPos (by simpa only [Z] using hZTwo) hzy
          (by simpa only [L, Z] using hRatio)
      have hCsmallC : Csmall ≤ C := by
        dsimp [C]
        linarith [hCbounded, hClarge]
      calc
        siftedCount source.carrier source.k z ≤
            source.y * R *
              (1 + Csmall * e) := by
          simpa only [R, e, L, Z] using hCase
        _ ≤ source.y * R * (1 + C * e) := by
          apply mul_le_mul_of_nonneg_left _
            (mul_nonneg hyPos.le hRPos.le)
          gcongr
        _ = source.y * sieveProduct source.k z *
            (1 + C * Real.exp
              (-Real.log source.y / Real.log z ^ 2)) := by
          rfl
    · have hRatio' :
          32 * Real.exp 1 + 2 ≤ L / Z ^ 2 :=
        le_of_not_ge hRatio
      have hCase :=
        hLarge source hzPos (by simpa only [Z] using hZTwo) hzy
          (by simpa only [L, Z] using hRatio')
      have hClargeC : Clarge ≤ C := by
        dsimp [C]
        linarith [hCbounded, hCsmall]
      calc
        siftedCount source.carrier source.k z ≤
            source.y * R *
              (1 + Clarge * e) := by
          simpa only [R, e, L, Z] using hCase
        _ ≤ source.y * R * (1 + C * e) := by
          apply mul_le_mul_of_nonneg_left _
            (mul_nonneg hyPos.le hRPos.le)
          gcongr
        _ = source.y * sieveProduct source.k z *
            (1 + C * Real.exp
              (-Real.log source.y / Real.log z ^ 2)) := by
          rfl

/-- The `d = 1` case of the printed regularity hypothesis bounds the whole
source, hence every sifted subset, by `y + 1`. -/
theorem RegularSource.siftedCount_le_y_add_one
    (source : RegularSource) (z : ℝ) :
    siftedCount source.carrier source.k z ≤ source.y + 1 := by
  have hregular :=
    source.regular 1 (by norm_num) (by simp)
  have hcard :
      (source.carrier.card : ℝ) ≤ source.y + 1 := by
    have := (abs_le.mp hregular).2
    norm_num at this
    linarith
  calc
    siftedCount source.carrier source.k z =
        ((source.carrier.filter fun n =>
          Nat.Coprime ((siftingPrimes source.k z).prod id) n).card : ℝ) := rfl
    _ ≤ (source.carrier.card : ℝ) := by
      exact_mod_cast Finset.card_filter_le source.carrier
        (fun n => Nat.Coprime ((siftingPrimes source.k z).prod id) n)
    _ ≤ source.y + 1 := hcard

/-- The source's literal optimizing cutoff
`xi^2 = y / (1 + log(y)^2)`. -/
noncomputable def threeNineCutoff (y : ℝ) : ℝ :=
  Real.sqrt (y / (1 + Real.log y ^ 2))

theorem threeNineCutoff_sq {y : ℝ} (hy : 0 ≤ y) :
    threeNineCutoff y ^ 2 = y / (1 + Real.log y ^ 2) := by
  rw [threeNineCutoff, Real.sq_sqrt]
  positivity

/-- The logarithm lost in the source's optimized cutoff is at most twice the
displayed `log log(3y)` error factor. -/
private theorem log_one_add_log_sq_le_two_log_log_three_mul
    {y : ℝ} (hy : 1 < y) :
    Real.log (1 + Real.log y ^ 2) ≤
      2 * Real.log (Real.log (3 * y)) := by
  have hy0 : 0 < y := zero_lt_one.trans hy
  have hL : 0 < Real.log y := Real.log_pos hy
  have hExpOneThree : Real.exp 1 ≤ (3 : ℝ) := by
    nlinarith [Real.exp_one_lt_d9]
  have hLogThree : 1 ≤ Real.log (3 : ℝ) :=
    (Real.le_log_iff_exp_le (by norm_num)).2 hExpOneThree
  have hLogMul :
      Real.log (3 * y) = Real.log 3 + Real.log y := by
    rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) hy0.ne']
  have hBase :
      Real.log y + 1 ≤ Real.log (3 * y) := by
    rw [hLogMul]
    linarith
  have hBasePos : 0 < Real.log y + 1 := by linarith
  have hTargetPos : 0 < Real.log (3 * y) :=
    hBasePos.trans_le hBase
  have hSq :
      1 + Real.log y ^ 2 ≤ (Real.log y + 1) ^ 2 := by
    nlinarith
  calc
    Real.log (1 + Real.log y ^ 2) ≤
        Real.log ((Real.log y + 1) ^ 2) :=
      Real.strictMonoOn_log.monotoneOn
          (add_pos_of_pos_of_nonneg zero_lt_one (sq_nonneg (Real.log y)))
        (sq_pos_of_pos hBasePos) hSq
    _ = 2 * Real.log (Real.log y + 1) := by
      rw [Real.log_pow]
      norm_num
    _ ≤ 2 * Real.log (Real.log (3 * y)) := by
      exact mul_le_mul_of_nonneg_left
        (Real.strictMonoOn_log.monotoneOn hBasePos hTargetPos hBase)
        (by norm_num)

/-- At the explicit large-source threshold, the secondary logarithm consumes
at most one quarter of `log y`.  The proof is symbolic and uses no finite
parameter scan. -/
private theorem log_log_three_mul_le_quarter_log
    {y : ℝ} (hy : 1 < y) (hyLarge : 64 ≤ Real.log y) :
    Real.log (Real.log (3 * y)) ≤ Real.log y / 4 := by
  have hy0 : 0 < y := zero_lt_one.trans hy
  have hL : 0 < Real.log y := Real.log_pos hy
  have hLogThreeUpper : Real.log (3 : ℝ) ≤ 2 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
    norm_num at this ⊢
    exact this
  have hLogMul :
      Real.log (3 * y) = Real.log 3 + Real.log y := by
    rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) hy0.ne']
  have hInnerUpper :
      Real.log (3 * y) ≤ 2 * Real.log y := by
    rw [hLogMul]
    linarith
  have hInnerPos : 0 < Real.log (3 * y) := by
    rw [hLogMul]
    have hLogThreePos : 0 < Real.log (3 : ℝ) := Real.log_pos (by norm_num)
    linarith
  have hTwoLPos : 0 < 2 * Real.log y := by positivity
  have hLogL :
      Real.log (Real.log y) ≤ Real.log y / 8 + 6 := by
    have hEight : Real.log (8 : ℝ) ≤ 7 := by
      convert
        (Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 8)) using 1;
          norm_num
    have hDivPos : 0 < Real.log y / 8 := by positivity
    have hDiv :
        Real.log (Real.log y / 8) ≤ Real.log y / 8 - 1 :=
      Real.log_le_sub_one_of_pos hDivPos
    calc
      Real.log (Real.log y) =
          Real.log 8 + Real.log (Real.log y / 8) := by
        rw [← Real.log_mul (by norm_num : (8 : ℝ) ≠ 0) hDivPos.ne']
        congr 1
        ring
      _ ≤ 7 + (Real.log y / 8 - 1) := add_le_add hEight hDiv
      _ = Real.log y / 8 + 6 := by ring
  have hLogTwo : Real.log (2 : ℝ) ≤ 1 := by
    convert
      (Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)) using 1;
        norm_num
  calc
    Real.log (Real.log (3 * y)) ≤
        Real.log (2 * Real.log y) :=
      Real.strictMonoOn_log.monotoneOn hInnerPos hTwoLPos hInnerUpper
    _ = Real.log 2 + Real.log (Real.log y) := by
      rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hL.ne']
    _ ≤ 1 + (Real.log y / 8 + 6) := add_le_add hLogTwo hLogL
    _ ≤ Real.log y / 4 := by linarith

private theorem log_threeNineCutoff
    {y : ℝ} (hy : 1 < y) :
    Real.log (threeNineCutoff y) =
      (Real.log y - Real.log (1 + Real.log y ^ 2)) / 2 := by
  have hy0 : 0 < y := zero_lt_one.trans hy
  have hden : 0 < 1 + Real.log y ^ 2 := by positivity
  rw [threeNineCutoff, Real.log_sqrt (div_nonneg hy0.le hden.le),
    Real.log_div hy0.ne' hden.ne']

/-- The reciprocal logarithm at the source cutoff has leading term
`2 / log y`; the remaining loss has exactly the `(3.9)` log-log shape. -/
private theorem one_div_log_threeNineCutoff_le
    {y : ℝ} (hy : 1 < y) (hyLarge : 64 ≤ Real.log y) :
    1 / Real.log (threeNineCutoff y) ≤
      2 / Real.log y +
        8 * Real.log (Real.log (3 * y)) / Real.log y ^ 2 := by
  let L := Real.log y
  let a := Real.log (1 + Real.log y ^ 2)
  let G := Real.log (Real.log (3 * y))
  have hL : 0 < L := by
    dsimp [L]
    exact Real.log_pos hy
  have hG : 0 ≤ G := by
    have hExpOneThree : Real.exp 1 ≤ (3 : ℝ) := by
      nlinarith [Real.exp_one_lt_d9]
    have hLogThree : 1 ≤ Real.log (3 : ℝ) :=
      (Real.le_log_iff_exp_le (by norm_num)).2 hExpOneThree
    have hLogMul :
        Real.log (3 * y) = Real.log 3 + Real.log y := by
      rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0)
        (zero_lt_one.trans hy).ne']
    dsimp [G]
    exact Real.log_nonneg (by rw [hLogMul]; linarith)
  have haG : a ≤ 2 * G := by
    simpa [a, G] using
      log_one_add_log_sq_le_two_log_log_three_mul hy
  have hGL : G ≤ L / 4 := by
    simpa [G, L] using log_log_three_mul_le_quarter_log hy hyLarge
  have haL : a ≤ L / 2 := by linarith
  have hcutLog :
      Real.log (threeNineCutoff y) = (L - a) / 2 := by
    simpa [L, a] using log_threeNineCutoff hy
  have hcutLogPos : 0 < Real.log (threeNineCutoff y) := by
    rw [hcutLog]
    linarith
  have hDenPos : 0 < (L - a) / 2 := by
    rw [← hcutLog]
    exact hcutLogPos
  rw [hcutLog]
  change 1 / ((L - a) / 2) ≤ 2 / L + 8 * G / L ^ 2
  apply (div_le_iff₀ hDenPos).2
  field_simp [hL.ne']
  nlinarith [mul_nonneg hG (sub_nonneg.mpr (by linarith : 0 ≤ L - 2 * a))]

/-- The exact large-`y` branch of the source corollary `(3.9)`, at the literal
choice `xi^2 = y / (1 + log(y)^2)`.  All constants are absolute and the
bounded branch is deliberately not hidden in this theorem. -/
theorem RegularSource.exists_siftedCount_le_threeNine_of_log_ge :
    ∃ c₁ > 0, ∀ (source : RegularSource) {z : ℝ},
      64 ≤ Real.log source.y → Real.sqrt source.y ≤ z →
      siftedCount source.carrier source.k z ≤
        source.y * sieveProduct source.k z *
          (2 * Real.exp Real.eulerMascheroniConstant * Real.log z /
              Real.log source.y +
            c₁ * Real.log z * Real.log (Real.log (3 * source.y)) /
              Real.log source.y ^ 2) := by
  obtain ⟨B, hB, hPostMertens⟩ :=
    RegularSource.exists_siftedCount_le_theoremTwo_mertens
  obtain ⟨B₀, hB₀, hInvProductOne⟩ :=
    exists_sieveProduct_one_inv_le_exp_mul_log_add
  let E := Real.exp Real.eulerMascheroniConstant
  let c₁ := 9 * E + 12 * B + 2 * B₀
  have hE : 0 < E := by
    dsimp [E]
    positivity
  refine ⟨c₁, by dsimp [c₁]; positivity, fun source z hyLarge hz => ?_⟩
  let L := Real.log source.y
  let G := Real.log (Real.log (3 * source.y))
  let xi := threeNineCutoff source.y
  have hy : 1 < source.y := source.one_lt_y
  have hy0 : 0 < source.y := zero_lt_one.trans hy
  have hL : 0 < L := by
    dsimp [L]
    exact Real.log_pos hy
  have hZ : L / 2 ≤ Real.log z := by
    have hsqrtPos : 0 < Real.sqrt source.y := Real.sqrt_pos.2 hy0
    have hzPos : 0 < z := hsqrtPos.trans_le hz
    calc
      L / 2 = Real.log (Real.sqrt source.y) := by
        dsimp [L]
        rw [Real.log_sqrt hy0.le]
      _ ≤ Real.log z :=
        Real.strictMonoOn_log.monotoneOn hsqrtPos hzPos hz
  have hzOne : 1 < z := by
    have hsqrtOne : 1 < Real.sqrt source.y := by
      rw [Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 1)]
      simpa using hy
    exact hsqrtOne.trans_le hz
  have hLogZ : 0 < Real.log z := Real.log_pos hzOne
  have hG : 1 ≤ G := by
    have hExpOneThree : Real.exp 1 ≤ (3 : ℝ) := by
      nlinarith [Real.exp_one_lt_d9]
    have hLogThree : 1 ≤ Real.log (3 : ℝ) :=
      (Real.le_log_iff_exp_le (by norm_num)).2 hExpOneThree
    have hLogMul :
        Real.log (3 * source.y) =
          Real.log 3 + Real.log source.y := by
      rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) hy0.ne']
    dsimp [G]
    apply (Real.le_log_iff_exp_le (by rw [hLogMul]; linarith)).2
    nlinarith [Real.exp_one_lt_d9]
  have haL :
      Real.log (1 + L ^ 2) ≤ L / 2 := by
    have haG :
        Real.log (1 + L ^ 2) ≤ 2 * G := by
      simpa [L, G] using
        log_one_add_log_sq_le_two_log_log_three_mul hy
    have hGL : G ≤ L / 4 := by
      simpa [L, G] using
        log_log_three_mul_le_quarter_log hy hyLarge
    linarith
  have hXiLog :
      Real.log xi =
        (L - Real.log (1 + L ^ 2)) / 2 := by
    simpa [xi, L] using log_threeNineCutoff hy
  have hXiLogPos : 0 < Real.log xi := by
    rw [hXiLog]
    linarith
  have hXiPos : 0 < xi := by
    dsimp [xi, threeNineCutoff]
    positivity
  have hXiOne : 1 < xi := by
    rw [← Real.exp_zero, ← Real.exp_log hXiPos]
    exact Real.exp_lt_exp.mpr hXiLogPos
  have hXiSqrt : xi < Real.sqrt source.y := by
    dsimp [xi, threeNineCutoff]
    apply Real.sqrt_lt_sqrt
    · positivity
    · have hden : 1 < 1 + L ^ 2 := by
        have : 0 < L ^ 2 := sq_pos_of_pos hL
        linarith
      have hdenPos : 0 < 1 + L ^ 2 := zero_lt_one.trans hden
      apply (div_lt_iff₀ hdenPos).2
      nlinarith [hy0]
  have hXiZ : xi < z := hXiSqrt.trans_le hz
  have hBase := hPostMertens source hzOne hXiOne hXiZ
  have hInvXi :
      1 / Real.log xi ≤ 2 / L + 8 * G / L ^ 2 := by
    simpa [xi, L, G] using
      one_div_log_threeNineCutoff_le hy hyLarge
  have hQ :
      0 ≤ 2 / L + 8 * G / L ^ 2 := by positivity
  have hNumerator :
      0 ≤ E * Real.log z + B := by positivity
  have hBMain :
      2 * B / L ≤ 4 * B * Real.log z * G / L ^ 2 := by
    apply (div_le_iff₀ hL).2
    field_simp [hL.ne']
    nlinarith [mul_nonneg hB.le (by linarith : 0 ≤ G)]
  have hBError :
      8 * B * G / L ^ 2 ≤
        8 * B * Real.log z * G / L ^ 2 := by
    apply (div_le_div_iff_of_pos_right (sq_pos_of_pos hL)).2
    nlinarith [mul_nonneg hB.le (by linarith : 0 ≤ G)]
  have hCoefficient :
      (E * Real.log z + B) / Real.log xi ≤
        2 * E * Real.log z / L +
          (8 * E + 12 * B) * Real.log z * G / L ^ 2 := by
    calc
      (E * Real.log z + B) / Real.log xi =
          (E * Real.log z + B) * (1 / Real.log xi) := by ring
      _ ≤ (E * Real.log z + B) *
          (2 / L + 8 * G / L ^ 2) :=
        mul_le_mul_of_nonneg_left hInvXi hNumerator
      _ =
          2 * E * Real.log z / L +
            8 * E * Real.log z * G / L ^ 2 +
            2 * B / L + 8 * B * G / L ^ 2 := by ring
      _ ≤
          2 * E * Real.log z / L +
            8 * E * Real.log z * G / L ^ 2 +
            4 * B * Real.log z * G / L ^ 2 +
            8 * B * Real.log z * G / L ^ 2 := by
        linarith
      _ =
          2 * E * Real.log z / L +
            (8 * E + 12 * B) * Real.log z * G / L ^ 2 := by
        ring
  have hInvProduct :=
    (one_div_le_one_div_of_le (sieveProduct_pos 1 z)
      (sieveProduct_one_le source.k z))
  have hRInv :
      (sieveProduct source.k z)⁻¹ ≤ E * Real.log z + B₀ := by
    rw [inv_eq_one_div]
    calc
      1 / sieveProduct source.k z ≤ 1 / sieveProduct 1 z := hInvProduct
      _ ≤ E * Real.log z + B₀ := by
        dsimp [E]
        simpa only [inv_eq_one_div] using hInvProductOne z hzOne
  have hRPay :
      1 ≤ sieveProduct source.k z *
          (E + 2 * B₀) * Real.log z * G := by
    have hInvOne :
        1 ≤ sieveProduct source.k z * (E * Real.log z + B₀) := by
      simpa [mul_comm] using
        (inv_le_iff_one_le_mul₀ (sieveProduct_pos source.k z)).mp hRInv
    have hAbsorb :
        E * Real.log z + B₀ ≤ (E + 2 * B₀) * Real.log z * G := by
      have hLogZHalf : 1 / 2 ≤ Real.log z := by
        linarith
      have hEG :
          E * Real.log z ≤ E * Real.log z * G :=
        by
          simpa only [mul_one] using
            mul_le_mul_of_nonneg_left hG
              (mul_nonneg hE.le hLogZ.le)
      have hTwoZG : 1 ≤ 2 * Real.log z * G := by
        calc
          1 ≤ 2 * Real.log z := by linarith
          _ ≤ 2 * Real.log z * G :=
            by
              simpa only [mul_one] using
                mul_le_mul_of_nonneg_left hG
                  (show 0 ≤ 2 * Real.log z by positivity)
      have hBG : B₀ ≤ 2 * B₀ * Real.log z * G := by
        nlinarith [mul_le_mul_of_nonneg_left hTwoZG hB₀.le]
      nlinarith
    simpa [mul_assoc] using hInvOne.trans
      (mul_le_mul_of_nonneg_left hAbsorb
        (sieveProduct_pos source.k z).le)
  have hXiSq :
      xi ^ 2 ≤
        source.y * sieveProduct source.k z *
          ((E + 2 * B₀) * Real.log z * G / L ^ 2) := by
    have hXiSqEq :
        xi ^ 2 = source.y / (1 + L ^ 2) := by
      simpa [xi, L] using threeNineCutoff_sq hy0.le
    have hDen :
        source.y / (1 + L ^ 2) ≤ source.y / L ^ 2 := by
      exact div_le_div_of_nonneg_left hy0.le (sq_pos_of_pos hL)
        (by linarith : L ^ 2 ≤ 1 + L ^ 2)
    rw [hXiSqEq]
    calc
      source.y / (1 + L ^ 2) ≤ source.y / L ^ 2 := hDen
      _ ≤ source.y *
          (sieveProduct source.k z *
            ((E + 2 * B₀) * Real.log z * G)) / L ^ 2 := by
        exact
          div_le_div_of_nonneg_right
            (by
              simpa [mul_assoc] using
                mul_le_mul_of_nonneg_left hRPay hy0.le)
            (sq_nonneg L)
      _ = source.y * sieveProduct source.k z *
          ((E + 2 * B₀) * Real.log z * G / L ^ 2) := by ring
  have hScaledCoefficient :
      source.y * sieveProduct source.k z *
          ((E * Real.log z + B) / Real.log xi) ≤
        source.y * sieveProduct source.k z *
          (2 * E * Real.log z / L +
            (8 * E + 12 * B) * Real.log z * G / L ^ 2) :=
    mul_le_mul_of_nonneg_left hCoefficient
      (mul_nonneg hy0.le (sieveProduct_pos source.k z).le)
  calc
    siftedCount source.carrier source.k z ≤
        source.y * sieveProduct source.k z *
            ((E * Real.log z + B) / Real.log xi) + xi ^ 2 := by
      simpa [E, xi] using hBase
    _ ≤ source.y * sieveProduct source.k z *
          (2 * E * Real.log z / L +
            (8 * E + 12 * B) * Real.log z * G / L ^ 2) +
          source.y * sieveProduct source.k z *
            ((E + 2 * B₀) * Real.log z * G / L ^ 2) :=
      add_le_add hScaledCoefficient hXiSq
    _ = source.y * sieveProduct source.k z *
          (2 * E * Real.log z / L +
            c₁ * Real.log z * G / L ^ 2) := by
      dsimp [c₁]
      ring
    _ = source.y * sieveProduct source.k z *
          (2 * Real.exp Real.eulerMascheroniConstant * Real.log z /
              Real.log source.y +
            c₁ * Real.log z * Real.log (Real.log (3 * source.y)) /
              Real.log source.y ^ 2) := by
      rfl

/-- The source corollary `(3.9)` with one absolute constant.  The large range
uses the paper's literal optimized cutoff; the complementary bounded range is
absorbed symbolically from `H_k(M)` at `d = 1` and the same Mertens inversion,
without enumerating any values of `y` or `z`. -/
theorem RegularSource.exists_siftedCount_le_threeNine :
    ∃ c₁ > 0, ∀ (source : RegularSource) {z : ℝ},
      Real.sqrt source.y ≤ z →
      siftedCount source.carrier source.k z ≤
        source.y * sieveProduct source.k z *
          (2 * Real.exp Real.eulerMascheroniConstant * Real.log z /
              Real.log source.y +
            c₁ * Real.log z * Real.log (Real.log (3 * source.y)) /
              Real.log source.y ^ 2) := by
  obtain ⟨C, hC, hLarge⟩ :=
    RegularSource.exists_siftedCount_le_threeNine_of_log_ge
  obtain ⟨B, hB, hInvProductOne⟩ :=
    exists_sieveProduct_one_inv_le_exp_mul_log_add
  let E := Real.exp Real.eulerMascheroniConstant
  let G₀ := Real.log (Real.log 3)
  let c₁ := C + (8192 * E + 256 * B) / G₀
  have hE : 0 < E := by
    dsimp [E]
    positivity
  have hExpOneThree : Real.exp 1 < (3 : ℝ) := by
    nlinarith [Real.exp_one_lt_d9]
  have hLogThree : 1 < Real.log (3 : ℝ) :=
    (Real.lt_log_iff_exp_lt (by norm_num)).2 hExpOneThree
  have hG₀ : 0 < G₀ := by
    dsimp [G₀]
    exact Real.log_pos hLogThree
  refine ⟨c₁, by dsimp [c₁]; positivity, fun source z hz => ?_⟩
  let L := Real.log source.y
  let G := Real.log (Real.log (3 * source.y))
  have hy : 1 < source.y := source.one_lt_y
  have hy0 : 0 < source.y := zero_lt_one.trans hy
  have hL : 0 < L := by
    dsimp [L]
    exact Real.log_pos hy
  have hsqrtPos : 0 < Real.sqrt source.y := Real.sqrt_pos.2 hy0
  have hzPos : 0 < z := hsqrtPos.trans_le hz
  have hzOne : 1 < z := by
    have hsqrtOne : 1 < Real.sqrt source.y := by
      rw [Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 1)]
      simpa using hy
    exact hsqrtOne.trans_le hz
  have hLogZ : 0 < Real.log z := Real.log_pos hzOne
  have hZ : L / 2 ≤ Real.log z := by
    calc
      L / 2 = Real.log (Real.sqrt source.y) := by
        dsimp [L]
        rw [Real.log_sqrt hy0.le]
      _ ≤ Real.log z :=
        Real.strictMonoOn_log.monotoneOn hsqrtPos hzPos hz
  have hG₀G : G₀ ≤ G := by
    have hThreeLe : (3 : ℝ) ≤ 3 * source.y := by nlinarith
    have hLogThreePos : 0 < Real.log (3 : ℝ) := zero_lt_one.trans hLogThree
    have hLogTargetPos : 0 < Real.log (3 * source.y) :=
      Real.log_pos (by nlinarith)
    dsimp [G₀, G]
    exact Real.strictMonoOn_log.monotoneOn hLogThreePos hLogTargetPos
      (Real.strictMonoOn_log.monotoneOn (by norm_num)
        (mul_pos (by norm_num) hy0) hThreeLe)
  have hG : 0 < G := hG₀.trans_le hG₀G
  by_cases hyLarge : 64 ≤ L
  · have hBound := hLarge source (by simpa [L] using hyLarge) hz
    have hCle : C ≤ c₁ := by
      dsimp [c₁]
      have : 0 ≤ (8192 * E + 256 * B) / G₀ := by positivity
      linarith
    have hErrorNonneg :
        0 ≤ Real.log z * G / L ^ 2 := by positivity
    have hError :
        C * Real.log z * G / L ^ 2 ≤
          c₁ * Real.log z * G / L ^ 2 := by
      calc
        C * Real.log z * G / L ^ 2 =
            C * (Real.log z * G / L ^ 2) := by ring
        _ ≤ c₁ * (Real.log z * G / L ^ 2) :=
          mul_le_mul_of_nonneg_right hCle hErrorNonneg
        _ = c₁ * Real.log z * G / L ^ 2 := by ring
    have hBracket :
        2 * E * Real.log z / L +
            C * Real.log z * G / L ^ 2 ≤
          2 * E * Real.log z / L +
            c₁ * Real.log z * G / L ^ 2 :=
      add_le_add le_rfl hError
    calc
      siftedCount source.carrier source.k z ≤
          source.y * sieveProduct source.k z *
            (2 * E * Real.log z / L +
              C * Real.log z * G / L ^ 2) := by
        simpa [E, L, G] using hBound
      _ ≤ source.y * sieveProduct source.k z *
            (2 * E * Real.log z / L +
              c₁ * Real.log z * G / L ^ 2) :=
        mul_le_mul_of_nonneg_left hBracket
          (mul_nonneg hy0.le (sieveProduct_pos source.k z).le)
      _ = source.y * sieveProduct source.k z *
          (2 * Real.exp Real.eulerMascheroniConstant * Real.log z /
              Real.log source.y +
            c₁ * Real.log z * Real.log (Real.log (3 * source.y)) /
              Real.log source.y ^ 2) := by
        rfl
  · have hySmall : L < 64 := lt_of_not_ge hyLarge
    have hInvProduct :=
      one_div_le_one_div_of_le (sieveProduct_pos 1 z)
        (sieveProduct_one_le source.k z)
    have hRInv :
        (sieveProduct source.k z)⁻¹ ≤ E * Real.log z + B := by
      rw [inv_eq_one_div]
      calc
        1 / sieveProduct source.k z ≤ 1 / sieveProduct 1 z := hInvProduct
        _ ≤ E * Real.log z + B := by
          dsimp [E]
          simpa only [inv_eq_one_div] using hInvProductOne z hzOne
    have hInvOne :
        1 ≤ sieveProduct source.k z * (E * Real.log z + B) := by
      simpa [mul_comm] using
        (inv_le_iff_one_le_mul₀ (sieveProduct_pos source.k z)).mp hRInv
    have hLsqConst : 2 * L ^ 2 ≤ 8192 := by
      nlinarith [sq_nonneg (L - 64)]
    have hMainBeforeG :
        2 * L ^ 2 * (E * Real.log z) ≤
          8192 * E * Real.log z :=
      by
        simpa only [mul_assoc] using
          mul_le_mul_of_nonneg_right hLsqConst
            (mul_nonneg hE.le hLogZ.le)
    have hMain :
        2 * L ^ 2 * (E * Real.log z) ≤
          8192 * E * Real.log z :=
      hMainBeforeG
    have hLsqLinear : 2 * L ^ 2 ≤ 128 * L := by
      nlinarith
    have hBLinear :
        2 * L ^ 2 * B ≤ 128 * L * B :=
      mul_le_mul_of_nonneg_right hLsqLinear hB.le
    have hLZ : 128 * L ≤ 256 * Real.log z := by
      linarith
    have hBBeforeG :
        2 * L ^ 2 * B ≤ 256 * B * Real.log z := by
      calc
        2 * L ^ 2 * B ≤ 128 * L * B := hBLinear
        _ ≤ 256 * Real.log z * B :=
          mul_le_mul_of_nonneg_right hLZ hB.le
        _ = 256 * B * Real.log z := by ring
    have hBTerm :
        2 * L ^ 2 * B ≤ 256 * B * Real.log z :=
      hBBeforeG
    have hNumerator :
        2 * L ^ 2 * (E * Real.log z + B) ≤
          (8192 * E + 256 * B) * Real.log z := by
      calc
        2 * L ^ 2 * (E * Real.log z + B) =
            2 * L ^ 2 * (E * Real.log z) + 2 * L ^ 2 * B := by ring
        _ ≤ 8192 * E * Real.log z + 256 * B * Real.log z :=
          add_le_add hMain hBTerm
        _ = (8192 * E + 256 * B) * Real.log z := by ring
    have hCoefficient :
        2 * L ^ 2 * (E * Real.log z + B) ≤
          c₁ * Real.log z * G := by
      calc
        2 * L ^ 2 * (E * Real.log z + B) ≤
            (8192 * E + 256 * B) * Real.log z := hNumerator
        _ = ((8192 * E + 256 * B) / G₀) * Real.log z * G₀ := by
          field_simp [hG₀.ne']
        _ ≤ ((8192 * E + 256 * B) / G₀) * Real.log z * G := by
          exact mul_le_mul_of_nonneg_left hG₀G
            (mul_nonneg (div_nonneg (by positivity) hG₀.le) hLogZ.le)
        _ ≤ c₁ * Real.log z * G := by
          have hc :
              (8192 * E + 256 * B) / G₀ ≤ c₁ := by
            dsimp [c₁]
            linarith
          exact
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hc hLogZ.le) hG.le
    have hPay :
        2 * L ^ 2 ≤
          sieveProduct source.k z * c₁ * Real.log z * G := by
      calc
        2 * L ^ 2 ≤
            2 * L ^ 2 *
              (sieveProduct source.k z * (E * Real.log z + B)) :=
          by
            simpa only [mul_one] using
              mul_le_mul_of_nonneg_left hInvOne
                (show 0 ≤ 2 * L ^ 2 by positivity)
        _ = sieveProduct source.k z *
              (2 * L ^ 2 * (E * Real.log z + B)) := by ring
        _ ≤ sieveProduct source.k z * (c₁ * Real.log z * G) :=
          mul_le_mul_of_nonneg_left hCoefficient
            (sieveProduct_pos source.k z).le
        _ = sieveProduct source.k z * c₁ * Real.log z * G := by ring
    have hTwo :
        2 ≤ sieveProduct source.k z * c₁ * Real.log z * G / L ^ 2 := by
      exact (le_div_iff₀ (sq_pos_of_pos hL)).2 (by simpa using hPay)
    have hCard : source.y + 1 ≤ 2 * source.y := by linarith
    have hCount :
        siftedCount source.carrier source.k z ≤ 2 * source.y :=
      (source.siftedCount_le_y_add_one z).trans hCard
    have hBounded :
        2 * source.y ≤
          source.y *
            (sieveProduct source.k z * c₁ * Real.log z * G / L ^ 2) :=
      by
        simpa only [mul_comm] using
          mul_le_mul_of_nonneg_left hTwo hy0.le
    have hLeading : 0 ≤ 2 * E * Real.log z / L := by positivity
    calc
      siftedCount source.carrier source.k z ≤ 2 * source.y := hCount
      _ ≤ source.y *
          (sieveProduct source.k z * c₁ * Real.log z * G / L ^ 2) :=
        hBounded
      _ = source.y * sieveProduct source.k z *
          (c₁ * Real.log z * G / L ^ 2) := by ring
      _ ≤ source.y * sieveProduct source.k z *
          (2 * E * Real.log z / L +
            c₁ * Real.log z * G / L ^ 2) :=
        mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hLeading)
          (mul_nonneg hy0.le (sieveProduct_pos source.k z).le)
      _ = source.y * sieveProduct source.k z *
          (2 * Real.exp Real.eulerMascheroniConstant * Real.log z /
              Real.log source.y +
            c₁ * Real.log z * Real.log (Real.log (3 * source.y)) /
              Real.log source.y ^ 2) := by
        rfl

/-- Exact one-prime identity for the adapted finite Rosser coefficient at
`1 / p`.  Its correspondence with the concrete source-count identity `(2.2)`
is still to be proved. -/
theorem densitySum_insert
    (D q : ℕ) (P : Finset ℕ) (hq : q ∉ P) :
    LinearSieve.upperRosserSetDensitySum localDensity D (insert q P) =
      ∑ s ∈ P.powerset,
        (LinearSieve.upperRosserSetWeight D s +
            localDensity q *
              LinearSieve.upperRosserSetWeight D (insert q s)) *
          ∏ p ∈ s, localDensity p :=
  LinearSieve.upperRosserSetDensitySum_insert localDensity D q P hq

/-- The adapted finite-depth coefficient recursion obtained by removing two
boundary primes.  No infinite-depth limit or source-count correspondence is
asserted. -/
theorem fixedDepthRelativeDensity_succ
    {D q : ℕ} {P : Finset ℕ}
    (hqs : q ∉ P) (hqprime : q.Prime)
    (hprime : ∀ p ∈ P, p.Prime) (hqmin : ∀ p ∈ P, q ≤ p)
    (r : ℕ) :
    LinearSieve.upperRosserBoundaryChainsFixedDepthRelativeDensity
          localDensity D q P (r + 1) =
      ∑ p₀ ∈ P,
        ∑ p₁ ∈ P.filter (fun p₁ => p₁ < p₀ ∧ p₀ ^ 3 < D),
          LinearSieve.upperRosserBoundaryRelativePairTransition
              localDensity P p₀ p₁ *
            LinearSieve.upperRosserBoundaryChainsFixedDepthRelativeDensity
              localDensity (D ⌈/⌉ (p₀ * p₁)) q
                (P.filter fun p => p < p₁) r := by
  apply LinearSieve.upperRosserBoundaryChainsFixedDepthRelativeDensity_succ
    localDensity hqs hqprime hprime hqmin
  intro p hp
  exact one_sub_localDensity_ne_zero (hprime p hp)

/-- Exact normalized finite boundary expansion for the adapted coefficient
model at `gamma(p) = 1`.  It is finite, but is not yet the paper's concrete
Theorem 1 expansion of `siftedCount`. -/
theorem densityRatio_eq_finiteBoundaryDepths
    {D : ℕ} (P : Finset ℕ) (hD : 1 < D)
    (hprime : ∀ p ∈ P, p.Prime) (hpD : ∀ p ∈ P, p < D) :
    LinearSieve.upperRosserSetDensitySum localDensity D P /
          ∏ p ∈ P, (1 - localDensity p) =
      1 + ∑ q ∈ P,
        (localDensity q / (1 - localDensity q)) *
          ∑ r ∈ Finset.range ((P.filter fun p => q < p).card + 1),
            LinearSieve.upperRosserBoundaryChainsFixedDepthRelativeDensity
              localDensity D q (P.filter fun p => q < p) r := by
  exact
    LinearSieve.upperRosserSetDensityRatio_eq_one_add_sum_relativeBoundaryDepths
      localDensity P hD hprime hpD
        (fun p hp => one_sub_localDensity_ne_zero (hprime p hp))

/-- The sign `(-1)^i`, kept as a real number for the finite comparison. -/
def alternatingSign (i : ℕ) : ℝ := if Even i then 1 else -1

/-- A finite alternating sum over an explicitly supplied carrier. -/
def alternatingSum (I : Finset ℕ) (a : ℕ → ℝ) : ℝ :=
  ∑ i ∈ I, alternatingSign i * a i

/-- The four finite pieces common to Jurkat--Richert Theorems 1 and 4:
the initial term, the depths `1 ≤ i < r`, the depth-`r` terminal term, and the
boundary depths `1 ≤ i ≤ r`. -/
def finiteExpansion
    (r : ℕ) (initial : ℝ) (interior : ℕ → ℝ)
    (terminal : ℝ) (boundary : ℕ → ℝ) : ℝ :=
  initial +
    alternatingSum (Finset.Ico 1 r) interior +
    alternatingSign r * terminal +
    alternatingSum (Finset.Icc 1 r) boundary

theorem alternatingSum_sub
    (I : Finset ℕ) (a b : ℕ → ℝ) (y : ℝ) :
    alternatingSum I (fun i => a i - y * b i) =
      alternatingSum I a - y * alternatingSum I b := by
  unfold alternatingSum
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- Algebraic term-by-term subtraction for two finite expansions with the
source shape. `ChenFiniteDiscrepancy` applies the concrete Theorems 1 and 4,
including Theorem 4's uniform remainder. -/
theorem finiteExpansion_comparison
    (r : ℕ) (y : ℝ)
    (aInitial bInitial : ℝ)
    (aInterior bInterior : ℕ → ℝ)
    (aTerminal bTerminal : ℝ)
    (aBoundary bBoundary : ℕ → ℝ) :
    finiteExpansion r aInitial aInterior aTerminal aBoundary -
        y * finiteExpansion r bInitial bInterior bTerminal bBoundary =
      finiteExpansion r (aInitial - y * bInitial)
        (fun i => aInterior i - y * bInterior i)
        (aTerminal - y * bTerminal)
        (fun i => aBoundary i - y * bBoundary i) := by
  unfold finiteExpansion
  rw [alternatingSum_sub, alternatingSum_sub]
  ring

/-- The signed version of `finiteExpansion_comparison`, with the outer parity
sign used on page 230. `ChenFiniteDiscrepancy` supplies the two concrete
source expansions. -/
theorem signed_finiteExpansion_comparison
    (nu r : ℕ) (y count model : ℝ)
    (aInitial bInitial : ℝ)
    (aInterior bInterior : ℕ → ℝ)
    (aTerminal bTerminal : ℝ)
    (aBoundary bBoundary : ℕ → ℝ)
    (hcount :
      count = finiteExpansion r aInitial aInterior aTerminal aBoundary)
    (hmodel :
      model = finiteExpansion r bInitial bInterior bTerminal bBoundary) :
    alternatingSign nu * (count - y * model) =
      alternatingSign nu *
        finiteExpansion r (aInitial - y * bInitial)
          (fun i => aInterior i - y * bInterior i)
          (aTerminal - y * bTerminal)
          (fun i => aBoundary i - y * bBoundary i) := by
  rw [hcount, hmodel, finiteExpansion_comparison]

/-- The one-step factor produced by the 1965 Lemma 5.2 iteration. -/
noncomputable def terminalTheta (epsilon : ℝ) : ℝ :=
  Real.exp 1 / 3 * (1 + epsilon)

theorem terminalTheta_nonneg {epsilon : ℝ} (hepsilon : 0 ≤ epsilon) :
    0 ≤ terminalTheta epsilon := by
  unfold terminalTheta
  positivity

/-- Once the source error in Lemma 5.2 is at most `10⁻⁴`, its factor is at
most `0.907`.  This preserves the small numerical margin needed beyond the
critical exponent `5/21`. -/
theorem terminalTheta_le_nineHundredSevenThousandths
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon) (hepsilonSmall : epsilon ≤ 1 / 10000) :
    terminalTheta epsilon ≤ 907 / 1000 := by
  unfold terminalTheta
  nlinarith [Real.exp_one_lt_d9]

/-- Finite repeated elimination of terminal sums.  This is the induction
actually used after Lemma 5.2; it does not construct an infinite chain. -/
theorem terminal_le_theta_pow
    (terminal : ℕ → ℝ) (theta : ℝ)
    (htheta : 0 ≤ theta)
    (hstep : ∀ r : ℕ, terminal (r + 1) ≤ theta * terminal r) :
    ∀ r : ℕ, terminal r ≤ theta ^ r * terminal 0 := by
  intro r
  induction r with
  | zero => simp
  | succ r ih =>
      calc
        terminal (r + 1) ≤ theta * terminal r := hstep r
        _ ≤ theta * (theta ^ r * terminal 0) :=
          mul_le_mul_of_nonneg_left ih htheta
        _ = theta ^ (r + 1) * terminal 0 := by rw [pow_succ]; ring

/-- A strict-margin rational block inequality for the terminal exponent:
`0.907^50 ≤ (2/3)^12`.  Here `12/50 > 5/21`, leaving room to absorb the
log-log factor introduced by the source depth choice `(6.3)`. -/
theorem nineHundredSevenThousandths_pow_fifty :
    (907 / 1000 : ℝ) ^ 50 ≤ (2 / 3 : ℝ) ^ 12 := by
  norm_num

/-- Lemma 5.2's finite iteration contracts every block of 50 eliminations by
at least `(2/3)^12`, once its explicit source error is at most `10⁻⁴`. -/
theorem terminalTheta_pow_fifty_mul_le
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon)
    (hepsilonSmall : epsilon ≤ 1 / 10000) (m : ℕ) :
    terminalTheta epsilon ^ (50 * m) ≤ (2 / 3 : ℝ) ^ (12 * m) := by
  have htheta :=
    terminalTheta_le_nineHundredSevenThousandths hepsilon hepsilonSmall
  have hpow :
      terminalTheta epsilon ^ 50 ≤ (907 / 1000 : ℝ) ^ 50 :=
    pow_le_pow_left₀ (terminalTheta_nonneg hepsilon) htheta 50
  calc
    terminalTheta epsilon ^ (50 * m) =
        (terminalTheta epsilon ^ 50) ^ m := by rw [pow_mul]
    _ ≤ ((907 / 1000 : ℝ) ^ 50) ^ m :=
      pow_le_pow_left₀ (pow_nonneg (terminalTheta_nonneg hepsilon) 50) hpow m
    _ ≤ ((2 / 3 : ℝ) ^ 12) ^ m :=
      pow_le_pow_left₀ (by positivity)
        nineHundredSevenThousandths_pow_fifty m
    _ = (2 / 3 : ℝ) ^ (12 * m) := by rw [pow_mul]

/-- The strict block estimate applies to every finite depth, with the final
incomplete block retained through `r / 50`. -/
theorem terminalTheta_pow_le_block
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon)
    (hepsilonSmall : epsilon ≤ 1 / 10000) (r : ℕ) :
    terminalTheta epsilon ^ r ≤
      (2 / 3 : ℝ) ^ (12 * (r / 50)) := by
  have htheta :=
    terminalTheta_le_nineHundredSevenThousandths hepsilon hepsilonSmall
  have hthetaOne : terminalTheta epsilon ≤ 1 := htheta.trans (by norm_num)
  have hdepth : 50 * (r / 50) ≤ r := by omega
  calc
    terminalTheta epsilon ^ r ≤
        terminalTheta epsilon ^ (50 * (r / 50)) :=
      pow_le_pow_of_le_one (terminalTheta_nonneg hepsilon) hthetaOne hdepth
    _ ≤ (2 / 3 : ℝ) ^ (12 * (r / 50)) :=
      terminalTheta_pow_fifty_mul_le hepsilon hepsilonSmall (r / 50)

/-- Direct finite terminal-sum consumer at the arbitrary parity-compatible
depth selected by `(6.3)`.  Converting this strict block exponent to the final
logarithmic bound is a separate analytic step. -/
theorem terminal_le_strict_block
    (terminal : ℕ → ℝ) {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon) (hepsilonSmall : epsilon ≤ 1 / 10000)
    (hterminalZero : 0 ≤ terminal 0)
    (hstep :
      ∀ r : ℕ, terminal (r + 1) ≤ terminalTheta epsilon * terminal r)
    (r : ℕ) :
    terminal r ≤
      (2 / 3 : ℝ) ^ (12 * (r / 50)) * terminal 0 := by
  calc
    terminal r ≤ terminalTheta epsilon ^ r * terminal 0 :=
      terminal_le_theta_pow terminal (terminalTheta epsilon)
        (terminalTheta_nonneg hepsilon) hstep r
    _ ≤ (2 / 3 : ℝ) ^ (12 * (r / 50)) * terminal 0 :=
      mul_le_mul_of_nonneg_right
        (terminalTheta_pow_le_block hepsilon hepsilonSmall r)
        hterminalZero

#print axioms sieveProduct_eq_one_sub_sum
#print axioms sieveProduct_one_eq_mertensPrimeProduct
#print axioms exists_sieveProduct_one_mertens_bound
#print axioms exists_sieveProduct_one_inv_le_log_div_add
#print axioms exists_sieveProduct_one_inv_le_exp_mul_log_add
#print axioms siftingPrimes_union_excluded
#print axioms excludedSiftingFactor_primeFactors
#print axioms prod_one_sub_localDensity_eq_totient_div_prod
#print axioms sum_reciprocal_of_radical_eq_le
#print axioms siftingPrimes_excludedSiftingFactor
#print axioms sieveProduct_one_eq_mul_excludedFactor
#print axioms siftedCount_eq_card_sub_conditioned_sum
#print axioms siftedCount_eq_siftedCount_sub_interval
#print axioms siftedCount_theoremOne_depthOne
#print axioms conditionedCarrier_eq_filter_prod_of_interiorChain
#print axioms chainSiftedCount_eq_at_z₁_sub_extensions
#print axioms chainSiftedCount_eq_recursiveExpansion
#print axioms siftedCount_eq_theoremOneRecursiveExpansion
#print axioms theoremOneRecursiveExpansion_eq_alternatingDepthSums
#print axioms siftedCount_eq_theoremOneFourSums
#print axioms mem_literalQuotientCarrier
#print axioms literalQuotientCarrier_bijOn
#print axioms card_literalQuotientCarrier
#print axioms RegularSource.literalQuotient
#print axioms siftedCount_literalQuotientCarrier_eq_divisibilityFiber
#print axioms RegularSource.boundingSieve_nu_apply
#print axioms RegularSource.boundingSieve_siftedSum_eq
#print axioms RegularSource.boundingSieve_sieveProduct_eq
#print axioms RegularSource.boundingSieve_selbergTerm_prime
#print axioms RegularSource.boundingSieve_selbergTerm_of_dvd
#print axioms coprime_of_dvd_siftingPrimes_prod
#print axioms siftingPrimes_mul_eq_sdiff_primeFactors
#print axioms siftingPrimes_mul_prod_mul
#print axioms RegularSource.abs_boundingSieve_rem_le_one_of_dvd
#print axioms RegularSource.boundingSieve_errSum_le
#print axioms RegularSource.exists_siftedCount_le_selberg
#print axioms selbergReciprocalTotientCarrier_map_mul
#print axioms sum_selbergReciprocalTotientCarrier_if_dvd
#print axioms moebius_mul_moebius_div_totient_of_dvd
#print axioms reciprocalTotientSum_coprime_mul_decomposition
#print axioms sum_reciprocalTotient_divisors_eq
#print axioms selbergReciprocalTotientSum_eq_divisorPackets
#print axioms mul_selbergReciprocalTotientSum_le
#print axioms selbergReciprocalTotientSum_one_le_excludedFactor
#print axioms sieveProduct_one_mul_selbergReciprocalTotientSum_le
#print axioms hasSum_selbergSmoothReciprocal
#print axioms mem_selbergPsiCarrier_iff_factoredNumbers
#print axioms siftingPrimes_one_eq_primesBelow
#print axioms selbergPsiCarrier_eq_smoothNumbersUpTo
#print axioms selbergPsiCarrier_mono
#print axioms selbergPsi_mono
#print axioms selbergPsiCarrier_card_le_pow_primeCounting_mul_sqrt
#print axioms hasSum_selbergSmoothRpow
#print axioms selbergSmoothRpowSum_eq_sum_range_indicator
#print axioms selbergSmoothRpowSum_le_eulerProduct
#print axioms selbergPsi_le_rpow_mul_smoothRpowSum
#print axioms selbergPsi_le_rpow_mul_eulerProduct
#print axioms selbergSmoothReciprocalSum_eq_sum_range_indicator
#print axioms selbergSmoothReciprocalSum_sub_eq_psi_div_add_integral
#print axioms tendsto_selbergSmoothReciprocalSum
#print axioms exists_selbergSmoothReciprocalSum_tail_lt
#print axioms selbergSmoothReciprocalSum_le
#print axioms sieveProduct_one_mul_selbergSmoothReciprocalSum_le
#print axioms selbergMoebiusPacket_eq
#print axioms RegularSource.levelSelbergDenominator_eq_reciprocalTotientSum
#print axioms RegularSource.levelSelbergWeight_eq_printed
#print axioms RegularSource.levelSelbergDenominator_pos
#print axioms RegularSource.levelSelbergWeight_one
#print axioms RegularSource.levelSelbergWeight_support
#print axioms RegularSource.levelSelbergWeight_eq_zero_of_not_support
#print axioms RegularSource.abs_levelSelbergWeight_le_one
#print axioms selbergReciprocalTotientCarrier_subset_psiCarrier
#print axioms RegularSource.sum_abs_levelSelbergWeight_le_psi
#print axioms RegularSource.levelSelbergLambdaSquared_mass_le_psi_sq
#print axioms RegularSource.levelSelbergLambdaSquared_support
#print axioms RegularSource.siftedCount_le_levelSelberg
#print axioms RegularSource.siftedCount_le_levelSelberg_psi
#print axioms RegularSource.siftedCount_le_moebius_divisorError
#print axioms sieveProduct_exp_two_le_of_log_le_two
#print axioms RegularSource.exists_siftedCount_le_moebius_boundedZ
#print axioms selbergRealReciprocalTotientCarrier_eq_floor
#print axioms selbergRealReciprocalTotientSum_eq_floor
#print axioms selbergRealReciprocalTotientSum_eq_divisorPackets
#print axioms mul_selbergRealReciprocalTotientSum_le
#print axioms sieveProduct_one_mul_selbergRealReciprocalTotientSum_le
#print axioms selbergRealSmoothReciprocalSum_le
#print axioms sieveProduct_one_mul_selbergRealSmoothReciprocalSum_le
#print axioms mem_selbergRealPsiCarrier
#print axioms selbergRealPsi_le_rpow_mul_eulerProduct
#print axioms selbergEulerProduct_le_exp_four_mul
#print axioms sum_inv_siftingPrimes_le_one_add_log
#print axioms sum_siftingPrimes_rpow_one_sub_le
#print axioms vinogradovRankinEulerProduct_le
#print axioms selbergRealPsi_le_vinogradovRankin
#print axioms selbergRealPsi_le_self
#print axioms selbergRealPsi_le_rankin_logSq
#print axioms selbergRealPsi_div_sq_le_rankin_logSq
#print axioms integral_selbergRealPsi_div_sq_le_rankin_logSq
#print axioms selbergSmoothReciprocalSum_sub_le_rankin_logSq
#print axioms sieveProduct_inv_sub_selbergSmoothReciprocalSum_le_rankin_logSq
#print axioms sieveProduct_inv_sub_selbergSmoothReciprocalSum_le_rankin
#print axioms selbergRealPsiCarrier_eq_Icc
#print axioms selbergRealPsi_eq_floor_of_lt
#print axioms selbergRealPsi_sq_le
#print axioms selbergRealSmoothReciprocalSum_eq_harmonic
#print axioms log_le_selbergRealSmoothReciprocalSum
#print axioms selbergRealSmoothReciprocalSum_mono
#print axioms fourOneCutoff_sq
#print axioms log_fourOneCutoff
#print axioms rpow_quarter_le_fourOneCutoff
#print axioms quarter_log_le_fourOneSmoothReciprocalSum
#print axioms RegularSource.realLevelSelbergDenominator_eq
#print axioms RegularSource.realLevelSelbergWeight_eq_printed
#print axioms RegularSource.realLevelSelbergDenominator_pos
#print axioms RegularSource.realLevelSelbergWeight_support
#print axioms RegularSource.realLevelSelbergLambdaSquared_mass_le_psi_sq
#print axioms RegularSource.siftedCount_le_realLevelSelberg_psi
#print axioms RegularSource.siftedCount_le_theoremTwo
#print axioms RegularSource.siftedCount_le_theoremTwo_log
#print axioms RegularSource.exists_siftedCount_le_theoremTwo_mertens
#print axioms sieveProduct_one_le
#print axioms RegularSource.exists_siftedCount_le_rankin_logSq_of_ratio_le
#print axioms RegularSource.exists_siftedCount_le_rankin_logSq_of_ratio_ge
#print axioms RegularSource.exists_siftedCount_le_rankin_logSq
#print axioms RegularSource.siftedCount_le_y_add_one
#print axioms threeNineCutoff_sq
#print axioms RegularSource.exists_siftedCount_le_threeNine_of_log_ge
#print axioms RegularSource.exists_siftedCount_le_threeNine
#print axioms densitySum_insert
#print axioms fixedDepthRelativeDensity_succ
#print axioms densityRatio_eq_finiteBoundaryDepths
#print axioms finiteExpansion_comparison
#print axioms signed_finiteExpansion_comparison
#print axioms terminalTheta_pow_fifty_mul_le
#print axioms terminalTheta_pow_le_block
#print axioms terminal_le_strict_block

end

end MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne
