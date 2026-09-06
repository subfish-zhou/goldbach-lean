import MathlibNt.SieveTheory.Selberg.Liu.LiuSelbergOptimalWeights

/-!
# Arithmetic convolution for Liu's Selberg denominator

This file isolates the exact multiplicative arithmetic underlying the finite
Selberg denominator.
-/

open scoped BigOperators
open scoped ArithmeticFunction.Moebius
open scoped ArithmeticFunction.zeta

namespace MathlibNt.SieveTheory.LiuWeight

open Finset

/-- The squarefree source arithmetic factor, extended by zero at zero and away
from the source primes. -/
noncomputable def liuSelbergArithmetic (N n : ℕ) : ℝ :=
  if n = 0 then 0
  else if Squarefree n ∧ Nat.Coprime n N then
    ∏ p ∈ n.primeFactors, ((p : ℝ) - 2)⁻¹
  else 0

@[simp]
theorem liuSelbergArithmetic_zero (N : ℕ) : liuSelbergArithmetic N 0 = 0 := by
  simp [liuSelbergArithmetic]

@[simp]
theorem liuSelbergArithmetic_one (N : ℕ) : liuSelbergArithmetic N 1 = 1 := by
  simp [liuSelbergArithmetic]

theorem liuSelbergArithmetic_eq_zero_of_not_squarefree_or_not_coprime
    {N n : ℕ} (h : ¬(Squarefree n ∧ Nat.Coprime n N)) :
    liuSelbergArithmetic N n = 0 := by
  simp [liuSelbergArithmetic, h]

theorem liuSelbergArithmetic_eq_prod
    {N n : ℕ} (hn : n ≠ 0) (hs : Squarefree n) (hc : Nat.Coprime n N) :
    liuSelbergArithmetic N n =
      ∏ p ∈ n.primeFactors, ((p : ℝ) - 2)⁻¹ := by
  simp [liuSelbergArithmetic, hn, hs, hc]

/-- A divisor of Liu's squarefree source modulus is exactly a squarefree
integer coprime to `N` (with the cutoff made explicit for the reverse
direction). -/
theorem dvd_liuPaperQModulus_iff_squarefree_coprime
    {N n : ℕ} (hn : n ≤ paperQSourceCutoff N ε) :
    n ∣ liuPaperQModulus N ε ↔ Squarefree n ∧ Nat.Coprime n N := by
  classical
  constructor
  · intro hd
    refine ⟨(liuPaperQModulus_squarefree N ε).squarefree_of_dvd hd, ?_⟩
    have hQN : Nat.Coprime (liuPaperQModulus N ε) N := by
      rw [liuPaperQModulus_eq_paperQStyleModulus]
      unfold paperQStyleModulus
      apply Nat.Coprime.prod_left
      intro p hp
      exact (Finset.mem_filter.mp hp).2.1.coprime_iff_not_dvd.mpr
        (Finset.mem_filter.mp hp).2.2
    exact Nat.Coprime.of_dvd_left hd hQN
  · rintro ⟨hs, hc⟩
    have hQ0 : liuPaperQModulus N ε ≠ 0 :=
      (liuPaperQModulus_squarefree N ε).ne_zero
    have hsub : n.primeFactors ⊆
        (liuPaperQModulus N ε).primeFactors := by
      intro p hp
      have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
      have hpn : ¬p ∣ N := by
        exact (Nat.Prime.coprime_iff_not_dvd hpp).mp
          (Nat.Coprime.of_dvd_left (Nat.dvd_of_mem_primeFactors hp) hc)
      have hple : p ≤ paperQSourceCutoff N ε := by
        exact le_trans (Nat.le_of_dvd (Nat.pos_of_ne_zero
          (Squarefree.ne_zero hs)) (Nat.dvd_of_mem_primeFactors hp)) hn
      have hpQ : p ∣ liuPaperQModulus N ε := by
        rw [liuPaperQModulus_eq_paperQStyleModulus]
        exact (prime_dvd_paperQStyleModulus hpp).mpr ⟨hple, hpn⟩
      exact (Nat.mem_primeFactors_of_ne_zero hQ0).mpr ⟨hpp, hpQ⟩
    rw [← Nat.prod_primeFactors_of_squarefree hs]
    exact (Nat.prod_primeFactors_dvd_iff hQ0).mpr hsub

theorem liuSelbergDenominator_eq_sum_Icc
    {N : ℕ} {epsilon : ℝ} (_hNeven : Even N)
    (_hR : 1 ≤ paperQSourceCutoff N epsilon) :
    liuSelbergDenominator N epsilon =
      ∑ n ∈ Finset.Icc 1 (paperQSourceCutoff N epsilon),
        liuSelbergArithmetic N n := by
  classical
  unfold liuSelbergDenominator
  let C := liuSelbergLambdaSourceCarrier N epsilon
  let I := Finset.Icc 1 (paperQSourceCutoff N epsilon)
  have hCsub : C ⊆ I := by
    intro n hn
    rw [mem_liuSelbergLambdaSourceCarrier] at hn
    have hn0 : n ≠ 0 := by
      intro hn0
      apply (liuPaperQModulus_squarefree N epsilon).ne_zero
      exact zero_dvd_iff.mp (hn0 ▸ hn.1)
    exact Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr hn0, hn.2⟩
  have hterm : ∀ n ∈ C, liuSelbergTerm n = liuSelbergArithmetic N n := by
    intro n hn
    obtain ⟨hd, hcutoff⟩ := mem_liuSelbergLambdaSourceCarrier.mp hn
    obtain ⟨hs, hc⟩ := (dvd_liuPaperQModulus_iff_squarefree_coprime hcutoff).mp hd
    exact (liuSelbergArithmetic_eq_prod hs.ne_zero hs hc).symm
  have hzero : ∀ n ∈ I, n ∉ C → liuSelbergArithmetic N n = 0 := by
    intro n hnI hnC
    apply liuSelbergArithmetic_eq_zero_of_not_squarefree_or_not_coprime
    intro hsc
    have hcutoff := (Finset.mem_Icc.mp hnI).2
    exact hnC (mem_liuSelbergLambdaSourceCarrier.mpr
      ⟨(dvd_liuPaperQModulus_iff_squarefree_coprime hcutoff).mpr hsc, hcutoff⟩)
  calc
    ∑ l ∈ C, liuSelbergTerm l = ∑ l ∈ C, liuSelbergArithmetic N l := by
      apply Finset.sum_congr rfl
      intro l hl
      exact hterm l hl
    _ = ∑ l ∈ I, liuSelbergArithmetic N l := by
      exact Finset.sum_subset hCsub (fun n hnI hnC => hzero n hnI hnC)

noncomputable def liuReciprocal : ArithmeticFunction ℝ :=
  ⟨fun n => if n = 0 then 0 else (n : ℝ)⁻¹, by simp⟩

@[simp]
theorem liuReciprocal_apply (n : ℕ) :
    liuReciprocal n = if n = 0 then 0 else (n : ℝ)⁻¹ := rfl

noncomputable def liuSelbergArithmeticFunction (N : ℕ) : ArithmeticFunction ℝ :=
  ⟨liuSelbergArithmetic N, liuSelbergArithmetic_zero N⟩

@[simp]
theorem liuSelbergArithmeticFunction_apply (N n : ℕ) :
    liuSelbergArithmeticFunction N n = liuSelbergArithmetic N n := rfl

noncomputable def liuMoebiusReciprocal : ArithmeticFunction ℝ :=
  ⟨fun n => if n = 0 then 0 else (μ n : ℝ) / (n : ℝ), by simp⟩

noncomputable def liuSelbergCorrection (N : ℕ) : ArithmeticFunction ℝ :=
  liuMoebiusReciprocal * liuSelbergArithmeticFunction N

theorem liuSelbergCorrection_apply (N n : ℕ) :
    liuSelbergCorrection N n =
      ∑ d ∈ n.divisors, liuMoebiusReciprocal (n / d) *
        liuSelbergArithmeticFunction N d := by
  unfold liuSelbergCorrection
  rw [ArithmeticFunction.mul_apply]
  simpa only [liuSelbergArithmeticFunction_apply] using
    (Nat.sum_divisorsAntidiagonal'
      (fun a b => liuMoebiusReciprocal a * liuSelbergArithmeticFunction N b)
      (n := n))

@[simp]
theorem liuReciprocal_zero : liuReciprocal 0 = 0 := rfl

@[simp]
theorem liuMoebiusReciprocal_zero : liuMoebiusReciprocal 0 = 0 := rfl

@[simp]
theorem liuSelbergCorrection_zero (N : ℕ) : liuSelbergCorrection N 0 = 0 := by
  simp

@[simp]
theorem liuSelbergCorrection_one (N : ℕ) : liuSelbergCorrection N 1 = 1 := by
  rw [liuSelbergCorrection_apply]
  simp [liuMoebiusReciprocal]

theorem liuSelbergArithmeticFunction_isMultiplicative (N : ℕ) :
    (liuSelbergArithmeticFunction N).IsMultiplicative := by
  classical
  refine ⟨liuSelbergArithmetic_one N, ?_⟩
  intro m n hmn
  by_cases hm : m = 0
  · subst m
    simp [liuSelbergArithmetic]
  by_cases hn : n = 0
  · subst n
    simp [liuSelbergArithmetic]
  have hsmn : Squarefree (m * n) ↔ Squarefree m ∧ Squarefree n :=
    Nat.squarefree_mul hmn
  have hcmn : Nat.Coprime (m * n) N ↔
      Nat.Coprime m N ∧ Nat.Coprime n N := by
    constructor
    · intro h
      exact ⟨Nat.Coprime.of_dvd_left (dvd_mul_right m n) h,
        Nat.Coprime.of_dvd_left (dvd_mul_left n m) h⟩
    · rintro ⟨hmN, hnN⟩
      exact hmN.mul_left hnN
  by_cases hsm : Squarefree m ∧ Nat.Coprime m N
  · by_cases hsn : Squarefree n ∧ Nat.Coprime n N
    · change liuSelbergArithmetic N (m * n) =
        liuSelbergArithmetic N m * liuSelbergArithmetic N n
      rw [liuSelbergArithmetic_eq_prod (mul_ne_zero hm hn)
        (hsmn.mpr ⟨hsm.1, hsn.1⟩)
        (hcmn.mpr ⟨hsm.2, hsn.2⟩),
        liuSelbergArithmetic_eq_prod hm hsm.1 hsm.2,
        liuSelbergArithmetic_eq_prod hn hsn.1 hsn.2,
        Nat.Coprime.primeFactors_mul hmn]
      rw [Finset.prod_union hmn.disjoint_primeFactors]
    · have hprod : ¬(Squarefree (m * n) ∧ Nat.Coprime (m * n) N) := by
        intro h
        exact hsn ⟨(hsmn.mp h.1).2, (hcmn.mp h.2).2⟩
      change liuSelbergArithmetic N (m * n) =
        liuSelbergArithmetic N m * liuSelbergArithmetic N n
      simp [liuSelbergArithmetic, hm, hn, hprod, hsn]
  · have hprod : ¬(Squarefree (m * n) ∧ Nat.Coprime (m * n) N) := by
      intro h
      exact hsm ⟨(hsmn.mp h.1).1, (hcmn.mp h.2).1⟩
    change liuSelbergArithmetic N (m * n) =
      liuSelbergArithmetic N m * liuSelbergArithmetic N n
    simp [liuSelbergArithmetic, hm, hn, hprod, hsm]

theorem liuReciprocal_isMultiplicative :
    liuReciprocal.IsMultiplicative := by
  classical
  have h :
      liuReciprocal =
        ArithmeticFunction.pdiv (ArithmeticFunction.zeta : ArithmeticFunction ℝ)
          (ArithmeticFunction.id : ArithmeticFunction ℝ) := by
    ext n
    cases n <;> simp [liuReciprocal, ArithmeticFunction.pdiv_apply]
  rw [h]
  have hid : ((ArithmeticFunction.id : ArithmeticFunction ℕ) :
      ArithmeticFunction ℝ).IsMultiplicative :=
    ArithmeticFunction.isMultiplicative_id.natCast
  exact ArithmeticFunction.IsMultiplicative.pdiv
    ArithmeticFunction.isMultiplicative_zeta.natCast
    hid

theorem liuMoebiusReciprocal_isMultiplicative :
    liuMoebiusReciprocal.IsMultiplicative := by
  classical
  have h :
      liuMoebiusReciprocal =
        ArithmeticFunction.pdiv (μ : ArithmeticFunction ℝ)
          (ArithmeticFunction.id : ArithmeticFunction ℝ) := by
    ext n
    cases n <;> simp [liuMoebiusReciprocal, ArithmeticFunction.pdiv_apply]
  rw [h]
  have hmu : (μ : ArithmeticFunction ℝ).IsMultiplicative :=
    ArithmeticFunction.isMultiplicative_moebius.intCast
  have hid : ((ArithmeticFunction.id : ArithmeticFunction ℕ) :
      ArithmeticFunction ℝ).IsMultiplicative :=
    ArithmeticFunction.isMultiplicative_id.natCast
  exact ArithmeticFunction.IsMultiplicative.pdiv
    hmu hid

theorem liuSelbergCorrection_isMultiplicative (N : ℕ) :
    (liuSelbergCorrection N).IsMultiplicative :=
  liuMoebiusReciprocal_isMultiplicative.mul
    (liuSelbergArithmeticFunction_isMultiplicative N)

private theorem liu_pdiv_mul_pdiv
    (f g : ArithmeticFunction ℝ) :
    ArithmeticFunction.pdiv f (ArithmeticFunction.id : ArithmeticFunction ℝ) *
        ArithmeticFunction.pdiv g (ArithmeticFunction.id : ArithmeticFunction ℝ) =
      ArithmeticFunction.pdiv (f * g) (ArithmeticFunction.id : ArithmeticFunction ℝ) := by
  ext n
  simp only [ArithmeticFunction.mul_apply, ArithmeticFunction.pdiv_apply]
  rw [Finset.sum_div]
  by_cases hn : n = 0
  · subst n
    simp
  · apply Finset.sum_congr rfl
    intro x hx
    obtain ⟨hxy, _⟩ := Nat.mem_divisorsAntidiagonal.mp hx
    have hx0 : x.1 ≠ 0 :=
      Nat.left_ne_zero_of_mem_divisorsAntidiagonal hx
    have hy0 : x.2 ≠ 0 :=
      Nat.right_ne_zero_of_mem_divisorsAntidiagonal hx
    change f x.1 * (x.1 : ℝ)⁻¹ * (g x.2 * (x.2 : ℝ)⁻¹) =
      f x.1 * g x.2 * (n : ℝ)⁻¹
    have hcast : (x.1 : ℝ) * (x.2 : ℝ) = (n : ℝ) := by
      exact_mod_cast hxy
    field_simp [hx0, hy0]
    calc
      f x.1 * g x.2 * (n : ℝ) =
          f x.1 * g x.2 * ((x.1 : ℝ) * (x.2 : ℝ)) := by rw [hcast]
      _ = f x.1 * (x.1 : ℝ) * g x.2 * (x.2 : ℝ) := by ring

theorem liuReciprocal_mul_liuMoebiusReciprocal :
    liuReciprocal * liuMoebiusReciprocal = 1 := by
  have hr :
      liuReciprocal =
        ArithmeticFunction.pdiv (ArithmeticFunction.zeta : ArithmeticFunction ℝ)
          (ArithmeticFunction.id : ArithmeticFunction ℝ) := by
    ext n
    cases n <;> simp [liuReciprocal, ArithmeticFunction.pdiv_apply]
  have hm :
      liuMoebiusReciprocal =
        ArithmeticFunction.pdiv (μ : ArithmeticFunction ℝ)
          (ArithmeticFunction.id : ArithmeticFunction ℝ) := by
    ext n
    cases n <;> simp [liuMoebiusReciprocal, ArithmeticFunction.pdiv_apply]
  rw [hr, hm, liu_pdiv_mul_pdiv,
    ArithmeticFunction.coe_zeta_mul_coe_moebius]
  ext n
  cases n with
  | zero => simp
  | succ n =>
    rcases n with _ | n
    · simp [ArithmeticFunction.pdiv_apply]
    · simp [ArithmeticFunction.pdiv_apply, ArithmeticFunction.id_apply]

theorem liuSelbergArithmeticFunction_eq_convolution :
    ∀ N, liuSelbergArithmeticFunction N =
      liuReciprocal * liuSelbergCorrection N := by
  intro N
  rw [liuSelbergCorrection, ← mul_assoc,
    liuReciprocal_mul_liuMoebiusReciprocal, one_mul]

theorem liuSelbergArithmetic_eq_convolution (N n : ℕ) :
    liuSelbergArithmetic N n =
      (liuReciprocal * liuSelbergCorrection N) n := by
  rw [← liuSelbergArithmeticFunction_apply, liuSelbergArithmeticFunction_eq_convolution]

theorem liuSelbergCorrection_prime_pow_sum
    {N p k : ℕ} (hp : p.Prime) :
    liuSelbergCorrection N (p ^ k) =
      ∑ j ∈ Finset.range (k + 1),
        liuMoebiusReciprocal (p ^ (k - j)) *
          liuSelbergArithmeticFunction N (p ^ j) := by
  rw [liuSelbergCorrection_apply, Nat.sum_divisors_prime_pow hp]
  apply Finset.sum_congr rfl
  intro x hx
  have hle : x ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hx)
  have hdiv : p ^ k / p ^ x = p ^ (k - x) := by
    apply Nat.div_eq_of_eq_mul_left
    · exact pow_pos hp.pos x
    · calc
        p ^ k = p ^ (k - x + x) :=
          congrArg (fun t => p ^ t) (Nat.sub_add_cancel hle).symm
        _ = p ^ (k - x) * p ^ x := by rw [pow_add]
  rw [hdiv]

private theorem liuSelbergArithmeticFunction_prime_pow_one
    {N p : ℕ} (hp : p.Prime) (hpn : ¬p ∣ N) :
    liuSelbergArithmeticFunction N p = ((p : ℝ) - 2)⁻¹ := by
  rw [liuSelbergArithmeticFunction_apply,
    liuSelbergArithmetic_eq_prod hp.ne_zero hp.squarefree
      (hp.coprime_iff_not_dvd.mpr hpn)]
  simp [hp.primeFactors]

private theorem liuSelbergArithmeticFunction_prime_pow_zero
    (N p : ℕ) :
    liuSelbergArithmeticFunction N (p ^ 0) = 1 := by
  simp

private theorem liuSelbergArithmeticFunction_prime_pow_eq_zero
    {N p k : ℕ} (hp : p.Prime) (hk : 2 ≤ k) :
    liuSelbergArithmeticFunction N (p ^ k) = 0 := by
  rw [liuSelbergArithmeticFunction_apply]
  apply liuSelbergArithmetic_eq_zero_of_not_squarefree_or_not_coprime
  intro h
  have hk0 : k ≠ 0 := by omega
  have hsf : ¬Squarefree (p ^ k) := by
    rw [Nat.squarefree_pow_iff hp.ne_one hk0]
    simp [Nat.ne_of_gt hk]
  exact hsf h.1

private theorem liuSelbergArithmeticFunction_prime_pow_eq_zero_of_dvd
    {N p k : ℕ} (hp : p.Prime) (hk : 1 ≤ k) (hpn : p ∣ N) :
    liuSelbergArithmeticFunction N (p ^ k) = 0 := by
  rw [liuSelbergArithmeticFunction_apply]
  apply liuSelbergArithmetic_eq_zero_of_not_squarefree_or_not_coprime
  intro h
  have hcop : Nat.Coprime p N :=
    Nat.Coprime.of_dvd_left (dvd_pow_self p (by omega)) h.2
  exact (hp.coprime_iff_not_dvd.mp hcop) hpn

private theorem liuMoebiusReciprocal_prime_pow_zero
    (p : ℕ) :
    liuMoebiusReciprocal (p ^ 0) = 1 := by
  simp [liuMoebiusReciprocal]

@[simp] theorem liuMoebiusReciprocal_one :
    liuMoebiusReciprocal 1 = 1 := by
  simp [liuMoebiusReciprocal]

private theorem liuMoebiusReciprocal_prime_pow_one
    {p : ℕ} (hp : p.Prime) :
    liuMoebiusReciprocal p = -(p : ℝ)⁻¹ := by
  simp [liuMoebiusReciprocal, hp.ne_zero,
    ArithmeticFunction.moebius_apply_prime hp, div_eq_mul_inv]

private theorem liuMoebiusReciprocal_prime_pow_eq_zero
    {p k : ℕ} (hp : p.Prime) (hk : 2 ≤ k) :
    liuMoebiusReciprocal (p ^ k) = 0 := by
  rw [liuMoebiusReciprocal]
  have hk0 : k ≠ 0 := by omega
  have hk1 : k ≠ 1 := by omega
  simp [ArithmeticFunction.moebius_apply_prime_pow hp hk0, hp.ne_zero, hk0, hk1]

theorem liuSelbergCorrection_prime_of_not_dvd
    {N p : ℕ} (hNeven : Even N) (hp : p.Prime) (hpn : ¬p ∣ N) :
    liuSelbergCorrection N p =
      2 / ((p : ℝ) * ((p : ℝ) - 2)) := by
  have hp2 : p ≠ 2 := by
    intro hp2
    apply hpn
    rw [hp2]
    exact hNeven.two_dvd
  rw [show p = p ^ 1 by simp, liuSelbergCorrection_prime_pow_sum hp]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    pow_zero, pow_one, tsub_self]
  simp only [Nat.one_sub, if_true, pow_one]
  rw [liuMoebiusReciprocal_prime_pow_one hp,
    liuSelbergArithmeticFunction_prime_pow_one hp hpn]
  simp [liuMoebiusReciprocal_one, liuSelbergArithmeticFunction_apply]
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hpR2 : (p : ℝ) - 2 ≠ 0 := by
    apply sub_ne_zero.mpr
    exact_mod_cast hp2
  field_simp [hpR, hpR2]
  ring

theorem liuSelbergCorrection_prime_sq_of_not_dvd
    {N p : ℕ} (hp : p.Prime) (hpn : ¬p ∣ N) :
    liuSelbergCorrection N (p ^ 2) =
      -1 / ((p : ℝ) * ((p : ℝ) - 2)) := by
  rw [liuSelbergCorrection_prime_pow_sum hp]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    pow_zero, pow_one, tsub_self]
  simp only [Nat.reduceSub, pow_one]
  rw [liuMoebiusReciprocal_prime_pow_eq_zero hp (by omega),
    liuMoebiusReciprocal_prime_pow_one hp,
    liuSelbergArithmeticFunction_prime_pow_one hp hpn,
    liuSelbergArithmeticFunction_prime_pow_eq_zero hp (by omega)]
  simp [liuMoebiusReciprocal_one, liuSelbergArithmeticFunction_apply,
    div_eq_mul_inv]
  ring

theorem liuSelbergCorrection_prime_pow_eq_zero_of_not_dvd
    {N p k : ℕ} (hp : p.Prime) (_hpn : ¬p ∣ N) (hk : 3 ≤ k) :
    liuSelbergCorrection N (p ^ k) = 0 := by
  rw [liuSelbergCorrection_prime_pow_sum hp]
  apply Finset.sum_eq_zero
  intro j hj
  by_cases hjle : j ≤ 1
  · have hkj : 2 ≤ k - j := by omega
    rw [liuMoebiusReciprocal_prime_pow_eq_zero hp hkj]
    simp
  · have hj2 : 2 ≤ j := by omega
    rw [liuSelbergArithmeticFunction_prime_pow_eq_zero hp hj2]
    simp

theorem liuSelbergCorrection_prime_of_dvd
    {N p : ℕ} (hp : p.Prime) (hpn : p ∣ N) :
    liuSelbergCorrection N p = -(p : ℝ)⁻¹ := by
  rw [show p = p ^ 1 by simp, liuSelbergCorrection_prime_pow_sum hp]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    pow_zero, pow_one, Nat.one_sub, if_true]
  rw [liuMoebiusReciprocal_prime_pow_one hp]
  have ha : liuSelbergArithmeticFunction N p = 0 :=
    by simpa using
      (liuSelbergArithmeticFunction_prime_pow_eq_zero_of_dvd hp le_rfl hpn)
  simp [ha, liuMoebiusReciprocal_one, liuSelbergArithmeticFunction_apply]

theorem liuSelbergCorrection_prime_pow_eq_zero_of_dvd
    {N p k : ℕ} (hp : p.Prime) (hpn : p ∣ N) (hk : 2 ≤ k) :
    liuSelbergCorrection N (p ^ k) = 0 := by
  rw [liuSelbergCorrection_prime_pow_sum hp]
  apply Finset.sum_eq_zero
  intro j hj
  by_cases hj0 : j = 0
  · subst j
    have hkp : 2 ≤ k - 0 := by simpa using hk
    rw [liuMoebiusReciprocal_prime_pow_eq_zero hp hkp]
    simp
  · have hj1 : 1 ≤ j := Nat.one_le_iff_ne_zero.mpr hj0
    rw [liuSelbergArithmeticFunction_prime_pow_eq_zero_of_dvd hp hj1 hpn]
    simp

/-- The finite harmonic sum, with the empty sum giving its value at zero. -/
noncomputable def liuHarmonic (x : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 x, (m : ℝ)⁻¹

@[simp]
theorem liuHarmonic_zero : liuHarmonic 0 = 0 := by
  simp [liuHarmonic]

theorem liuReciprocal_sum_Ioc (x : ℕ) :
    ∑ m ∈ Finset.Ioc 0 x, liuReciprocal m = liuHarmonic x := by
  have hI : Finset.Ioc 0 x = Finset.Icc 1 x := by
    ext m
    simp only [Finset.mem_Ioc, Finset.mem_Icc]
    omega
  rw [hI]
  simp only [liuHarmonic, liuReciprocal_apply]
  apply Finset.sum_congr rfl
  intro m hm
  simp [Nat.ne_of_gt (Finset.mem_Icc.mp hm).1]

theorem liuSelbergArithmetic_sum_Icc (N x : ℕ) :
    ∑ n ∈ Finset.Icc 1 x, liuSelbergArithmetic N n =
      ∑ d ∈ Finset.Icc 1 x,
        liuSelbergCorrection N d * liuHarmonic (x / d) := by
  have hI : Finset.Ioc 0 x = Finset.Icc 1 x := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_Icc]
    omega
  have hfun :
      liuSelbergArithmeticFunction N =
        liuSelbergCorrection N * liuReciprocal := by
    simpa only [mul_comm] using
      (liuSelbergArithmeticFunction_eq_convolution N)
  calc
    ∑ n ∈ Finset.Icc 1 x, liuSelbergArithmetic N n =
        ∑ n ∈ Finset.Ioc 0 x, liuSelbergArithmeticFunction N n := by
          rw [hI]
          simp only [liuSelbergArithmeticFunction_apply]
    _ = ∑ n ∈ Finset.Ioc 0 x,
        (liuSelbergCorrection N * liuReciprocal) n := by
          apply Finset.sum_congr rfl
          intro n hn
          rw [← hfun]
    _ = ∑ d ∈ Finset.Ioc 0 x, liuSelbergCorrection N d *
        ∑ m ∈ Finset.Ioc 0 (x / d), liuReciprocal m :=
      ArithmeticFunction.sum_Ioc_mul_eq_sum_sum
        (liuSelbergCorrection N) liuReciprocal x
    _ = ∑ d ∈ Finset.Icc 1 x,
        liuSelbergCorrection N d * liuHarmonic (x / d) := by
          rw [hI]
          apply Finset.sum_congr rfl
          intro d hd
          rw [liuReciprocal_sum_Ioc]

end MathlibNt.SieveTheory.LiuWeight
