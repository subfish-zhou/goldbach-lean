import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic

/-!
# Fixed-order divisor means and coefficient square sums

The actual ordered divisor function is the Dirichlet convolution power `ζ ^ k`.
The mean estimate uses only the elementary hyperbola identity and the harmonic
sum bound. The square majorant is unrestricted: no squarefree support is needed.
-/

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

open Finset

/-- The ordered `k`-fold divisor function, with the usual value zero at zero. -/
def fouvryTau (k : ℕ) : ArithmeticFunction ℕ := ArithmeticFunction.zeta ^ k

@[simp] theorem fouvryTau_zero (k : ℕ) : fouvryTau k 0 = 0 :=
  ArithmeticFunction.map_zero

theorem fouvryTau_multiplicative (k : ℕ) : (fouvryTau k).IsMultiplicative :=
  ArithmeticFunction.isMultiplicative_zeta.pow

@[simp] theorem fouvryTau_one (k : ℕ) : fouvryTau k 1 = 1 :=
  (fouvryTau_multiplicative k).map_one

theorem fouvryTau_order_one {n : ℕ} (hn : n ≠ 0) : fouvryTau 1 n = 1 := by
  simp [fouvryTau, ArithmeticFunction.zeta_apply, hn]

theorem fouvryTau_succ (k n : ℕ) :
    fouvryTau (k + 1) n = ∑ d ∈ n.divisors, fouvryTau k d := by
  exact ArithmeticFunction.coe_mul_zeta_apply (f := fouvryTau k)

theorem fouvryTau_two (n : ℕ) : fouvryTau 2 n = n.divisors.card := by
  rw [show 2 = 1 + 1 from rfl, fouvryTau_succ]
  trans ∑ _d ∈ n.divisors, 1
  · exact sum_congr rfl (fun d hd => fouvryTau_order_one (Nat.pos_of_mem_divisors hd).ne')
  · simp

theorem fouvryTau_prime_pow {p : ℕ} (hp : p.Prime) (k a : ℕ) :
    fouvryTau k (p ^ a) = k.multichoose a := by
  induction k generalizing a with
  | zero =>
    cases a with
    | zero => simp
    | succ a =>
      simp [fouvryTau, hp.ne_one]
  | succ k ih =>
    rw [fouvryTau_succ, Nat.sum_divisors_prime_pow hp]
    simp_rw [ih]
    rw [Nat.sum_range_multichoose, Nat.multichoose_eq]
    rw [show k + 1 + a - 1 = a + k by omega]
    exact Nat.choose_symm_of_eq_add (by omega)

private theorem multichoose_step (k a : ℕ) :
    k.multichoose (a + 1) * (a + 1) = k.multichoose a * (k + a) := by
  cases k with
  | zero => cases a <;> simp
  | succ k =>
    simp only [Nat.multichoose_eq]
    rw [show k + 1 + (a + 1) - 1 = k + a + 1 by omega,
      show k + 1 + a - 1 = k + a by omega,
      show k + 1 + a = k + a + 1 by omega]
    exact (Nat.add_one_mul_choose_eq (k + a) a).symm.trans (Nat.mul_comm _ _)

private theorem multichoose_mul_le (k l a : ℕ) :
    k.multichoose a * l.multichoose a ≤ (k * l).multichoose a := by
  cases k with
  | zero => cases a <;> simp
  | succ k =>
    cases l with
    | zero => cases a <;> simp
    | succ l =>
    induction a with
    | zero => simp
    | succ a ih =>
      have hstep := multichoose_step (k + 1) a
      have hstep' := multichoose_step (l + 1) a
      have hstep'' := multichoose_step ((k + 1) * (l + 1)) a
      have hratio : (k + 1 + a) * (l + 1 + a) ≤
          ((k + 1) * (l + 1) + a) * (a + 1) := by
        nlinarith [Nat.zero_le (a * k * l)]
      apply le_of_mul_le_mul_right (a := (a + 1) ^ 2) _ (by positivity)
      calc
        (k + 1).multichoose (a + 1) * (l + 1).multichoose (a + 1) * (a + 1) ^ 2 =
            ((k + 1).multichoose a * (l + 1).multichoose a) *
              ((k + 1 + a) * (l + 1 + a)) := by
              calc
                _ = ((k + 1).multichoose (a + 1) * (a + 1)) *
                    ((l + 1).multichoose (a + 1) * (a + 1)) := by ring
                _ = _ := by rw [hstep, hstep']; ring
        _ ≤ ((k + 1) * (l + 1)).multichoose a *
            (((k + 1) * (l + 1) + a) * (a + 1)) := Nat.mul_le_mul ih hratio
        _ = ((k + 1) * (l + 1)).multichoose (a + 1) * (a + 1) ^ 2 := by
              rw [← mul_assoc, ← hstep'']
              ring
        _ ≤ _ := le_rfl

/-- Products of divisor coefficients are dominated with explicit multiplied
order. This holds without any squarefree restriction. -/
theorem fouvryTau_mul_le (k l n : ℕ) :
    fouvryTau k n * fouvryTau l n ≤ fouvryTau (k * l) n := by
  obtain rfl | hn := eq_or_ne n 0
  · simp
  rw [(fouvryTau_multiplicative k).multiplicative_factorization _ hn,
    (fouvryTau_multiplicative l).multiplicative_factorization _ hn,
    (fouvryTau_multiplicative (k * l)).multiplicative_factorization _ hn]
  simp only [Finsupp.prod, Nat.support_factorization]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_le_prod'
  intro p hp
  simp only [fouvryTau_prime_pow (Nat.prime_of_mem_primeFactors hp)]
  exact multichoose_mul_le _ _ _

/-- The sharp fixed-order square majorant holds for every integer, not merely
for squarefree integers. -/
theorem fouvryTau_sq_le (k n : ℕ) : fouvryTau k n ^ 2 ≤ fouvryTau (k ^ 2) n := by
  simpa only [pow_two] using fouvryTau_mul_le k k n

/-- All integral moments have an explicit divisor-function majorant. The
nonzero hypothesis is needed only for the zeroth moment. -/
theorem fouvryTau_pow_le (k r : ℕ) {n : ℕ} (hn : n ≠ 0) :
    fouvryTau k n ^ r ≤ fouvryTau (k ^ r) n := by
  induction r with
  | zero => simp [fouvryTau_order_one hn]
  | succ r ih =>
    calc
      _ = fouvryTau k n ^ r * fouvryTau k n := pow_succ _ _
      _ ≤ fouvryTau (k ^ r) n * fouvryTau k n := Nat.mul_le_mul_right _ ih
      _ ≤ fouvryTau (k ^ r * k) n := fouvryTau_mul_le _ _ _
      _ = _ := by rw [pow_succ]

/-- A divisor-sum consequence of `∑ d ∣ n, φ(d) = n`. -/
theorem le_totient_mul_fouvryTau_two (n : ℕ) :
    n ≤ n.totient * fouvryTau 2 n := by
  obtain rfl | hn := eq_or_ne n 0
  · simp
  calc
    n = ∑ d ∈ n.divisors, d.totient := (Nat.sum_totient n).symm
    _ ≤ ∑ _d ∈ n.divisors, n.totient := by
      apply sum_le_sum
      intro d hd
      exact Nat.le_of_dvd (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hn))
        (Nat.totient_dvd_of_dvd (Nat.dvd_of_mem_divisors hd))
    _ = n.totient * fouvryTau 2 n := by simp [fouvryTau_two, Nat.mul_comm]

/-- Replace a totient denominator by an ordinary reciprocal while doubling
the fixed divisor order. -/
theorem fouvryTau_div_totient_le (k n : ℕ) :
    (fouvryTau k n : ℝ) / n.totient ≤ (fouvryTau (2 * k) n : ℝ) / n := by
  obtain rfl | hn := eq_or_ne n 0
  · simp
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hφpos : (0 : ℝ) < n.totient := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero hn)
  have hbound : (n : ℝ) ≤ (n.totient : ℝ) * fouvryTau 2 n := by
    exact_mod_cast le_totient_mul_fouvryTau_two n
  have hprod : (fouvryTau 2 n : ℝ) * fouvryTau k n ≤ fouvryTau (2 * k) n := by
    exact_mod_cast fouvryTau_mul_le 2 k n
  apply (div_le_div_iff₀ hφpos hnpos).mpr
  calc
    (fouvryTau k n : ℝ) * n ≤
        (fouvryTau k n : ℝ) * (n.totient * (fouvryTau 2 n : ℝ)) :=
      mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = ((fouvryTau 2 n : ℝ) * fouvryTau k n) * n.totient := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hprod hφpos.le

private noncomputable def reciprocalSum (N : ℕ) : ℝ :=
  ∑ d ∈ Ioc 0 N, (d : ℝ)⁻¹

private theorem reciprocalSum_nonneg (N : ℕ) : 0 ≤ reciprocalSum N :=
  Finset.sum_nonneg (fun _ _ => by positivity)

private theorem reciprocalSum_mono {M N : ℕ} (h : M ≤ N) :
    reciprocalSum M ≤ reciprocalSum N :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ioc_subset_Ioc_right h)
    (fun _ _ _ => by positivity)

private theorem reciprocalSum_le_log (N : ℕ) :
    reciprocalSum N ≤ 1 + Real.log N := by
  convert harmonic_le_one_add_log N using 1
  have heq : Ioc 0 N = Icc 1 N := by ext; simp only [mem_Ioc, mem_Icc]; omega
  simp [reciprocalSum, harmonic_eq_sum_Icc, heq]

private noncomputable def reciprocalTau (k : ℕ) : ArithmeticFunction ℝ where
  toFun n := (fouvryTau k n : ℝ) / n
  map_zero' := by simp

private theorem reciprocalTau_succ (k : ℕ) :
    reciprocalTau (k + 1) = reciprocalTau k * reciprocalTau 1 := by
  ext n
  change (fouvryTau (k + 1) n : ℝ) / n = _
  rw [show fouvryTau (k + 1) = fouvryTau k * fouvryTau 1 by
    change ArithmeticFunction.zeta ^ (k + 1) =
      ArithmeticFunction.zeta ^ k * ArithmeticFunction.zeta ^ 1
    rw [pow_one, pow_succ]]
  rw [ArithmeticFunction.mul_apply, Nat.cast_sum, sum_div, ArithmeticFunction.mul_apply]
  apply sum_congr rfl
  intro d hd
  have heq : (n : ℝ) = (d.1 : ℝ) * d.2 := by
    exact_mod_cast (Nat.mem_divisorsAntidiagonal.mp hd).1.symm
  change ((fouvryTau k d.1 * fouvryTau 1 d.2 : ℕ) : ℝ) / n =
    ((fouvryTau k d.1 : ℝ) / d.1) * ((fouvryTau 1 d.2 : ℝ) / d.2)
  rw [heq, Nat.cast_mul, div_mul_div_comm]

private theorem sum_reciprocalTau_le (k N : ℕ) :
    (∑ n ∈ Ioc 0 N, reciprocalTau k n) ≤ reciprocalSum N ^ k := by
  induction k with
  | zero =>
    simp only [reciprocalTau, fouvryTau, pow_zero, ArithmeticFunction.one_apply]
    simp [ite_div]
    split_ifs <;> norm_num
  | succ k ih =>
    rw [reciprocalTau_succ, ArithmeticFunction.sum_Ioc_mul_eq_sum_prod_filter]
    calc
      _ ≤ ∑ d ∈ Ioc 0 N ×ˢ Ioc 0 N, reciprocalTau k d.1 * reciprocalTau 1 d.2 :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
          (fun d _ _ => by
            change 0 ≤ ((fouvryTau k d.1 : ℝ) / d.1) *
              ((fouvryTau 1 d.2 : ℝ) / d.2)
            positivity)
      _ = (∑ d ∈ Ioc 0 N, reciprocalTau k d) * reciprocalSum N := by
        rw [sum_product, reciprocalSum, sum_mul_sum]
        apply sum_congr rfl
        intro d _
        apply sum_congr rfl
        intro e he
        change _ * ((fouvryTau 1 e : ℝ) / e) = _ * (e : ℝ)⁻¹
        rw [fouvryTau_order_one (mem_Ioc.mp he).1.ne', Nat.cast_one, one_div]
      _ ≤ reciprocalSum N ^ (k + 1) := by
        rw [pow_succ]
        exact mul_le_mul_of_nonneg_right ih (reciprocalSum_nonneg _)

/-- The reciprocal mean needed when paying modulus weights. Order zero is
allowed in this estimate. -/
theorem sum_fouvryTau_div_le (k N : ℕ) :
    (∑ n ∈ Ioc 0 N, (fouvryTau k n : ℝ) / n) ≤ (1 + Real.log N) ^ k := by
  exact (sum_reciprocalTau_le k N).trans
    (pow_le_pow_left₀ (reciprocalSum_nonneg _) (reciprocalSum_le_log _) _)

/-- Reciprocal divisor means at a real endpoint. -/
theorem sum_fouvryTau_div_le_real (k : ℕ) {x : ℝ} (hx : 1 ≤ x) :
    (∑ n ∈ Ioc 0 ⌊x⌋₊, (fouvryTau k n : ℝ) / n) ≤ (1 + Real.log x) ^ k := by
  have heq : reciprocalSum ⌊x⌋₊ = (harmonic ⌊x⌋₊ : ℝ) := by
    have hI : Ioc 0 ⌊x⌋₊ = Icc 1 ⌊x⌋₊ := by
      ext; simp only [mem_Ioc, mem_Icc]; omega
    simp [reciprocalSum, harmonic_eq_sum_Icc, hI]
  exact (sum_reciprocalTau_le k ⌊x⌋₊).trans
    (pow_le_pow_left₀ (reciprocalSum_nonneg _)
      (heq ▸ harmonic_floor_le_one_add_log x hx) _)

/-- A global totient-weighted divisor mean, with no order-dependent
implicit constant. -/
theorem sum_fouvryTau_div_totient_le_real (k : ℕ) {x : ℝ} (hx : 1 ≤ x) :
    (∑ n ∈ Ioc 0 ⌊x⌋₊, (fouvryTau k n : ℝ) / n.totient) ≤
      (1 + Real.log x) ^ (2 * k) := by
  calc
    _ ≤ ∑ n ∈ Ioc 0 ⌊x⌋₊, (fouvryTau (2 * k) n : ℝ) / n :=
      sum_le_sum (fun n _ => fouvryTau_div_totient_le k n)
    _ ≤ _ := sum_fouvryTau_div_le_real _ hx

/-- The reciprocal second moment, useful for sums of modulus weights. -/
theorem sum_fouvryTau_sq_div_le_real (k : ℕ) {x : ℝ} (hx : 1 ≤ x) :
    (∑ n ∈ Ioc 0 ⌊x⌋₊, (fouvryTau k n : ℝ) ^ 2 / n) ≤
      (1 + Real.log x) ^ (k ^ 2) := by
  calc
    _ ≤ ∑ n ∈ Ioc 0 ⌊x⌋₊, (fouvryTau (k ^ 2) n : ℝ) / n := by
      apply sum_le_sum
      intro n _
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      exact_mod_cast fouvryTau_sq_le k n
    _ ≤ _ := sum_fouvryTau_div_le_real _ hx

/-- Totient-weighted second moments also retain a fixed logarithm exponent. -/
theorem sum_fouvryTau_sq_div_totient_le_real (k : ℕ) {x : ℝ} (hx : 1 ≤ x) :
    (∑ n ∈ Ioc 0 ⌊x⌋₊, (fouvryTau k n : ℝ) ^ 2 / n.totient) ≤
      (1 + Real.log x) ^ (2 * k ^ 2) := by
  calc
    _ ≤ ∑ n ∈ Ioc 0 ⌊x⌋₊, (fouvryTau (k ^ 2) n : ℝ) / n.totient := by
      apply sum_le_sum
      intro n _
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      exact_mod_cast fouvryTau_sq_le k n
    _ ≤ _ := sum_fouvryTau_div_totient_le_real _ hx

private theorem sum_fouvryTau_le_harmonic (k N : ℕ) :
    (∑ n ∈ Ioc 0 N, (fouvryTau (k + 1) n : ℝ)) ≤
      N * reciprocalSum N ^ k := by
  induction k generalizing N with
  | zero =>
    simp only [zero_add, pow_zero, mul_one]
    have : ∑ n ∈ Ioc 0 N, fouvryTau 1 n = N := by
      simpa [fouvryTau] using ArithmeticFunction.sum_Ioc_zeta N
    exact_mod_cast this.le
  | succ k ih =>
    have hrec : ∑ n ∈ Ioc 0 N, fouvryTau (k + 1 + 1) n =
        ∑ d ∈ Ioc 0 N, ∑ n ∈ Ioc 0 (N / d), fouvryTau (k + 1) n := by
      change (∑ n ∈ Ioc 0 N,
        (ArithmeticFunction.zeta ^ (k + 1 + 1)) n) = _
      rw [pow_succ', ArithmeticFunction.sum_Ioc_mul_eq_sum_sum]
      apply sum_congr rfl
      intro d hd
      rw [ArithmeticFunction.zeta_apply_ne (mem_Ioc.mp hd).1.ne', one_mul]
      rfl
    rw [show (∑ n ∈ Ioc 0 N, (fouvryTau (k + 1 + 1) n : ℝ)) =
        ∑ d ∈ Ioc 0 N, ∑ n ∈ Ioc 0 (N / d), (fouvryTau (k + 1) n : ℝ) by
          exact_mod_cast hrec]
    calc
      _ ≤ ∑ d ∈ Ioc 0 N, (N / d : ℕ) * reciprocalSum (N / d) ^ k :=
        sum_le_sum (fun d _ => ih (N / d))
      _ ≤ ∑ d ∈ Ioc 0 N, ((N : ℝ) / d) * reciprocalSum N ^ k := by
        apply sum_le_sum
        intro d hd
        apply mul_le_mul
        · exact Nat.cast_div_le
        · exact pow_le_pow_left₀ (reciprocalSum_nonneg _) (reciprocalSum_mono (Nat.div_le_self _ _)) _
        · exact pow_nonneg (reciprocalSum_nonneg _) _
        · positivity
      _ = N * reciprocalSum N ^ (k + 1) := by
        simp only [div_eq_mul_inv, ← sum_mul, ← mul_sum, reciprocalSum, pow_succ]
        ring

/-- The global mean has logarithm exponent exactly one less than the order. -/
theorem sum_fouvryTau_le (k N : ℕ) :
    (∑ n ∈ Ioc 0 N, (fouvryTau (k + 1) n : ℝ)) ≤
      N * (1 + Real.log N) ^ k := by
  refine (sum_fouvryTau_le_harmonic k N).trans ?_
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (reciprocalSum_nonneg _) (reciprocalSum_le_log _) _) (by positivity)

/-- Real-endpoint form, uniform in `x`, with the order kept explicit. -/
theorem sum_fouvryTau_le_real {k : ℕ} (hk : 1 ≤ k) {x : ℝ} (hx : 1 ≤ x) :
    (∑ n ∈ Ioc 0 ⌊x⌋₊, (fouvryTau k n : ℝ)) ≤
      x * (1 + Real.log x) ^ (k - 1) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  have hfloor : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by simpa using hx)
  have hlog : 1 + Real.log (⌊x⌋₊ : ℝ) ≤ 1 + Real.log x := by
    have := Real.log_le_log (by exact_mod_cast (show 0 < ⌊x⌋₊ by omega))
      (Nat.floor_le (by linarith : 0 ≤ x))
    linarith
  have hnonneg : 0 ≤ 1 + Real.log (⌊x⌋₊ : ℝ) := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ ⌊x⌋₊ by exact_mod_cast hfloor)
    linarith
  simpa only [Nat.succ_sub_one] using
    (sum_fouvryTau_le j ⌊x⌋₊).trans
      (mul_le_mul (Nat.floor_le (by linarith)) (pow_le_pow_left₀ hnonneg hlog j)
        (pow_nonneg hnonneg j) (by linarith : 0 ≤ x))

/-- Every fixed integral moment has a global logarithmic bound. -/
theorem sum_fouvryTau_pow_le_real {k : ℕ} (hk : 1 ≤ k) (r : ℕ)
    {x : ℝ} (hx : 1 ≤ x) :
    (∑ n ∈ Ioc 0 ⌊x⌋₊, (fouvryTau k n : ℝ) ^ r) ≤
      x * (1 + Real.log x) ^ (k ^ r - 1) := by
  calc
    _ ≤ ∑ n ∈ Ioc 0 ⌊x⌋₊, (fouvryTau (k ^ r) n : ℝ) := by
      apply sum_le_sum
      intro n hn
      exact_mod_cast fouvryTau_pow_le k r (mem_Ioc.mp hn).1.ne'
    _ ≤ _ := sum_fouvryTau_le_real (Nat.one_le_pow r k hk) hx

/-- Unrestricted second moment with logarithm exponent `k² - 1`. -/
theorem sum_fouvryTau_sq_le_real {k : ℕ} (hk : 1 ≤ k) {x : ℝ} (hx : 1 ≤ x) :
    (∑ n ∈ Ioc 0 ⌊x⌋₊, (fouvryTau k n : ℝ) ^ 2) ≤
      x * (1 + Real.log x) ^ (k ^ 2 - 1) := by
  calc
    _ ≤ ∑ n ∈ Ioc 0 ⌊x⌋₊, (fouvryTau (k ^ 2) n : ℝ) := by
      apply sum_le_sum
      intro n _
      exact_mod_cast fouvryTau_sq_le k n
    _ ≤ _ := sum_fouvryTau_le_real (by nlinarith) hx

/-- The coefficient square sum required by dispersion, for arbitrary finite
support and signed coefficients dominated by the actual divisor function. -/
theorem sum_alpha_sq_le_fouvryTau {k : ℕ} (hk : 1 ≤ k) {x : ℝ} (hx : 1 ≤ x)
    (S : Finset ℕ) (hS : S ⊆ Ioc 0 ⌊x⌋₊) (α : ℕ → ℝ)
    (hα : ∀ n ∈ S, |α n| ≤ (fouvryTau k n : ℝ)) :
    (∑ n ∈ S, α n ^ 2) ≤ x * (1 + Real.log x) ^ (k ^ 2 - 1) := by
  calc
    _ ≤ ∑ n ∈ S, (fouvryTau k n : ℝ) ^ 2 := by
      apply sum_le_sum
      intro n hn
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (α n)) (hα n hn) 2
    _ ≤ ∑ n ∈ Ioc 0 ⌊x⌋₊, (fouvryTau k n : ℝ) ^ 2 :=
      sum_le_sum_of_subset_of_nonneg hS (fun _ _ _ => sq_nonneg _)
    _ ≤ _ := sum_fouvryTau_sq_le_real hk hx

/-- Direct dyadic alpha payment; the constant is independent of the scale,
the finite support, and the coefficients. -/
theorem sum_alpha_sq_dyadic_le {k : ℕ} (hk : 1 ≤ k) {M : ℝ} (hM : 1 ≤ M)
    (S : Finset ℕ) (hS : ∀ n ∈ S, M ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * M)
    (α : ℕ → ℝ) (hα : ∀ n ∈ S, |α n| ≤ (fouvryTau k n : ℝ)) :
    (∑ n ∈ S, α n ^ 2) ≤ 2 * M * (1 + Real.log (2 * M)) ^ (k ^ 2 - 1) := by
  apply sum_alpha_sq_le_fouvryTau hk (by linarith : 1 ≤ 2 * M) S _ α hα
  intro n hn
  have h := hS n hn
  apply mem_Ioc.mpr
  constructor
  · have : (0 : ℝ) < n := by linarith
    exact_mod_cast this
  · exact Nat.le_floor h.2

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
