import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryMainTerm
import Mathlib.Data.Nat.Factorization.Basic

/-!
# A uniform elementary main-term estimate for hard cutoffs

Mobius inversion and the error in counting multiples give the coprime
prefix count with error at most the number of divisors of the modulus.
This supplies an actual U main-term estimate for a hard cutoff. It does
not supply the smooth Poisson estimates needed later for V and W.
-/

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

open Finset

noncomputable section

def coprimePrefix (H q : ℕ) : ℝ :=
  ∑ m ∈ Ioc 0 H, if m.Coprime q then 1 else 0

theorem coprimePrefix_eq_divisor_sum (H : ℕ) {q : ℕ} (hq : q ≠ 0) :
    coprimePrefix H q =
      ∑ d ∈ q.divisors, (ArithmeticFunction.moebius d : ℝ) * (H / d : ℕ) := by
  rw [coprimePrefix, coprime_weight_eq_moebius (Ioc 0 H) (fun _ => 1) hq]
  apply Finset.sum_congr rfl
  intro d _
  rw [← Finset.sum_filter]
  simp [Nat.Ioc_filter_dvd_card_eq_div]

theorem coprimePrefix_period (q : ℕ) :
    coprimePrefix q q = (q.totient : ℝ) := by
  have hI : Ioc 0 q = Ico 1 (1 + q) := by
    ext m
    simp only [Finset.mem_Ioc, Finset.mem_Ico]
    omega
  unfold coprimePrefix
  simp_rw [Nat.coprime_comm]
  rw [← Finset.sum_filter, hI]
  simp [Nat.filter_coprime_Ico_eq_totient]

theorem moebius_density {q : ℕ} (hq : q ≠ 0) :
    (∑ d ∈ q.divisors, (ArithmeticFunction.moebius d : ℝ) / (d : ℝ)) =
      (q.totient : ℝ) / (q : ℝ) := by
  rw [← coprimePrefix_period, coprimePrefix_eq_divisor_sum q hq, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Nat.cast_div_charZero (Nat.dvd_of_mem_divisors hd)]
  have hqR : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq
  field_simp

theorem nat_div_error_le_one (H : ℕ) {d : ℕ} (hd : 0 < d) :
    |((H / d : ℕ) : ℝ) - (H : ℝ) / (d : ℝ)| ≤ 1 := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hlo : ((H / d : ℕ) : ℝ) * d ≤ H := by
    exact_mod_cast Nat.div_mul_le_self H d
  have hhi : (H : ℝ) < (d : ℝ) * (((H / d : ℕ) : ℝ) + 1) := by
    exact_mod_cast Nat.lt_mul_div_succ H hd
  have hl := (le_div_iff₀ hdR).mpr hlo
  have hh : (H : ℝ) / (d : ℝ) < ((H / d : ℕ) : ℝ) + 1 :=
    (div_lt_iff₀ hdR).mpr (by nlinarith)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem coprimePrefix_error (H : ℕ) {q : ℕ} (hq : q ≠ 0) :
    |coprimePrefix H q - (H : ℝ) * ((q.totient : ℝ) / q)| ≤
      (q.divisors.card : ℝ) := by
  calc
    _ = |∑ d ∈ q.divisors, (ArithmeticFunction.moebius d : ℝ) *
        (((H / d : ℕ) : ℝ) - (H : ℝ) / d)| := by
      rw [coprimePrefix_eq_divisor_sum H hq, ← moebius_density hq,
        Finset.mul_sum, ← Finset.sum_sub_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro d _
      ring
    _ ≤ ∑ d ∈ q.divisors, |(ArithmeticFunction.moebius d : ℝ) *
        (((H / d : ℕ) : ℝ) - (H : ℝ) / d)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _d ∈ q.divisors, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro d hd
      rw [abs_mul]
      have hmu : |(ArithmeticFunction.moebius d : ℝ)| ≤ 1 := by
        exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := d))
      simpa using mul_le_mul hmu (nat_div_error_le_one H (Nat.pos_of_mem_divisors hd))
        (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    _ = _ := by simp

def uModulusCoefficient (N : Finset ℕ) (β c : ℕ → ℝ) (q r : ℕ) : ℝ :=
  (c q * c r / ((q.totient : ℝ) * (r.totient : ℝ))) *
    coprimeMass N β q * coprimeMass N β r

def hardCutoffUMain (H : ℕ) (N Q : Finset ℕ) (β c : ℕ → ℝ) (a : ℤ) : ℝ :=
  ∑ q ∈ reducedModuli Q a, ∑ r ∈ reducedModuli Q a,
    uModulusCoefficient N β c q r * ((H : ℝ) * ((q * r).totient : ℝ) / (q * r : ℕ))

theorem dispersionU_hardCutoff_error
    (H : ℕ) (N Q : Finset ℕ) (β c : ℕ → ℝ) (a : ℤ)
    (hQ : ∀ q ∈ Q, q ≠ 0) :
    |dispersionU (Ioc 0 H) N Q (fun _ => 1) β c a - hardCutoffUMain H N Q β c a| ≤
      ∑ q ∈ reducedModuli Q a, ∑ r ∈ reducedModuli Q a,
        |uModulusCoefficient N β c q r| * ((q * r).divisors.card : ℝ) := by
  rw [dispersionU_eq_double_sum]
  change |(∑ q ∈ reducedModuli Q a, ∑ r ∈ reducedModuli Q a,
      uModulusCoefficient N β c q r * coprimePrefix H (q * r)) -
    (∑ q ∈ reducedModuli Q a, ∑ r ∈ reducedModuli Q a,
      uModulusCoefficient N β c q r *
        ((H : ℝ) * ((q * r).totient : ℝ) / (q * r : ℕ)))| ≤ _
  rw [← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro q hq
  rw [← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro r hr
  rw [← mul_sub, abs_mul]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  simpa only [mul_div_assoc] using coprimePrefix_error H
    (mul_ne_zero (hQ q (Finset.mem_filter.mp hq).1) (hQ r (Finset.mem_filter.mp hr).1))

end

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
