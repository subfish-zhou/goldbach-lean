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


def uModulusCoefficient (N : Finset ℕ) (β c : ℕ → ℝ) (q r : ℕ) : ℝ :=
  (c q * c r / ((q.totient : ℝ) * (r.totient : ℝ))) *
    coprimeMass N β q * coprimeMass N β r


end

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
