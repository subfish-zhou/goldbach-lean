import MathlibNt.SieveTheory.Distribution.LiuPan.LiuPanConvolutionCoefficient

open scoped BigOperators
open Finset
namespace MathlibNt.SieveTheory.LiuWeight

/-- All nonnegative integers up to N in the specified residue class, not a
prime-counting proxy. The residue need not be reduced or canonical. -/
def liuAPCarrier (N q l : ℕ) : Finset ℕ :=
  (range (N + 1)).filter fun n => n ≡ l [MOD q]

theorem liuAPCarrier_card_le (N q l : ℕ) :
    (liuAPCarrier N q l).card ≤ N / q + 1 := by
  have hinj : Set.InjOn (fun n : ℕ => n / q) (liuAPCarrier N q l) := by
    intro a ha b hb hab
    have hmod : a % q = b % q :=
      (Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm
    change a / q = b / q at hab
    calc
      a = a % q + q * (a / q) := (Nat.mod_add_div a q).symm
      _ = b % q + q * (b / q) := by rw [hmod, hab]
      _ = b := Nat.mod_add_div b q
  apply Finset.card_le_card_of_injOn (fun n => n / q) ?_ hinj |>.trans_eq (Finset.card_range _)
  intro n hn
  have hnN : n ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_filter.mp hn).1)
  exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right hnN))

/-- Positive-a product-fibre bijection for the literal production prime count. -/
theorem primesInAPBelow_eq_divisor_card (N a q l : ℕ) (ha : 0 < a) :
    AnalyticNumberTheory.Sieve.primesInAPBelow N a q l =
      ((liuAPCarrier N q l).filter fun n => a ∈ n.divisors ∧ (n / a).Prime).card := by
  unfold AnalyticNumberTheory.Sieve.primesInAPBelow
  apply Finset.card_bij (fun p _ => a * p)
  · intro p hp
    obtain ⟨_, hprime, hle, hmod⟩ := Finset.mem_filter.mp hp
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hmod⟩, ?_⟩
    refine ⟨Nat.mem_divisors.mpr ⟨dvd_mul_right _ _, Nat.ne_of_gt (Nat.mul_pos ha hprime.pos)⟩, ?_⟩
    simpa [Nat.mul_div_right _ ha] using hprime
  · intro p _ r _ heq
    exact Nat.mul_left_cancel ha heq
  · intro n hn
    obtain ⟨hnAP, hadiv, hprime⟩ := Finset.mem_filter.mp hn
    have hnN : n ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_filter.mp hnAP).1)
    have hprod : a * (n / a) = n := Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hadiv)
    refine ⟨n / a, Finset.mem_filter.mpr ⟨?_, hprime, ?_, ?_⟩, hprod⟩
    · exact Finset.mem_range.mpr (Nat.lt_succ_of_le ((Nat.div_le_self n a).trans hnN))
    · rwa [hprod]
    · rw [hprod]
      exact (Finset.mem_filter.mp hnAP).2

/-- Literal counting part of the source interval sum; no change to its Li term. -/
noncomputable def liuCoprimeIntervalCount (N z y A₁ A₂ q l : ℕ) : ℝ :=
  ∑ a ∈ Ioc A₁ A₂, if a.Coprime q then
    liuWeight N z y a * AnalyticNumberTheory.Sieve.primesInAPBelow N a q l else 0

/-- Product-fibre coefficient retaining both the interval and gcd restrictions. -/
noncomputable def liuBetaInterval (N z y A₁ A₂ q n : ℕ) : ℝ :=
  ∑ a ∈ n.divisors, if a ∈ Ioc A₁ A₂ ∧ a.Coprime q then
    liuWeight N z y a * (if (n / a).Prime then 1 else 0) else 0

/-- Exact finite regrouping, valid without a reduced-residue assumption. -/
theorem liuCoprimeIntervalCount_eq_sum_betaInterval (N z y A₁ A₂ q l : ℕ) :
    liuCoprimeIntervalCount N z y A₁ A₂ q l =
      ∑ n ∈ liuAPCarrier N q l, liuBetaInterval N z y A₁ A₂ q n := by
  classical
  unfold liuCoprimeIntervalCount
  have hterm (a : ℕ) (ha : a ∈ Ioc A₁ A₂) :
      (if a.Coprime q then liuWeight N z y a *
        AnalyticNumberTheory.Sieve.primesInAPBelow N a q l else 0) =
      ∑ n ∈ liuAPCarrier N q l, if a ∈ n.divisors then
        (if a.Coprime q then liuWeight N z y a *
          (if (n / a).Prime then 1 else 0) else 0) else 0 := by
    rw [primesInAPBelow_eq_divisor_card N a q l (by have := (Finset.mem_Ioc.mp ha).1; omega)]
    simp only [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter]
    by_cases hc : a.Coprime q
    · rw [if_pos hc]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _
      split_ifs <;> simp_all
    · simp [hc]
  rw [Finset.sum_congr rfl hterm, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n _
  unfold liuBetaInterval
  calc
    _ = ∑ a ∈ (Ioc A₁ A₂ ∩ n.divisors),
        if a.Coprime q then liuWeight N z y a *
          (if (n / a).Prime then 1 else 0) else 0 := by rw [Finset.sum_ite_mem]
    _ = ∑ a ∈ (n.divisors ∩ Ioc A₁ A₂),
        if a.Coprime q then liuWeight N z y a *
          (if (n / a).Prime then 1 else 0) else 0 := by rw [Finset.inter_comm]
    _ = _ := by
      rw [← Finset.sum_ite_mem]
      apply Finset.sum_congr rfl
      intro a _
      split_ifs <;> simp_all

theorem liuBetaInterval_nonneg (N z y A₁ A₂ q n : ℕ) :
    0 ≤ liuBetaInterval N z y A₁ A₂ q n := by
  apply Finset.sum_nonneg
  intro a _
  split_ifs <;> positivity [liuWeight_nonneg N z y a]

/-- Removing nonnegative interval/gcd filters can only increase a fibre. -/
theorem liuBetaInterval_le_beta (N z y A₁ A₂ q n : ℕ) :
    liuBetaInterval N z y A₁ A₂ q n ≤ liuBeta N z y n := by
  apply Finset.sum_le_sum
  intro a _
  split_ifs <;> simp_all [liuWeight_nonneg]

/-- Whole-a counting bound: no termwise error triangle inequality. -/
theorem liuCoprimeIntervalCount_le_three_mul_div_add_one
    (N z y A₁ A₂ q l : ℕ) :
    liuCoprimeIntervalCount N z y A₁ A₂ q l ≤ 3 * ((N / q : ℕ) + 1 : ℝ) := by
  rw [liuCoprimeIntervalCount_eq_sum_betaInterval]
  calc
    _ ≤ ∑ n ∈ liuAPCarrier N q l, (3 : ℝ) := by
      apply Finset.sum_le_sum
      intro n _
      exact (liuBetaInterval_le_beta N z y A₁ A₂ q n).trans (liuBeta_le_three N z y n)
    _ = 3 * (liuAPCarrier N q l).card := by simp [mul_comm]
    _ ≤ 3 * ((N / q : ℕ) + 1 : ℝ) := by
      gcongr
      exact_mod_cast liuAPCarrier_card_le N q l

/-- Real-division form, for every positive modulus and arbitrary residue. -/
theorem liuCoprimeIntervalCount_le_three_mul_real_div_add_one
    (N z y A₁ A₂ q l : ℕ) (hq : 0 < q) :
    liuCoprimeIntervalCount N z y A₁ A₂ q l ≤ 3 * ((N : ℝ) / q + 1) := by
  refine (liuCoprimeIntervalCount_le_three_mul_div_add_one N z y A₁ A₂ q l).trans ?_
  have hdiv : ((N / q : ℕ) : ℝ) ≤ (N : ℝ) / q := by
    apply (le_div_iff₀ (by exact_mod_cast hq : (0 : ℝ) < q)).mpr
    exact_mod_cast Nat.div_mul_le_self N q
  linarith

end MathlibNt.SieveTheory.LiuWeight