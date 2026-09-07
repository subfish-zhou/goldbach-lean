import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Divided Dirichlet powers of a prime box

The normalization is performed on the full arithmetic function, not just its
squarefree coefficients. Multiplicity is retained by taking factorially many
copies when recovering the unnormalized power.
-/

namespace MathlibNt.SieveTheory.LiLiuPrereqWF

open ArithmeticFunction Finset

/-- The indicator of the primes in a finite box, including an explicit prime filter. -/
def primeBox (B : Finset ℕ) : ArithmeticFunction ℕ :=
  ⟨fun n => if n ∈ B ∧ n.Prime then 1 else 0, by simp [Nat.not_prime_zero]⟩

@[simp]
theorem primeBox_apply (B : Finset ℕ) (n : ℕ) :
    primeBox B n = if n ∈ B ∧ n.Prime then 1 else 0 := rfl

theorem primeBox_mul_apply (B : Finset ℕ) (g : ArithmeticFunction ℕ) (n : ℕ) :
    (primeBox B * g) n =
      ∑ p ∈ n.primeFactors, if p ∈ B then g (n / p) else 0 := by
  rw [mul_apply, Nat.sum_divisorsAntidiagonal (fun p q => primeBox B p * g q)]
  calc
    ∑ p ∈ n.divisors, primeBox B p * g (n / p) =
        ∑ p ∈ n.primeFactors, primeBox B p * g (n / p) := by
      symm
      apply Finset.sum_subset
      · intro p hp
        obtain ⟨_, hd, hn⟩ := Nat.mem_primeFactors.mp hp
        exact Nat.mem_divisors.mpr ⟨hd, hn⟩
      · intro p hp hnot
        have hnp : ¬ p.Prime := by
          intro hprime
          exact hnot (Nat.mem_primeFactors.mpr
            ⟨hprime, (Nat.mem_divisors.mp hp).1, (Nat.mem_divisors.mp hp).2⟩)
        simp [hnp]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro p hp
      simp [Nat.prime_of_mem_primeFactors hp, ite_mul]

theorem cardFactors_div_prime_add_one {n p : ℕ} (hp : p ∈ n.primeFactors) :
    cardFactors n = 1 + cardFactors (n / p) := by
  have hprime := Nat.prime_of_mem_primeFactors hp
  have hquot : n / p ≠ 0 :=
    (Nat.div_pos (Nat.le_of_mem_primeFactors hp) hprime.pos).ne'
  calc
    cardFactors n = cardFactors (p * (n / p)) :=
      congrArg cardFactors (Nat.mul_div_cancel' (Nat.dvd_of_mem_primeFactors hp)).symm
    _ = _ := by rw [cardFactors_mul hprime.ne_zero hquot, cardFactors_apply_prime hprime]

/-- A nonzero coefficient of the k-fold prime convolution has exactly k prime
factors with multiplicity. This includes nonsquarefree integers. -/
theorem primeBox_pow_eq_zero_of_cardFactors_ne (B : Finset ℕ) (k n : ℕ)
    (h : cardFactors n ≠ k) : (primeBox B ^ k) n = 0 := by
  induction k generalizing n with
  | zero =>
      have hn : n ≠ 1 := by
        rintro rfl
        exact h cardFactors_one
      simp [hn]
  | succ k ih =>
      rw [pow_succ', primeBox_mul_apply]
      apply Finset.sum_eq_zero
      intro p hp
      have hne : cardFactors (n / p) ≠ k := by
        intro heq
        apply h
        rw [cardFactors_div_prime_add_one hp, heq]
        omega
      simp [ih (n / p) hne]

/-- Factorial domination for every integer, proved by the prime-divisor
recurrence and the distinction between distinct and repeated prime factors. -/
theorem primeBox_pow_le_factorial (B : Finset ℕ) (k n : ℕ) :
    (primeBox B ^ k) n ≤ k.factorial := by
  induction k generalizing n with
  | zero =>
      by_cases hn : n = 1 <;> simp [hn]
  | succ k ih =>
      by_cases h : cardFactors n = k + 1
      · rw [pow_succ', primeBox_mul_apply]
        calc
          ∑ p ∈ n.primeFactors, (if p ∈ B then (primeBox B ^ k) (n / p) else 0) ≤
              ∑ _p ∈ n.primeFactors, k.factorial := by
            apply Finset.sum_le_sum
            intro p _
            split_ifs
            · exact ih (n / p)
            · exact Nat.zero_le _
          _ = n.primeFactors.card * k.factorial := by simp
          _ ≤ (k + 1) * k.factorial := by
            apply Nat.mul_le_mul_right
            calc
              n.primeFactors.card ≤ cardFactors n := List.toFinset_card_le _
              _ = k + 1 := h
          _ = (k + 1).factorial := (Nat.factorial_succ k).symm
      · rw [primeBox_pow_eq_zero_of_cardFactors_ne B (k + 1) n h]
        exact Nat.zero_le _

/-- The real divided Dirichlet power; multiplication here is convolution. -/
noncomputable def dividedPower (f : ArithmeticFunction ℝ) (k : ℕ) :
    ArithmeticFunction ℝ :=
  (k.factorial : ℝ)⁻¹ • f ^ k

@[simp]
theorem dividedPower_apply (f : ArithmeticFunction ℝ) (k n : ℕ) :
    dividedPower f k n = (f ^ k) n / k.factorial := by
  simp [dividedPower, div_eq_mul_inv, mul_comm]

theorem factorial_mul_dividedPower (f : ArithmeticFunction ℝ) (k : ℕ) :
    (k.factorial : ℝ) • dividedPower f k = f ^ k := by
  rw [dividedPower, smul_smul, mul_inv_cancel₀, one_smul]
  exact_mod_cast Nat.factorial_ne_zero k

theorem smul_convolution (r s : ℝ) (f g : ArithmeticFunction ℝ) :
    (r • f) * (s • g) = (r * s) • (f * g) := by
  ext n
  simp only [mul_apply, smul_map, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d _
  ring

theorem dividedPower_split (f : ArithmeticFunction ℝ) (a b : ℕ) :
    dividedPower f (a + b) =
      (((a.factorial : ℝ) * b.factorial / (a + b).factorial) • dividedPower f a) *
        dividedPower f b := by
  unfold dividedPower
  rw [smul_smul, smul_convolution, ← pow_add]
  congr 1
  have ha : (a.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero a
  have hb : (b.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero b
  field_simp

theorem factorial_ratio_pos (a b : ℕ) :
    0 < (a.factorial : ℝ) * b.factorial / (a + b).factorial := by
  positivity

theorem factorial_ratio_le_one (a b : ℕ) :
    (a.factorial : ℝ) * b.factorial / (a + b).factorial ≤ 1 := by
  have h : a.factorial * b.factorial ≤ (a + b).factorial :=
    Nat.le_of_dvd (Nat.factorial_pos _) (Nat.factorial_mul_factorial_dvd_factorial_add a b)
  apply (div_le_one (by positivity : (0 : ℝ) < (a + b).factorial)).mpr
  exact_mod_cast h

theorem real_natCast_pow (f : ArithmeticFunction ℕ) (k : ℕ) :
    (f : ArithmeticFunction ℝ) ^ k = (f ^ k : ArithmeticFunction ℕ) := by
  induction k with
  | zero => simp
  | succ k ih => simp only [pow_succ, ih, natCoe_mul]

/-- The fixed normalized box weight. No split occurs in its definition. -/
noncomputable def boxWeight (B : Finset ℕ) (k : ℕ) : ArithmeticFunction ℝ :=
  dividedPower (primeBox B : ArithmeticFunction ℝ) k

theorem boxWeight_apply (B : Finset ℕ) (k n : ℕ) :
    boxWeight B k n = ((primeBox B ^ k) n : ℝ) / k.factorial := by
  simp [boxWeight, dividedPower_apply, real_natCast_pow]

theorem boxWeight_nonneg (B : Finset ℕ) (k n : ℕ) : 0 ≤ boxWeight B k n := by
  rw [boxWeight_apply]
  positivity

theorem boxWeight_le_one (B : Finset ℕ) (k n : ℕ) : boxWeight B k n ≤ 1 := by
  rw [boxWeight_apply]
  apply (div_le_one (by positivity : (0 : ℝ) < k.factorial)).mpr
  exact_mod_cast primeBox_pow_le_factorial B k n

theorem boxWeight_abs_le_one (B : Finset ℕ) (k n : ℕ) : |boxWeight B k n| ≤ 1 := by
  rw [abs_of_nonneg (boxWeight_nonneg B k n)]
  exact boxWeight_le_one B k n

theorem primeBox_pow_prime_pow (B : Finset ℕ) {p : ℕ} (hp : p.Prime) (hpB : p ∈ B)
    (k : ℕ) : (primeBox B ^ k) (p ^ k) = 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ', primeBox_mul_apply, Nat.primeFactors_prime_pow (Nat.succ_ne_zero k) hp]
      simpa [hpB, pow_succ, Nat.mul_div_cancel, hp.pos] using ih

/-- In particular the square of a box prime has coefficient 1/2, not zero. -/
theorem boxWeight_prime_pow (B : Finset ℕ) {p : ℕ} (hp : p.Prime) (hpB : p ∈ B)
    (k : ℕ) : boxWeight B k (p ^ k) = (k.factorial : ℝ)⁻¹ := by
  rw [boxWeight_apply, primeBox_pow_prime_pow B hp hpB]
  simp [one_div]

/-- The factorially many copies restore the original coefficient at every n,
so any subsequent finite weighted sum is preserved as well. -/
theorem sum_copies_boxWeight (B : Finset ℕ) (k n : ℕ) :
    (∑ _j ∈ Finset.range k.factorial, boxWeight B k n) =
      ((primeBox B ^ k) n : ℝ) := by
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, boxWeight_apply]
  have hk : (k.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  field_simp

/-- Explicit bounded factors for each division of the slots of the same box. -/
theorem boxWeight_bounded_split (B : Finset ℕ) (a b : ℕ) :
    let left := ((a.factorial : ℝ) * b.factorial / (a + b).factorial) • boxWeight B a
    let right := boxWeight B b
    boxWeight B (a + b) = left * right ∧
      (∀ n, |left n| ≤ 1) ∧ (∀ n, |right n| ≤ 1) := by
  dsimp
  refine ⟨dividedPower_split _ a b, ?_, boxWeight_abs_le_one B b⟩
  intro n
  rw [smul_map, smul_eq_mul, abs_mul, abs_of_pos (factorial_ratio_pos a b)]
  exact mul_le_one₀ (factorial_ratio_le_one a b)
    (abs_nonneg _) (boxWeight_abs_le_one B a n)

end MathlibNt.SieveTheory.LiLiuPrereqWF
