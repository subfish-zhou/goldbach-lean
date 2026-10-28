import MathlibNt.SieveTheory.LiLiuPrereqWFBoxAllocation
import MathlibNt.SieveTheory.LiLiuPrereqWFDividedPowers

/-!
# Closed-support common well-factorability

The function is fixed before all real level splits. The constructed example is
one normalized prime box with one extra box-width of support slack; it is not
the Iwaniec upper/lower sieve family and asserts no sieve density estimate.
-/

namespace MathlibNt.SieveTheory.LiLiuPrereqWF

open ArithmeticFunction Finset
open LiLiuPrereqWFBoxAllocation

def SupportedAt (f : ArithmeticFunction ℝ) (Q : ℝ) : Prop :=
  ∀ n : ℕ, f n ≠ 0 → (n : ℝ) ≤ Q

def BoundedOne (f : ArithmeticFunction ℝ) : Prop :=
  ∀ n : ℕ, |f n| ≤ 1

/-- Closed support, including the identity split. Equality of arithmetic
functions is Dirichlet convolution equality on all natural numbers. -/
def WellFactorable (f : ArithmeticFunction ℝ) (Q : ℝ) : Prop :=
  1 ≤ Q ∧ BoundedOne f ∧ SupportedAt f Q ∧
    ∀ Q₁ Q₂ : ℝ, 1 ≤ Q₁ → 1 ≤ Q₂ → Q₁ * Q₂ = Q →
      ∃ a b : ArithmeticFunction ℝ,
        BoundedOne a ∧ SupportedAt a Q₁ ∧
        BoundedOne b ∧ SupportedAt b Q₂ ∧ f = a * b

theorem supportedAt_mono {f : ArithmeticFunction ℝ} {Q R : ℝ}
    (hf : SupportedAt f Q) (hQR : Q ≤ R) : SupportedAt f R :=
  fun n hn => (hf n hn).trans hQR

theorem supportedAt_smul (r : ℝ) {f : ArithmeticFunction ℝ} {Q : ℝ}
    (hf : SupportedAt f Q) : SupportedAt (r • f) Q := by
  intro n hn
  apply hf n
  intro hz
  exact hn (by simp [hz])

theorem supportedAt_mul {f g : ArithmeticFunction ℝ} {Q R : ℝ}
    (hf : SupportedAt f Q) (hg : SupportedAt g R) (hQ : 0 ≤ Q) :
    SupportedAt (f * g) (Q * R) := by
  intro n hn
  by_contra h
  apply hn
  rw [mul_apply]
  apply Finset.sum_eq_zero
  intro d hd
  by_cases hfz : f d.1 = 0
  · simp [hfz]
  by_cases hgz : g d.2 = 0
  · simp [hgz]
  have heq : d.1 * d.2 = n := (Nat.mem_divisorsAntidiagonal.mp hd).1
  have hle : (n : ℝ) ≤ Q * R := by
    rw [← heq, Nat.cast_mul]
    exact mul_le_mul (hf d.1 hfz) (hg d.2 hgz) (Nat.cast_nonneg _) hQ
  exact (h hle).elim

theorem supportedAt_one : SupportedAt (1 : ArithmeticFunction ℝ) 1 := by
  intro n hn
  by_cases h : n = 1
  · simp [h]
  · simp [h] at hn

theorem supportedAt_pow {f : ArithmeticFunction ℝ} {U : ℝ}
    (hf : SupportedAt f U) (hU : 0 ≤ U) (k : ℕ) :
    SupportedAt (f ^ k) (U ^ k) := by
  induction k with
  | zero => simpa using supportedAt_one
  | succ k ih =>
      simpa only [pow_succ] using supportedAt_mul ih hf (pow_nonneg hU k)

theorem primeBox_supportedAt (B : Finset ℕ) {U : ℝ}
    (hB : ∀ p ∈ B, p.Prime → (p : ℝ) ≤ U) :
    SupportedAt (primeBox B : ArithmeticFunction ℝ) U := by
  intro n hn
  by_cases h : n ∈ B ∧ n.Prime
  · exact hB n h.1 h.2
  · simp [primeBox_apply, h] at hn

theorem boxWeight_supportedAt (B : Finset ℕ) {U : ℝ} (hU : 0 ≤ U)
    (hB : ∀ p ∈ B, p.Prime → (p : ℝ) ≤ U) (k : ℕ) :
    SupportedAt (boxWeight B k) (U ^ k) :=
  supportedAt_smul _ (supportedAt_pow (primeBox_supportedAt B hB) hU k)


end MathlibNt.SieveTheory.LiLiuPrereqWF
