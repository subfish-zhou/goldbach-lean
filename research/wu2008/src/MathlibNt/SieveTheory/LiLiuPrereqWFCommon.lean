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

private theorem prod_map_constant {α : Type*} (l : List α) (U : ℝ) :
    (l.map (fun _ => U)).prod = U ^ l.length := by
  simp

/-- Allocation of k identical box widths with one extra width of slack. -/
theorem exists_slot_split {U Q₁ Q₂ : ℝ} (hU : 1 ≤ U)
    (hQ₁ : 1 ≤ Q₁) (hQ₂ : 1 ≤ Q₂) (k : ℕ)
    (hsplit : Q₁ * Q₂ = U ^ (k + 1)) :
    ∃ a b : ℕ, a + b = k ∧ U ^ a ≤ Q₁ ∧ U ^ b ≤ Q₂ := by
  let input : List Unit := List.replicate k ()
  have hprefix : PrefixSquareBound (fun _ : Unit => U) (Q₁ * Q₂) input := by
    intro i hi
    have hik : i < k := by simpa [input] using hi
    change ((input.take i).map (fun _ : Unit => U)).prod * U ^ 2 ≤ Q₁ * Q₂
    rw [prod_map_constant, List.length_take]
    rw [Nat.min_eq_left hi.le, hsplit, ← pow_add]
    exact pow_le_pow_right₀ hU (by omega)
  obtain ⟨left, right, hpart, hleft, hright⟩ :=
    exists_boxPartition_of_prefixSquareBound (fun _ : Unit => U) hQ₁ hQ₂ input hprefix
  refine ⟨left.length, right.length, ?_, ?_, ?_⟩
  · simpa [input] using hpart.perm.length_eq
  · simpa only [prod_map_constant] using hleft
  · simpa only [prod_map_constant] using hright

/-- A concrete common WF weight. B and k are fixed before every level split;
the only split-dependent objects are the two explicitly normalized factors. -/
theorem boxWeight_wellFactorable (B : Finset ℕ) {U : ℝ} (hU : 1 ≤ U)
    (hB : ∀ p ∈ B, p.Prime → (p : ℝ) ≤ U) (k : ℕ) :
    WellFactorable (boxWeight B k) (U ^ (k + 1)) := by
  have hU₀ : 0 ≤ U := le_trans zero_le_one hU
  refine ⟨one_le_pow₀ hU, boxWeight_abs_le_one B k, ?_, ?_⟩
  · exact supportedAt_mono (boxWeight_supportedAt B hU₀ hB k)
      (pow_le_pow_right₀ hU (Nat.le_succ k))
  · intro Q₁ Q₂ hQ₁ hQ₂ hsplit
    obtain ⟨a, b, hab, ha, hb⟩ := exists_slot_split hU hQ₁ hQ₂ k hsplit
    subst k
    obtain ⟨heq, hleft, hright⟩ := boxWeight_bounded_split B a b
    refine ⟨_, _, hleft, ?_, hright, ?_, heq⟩
    · exact supportedAt_smul _
        (supportedAt_mono (boxWeight_supportedAt B hU₀ hB a) ha)
    · exact supportedAt_mono (boxWeight_supportedAt B hU₀ hB b) hb

end MathlibNt.SieveTheory.LiLiuPrereqWF
