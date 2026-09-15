import PrimeNumberTheoremAnd.ZetaBounds
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.Algebra.BigOperators.Module

/-!
# Finite Abel foundation for a weak Dirichlet-L strip

For every nonprincipal complex Dirichlet character modulo `q`, this module
proves the explicit prefix bound `‖∑ k < N, χ k‖ ≤ q` and exact finite Abel
identities for the Dirichlet-series and derivative weights.  No strip source
predicate is assumed.
-/

open Complex Finset

namespace DirichletLWeakStripDerivative

variable {q : ℕ} [NeZero q]

omit [NeZero q] in
lemma character_norm_le_one (χ : DirichletCharacter ℂ q) (n : ℕ) : ‖χ n‖ ≤ 1 := by
  exact DirichletCharacter.norm_le_one χ (n : ZMod q)

lemma sum_one_period_eq_zero (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    ∑ n ∈ range q, χ n = 0 := by
  cases q with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ q =>
      rw [← Fin.sum_univ_eq_sum_range]
      calc
        ∑ i : Fin (q + 1), χ (i : ℕ) =
            ∑ i : Fin (q + 1), χ ((ZMod.finEquiv (q + 1)) i) := by
          apply Finset.sum_congr rfl
          intro i _
          congr 1
          apply ZMod.val_injective
          rw [ZMod.val_natCast_of_lt i.isLt]
          rfl
        _ = ∑ a : ZMod (q + 1), χ a :=
          Equiv.sum_comp (ZMod.finEquiv (q + 1)).toEquiv χ
        _ = 0 := MulChar.sum_eq_zero_of_ne_one hχ

lemma sum_aligned_period_eq_zero (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (k : ℕ) :
    ∑ i ∈ range q, χ (k * q + i) = 0 := by
  have hterm (i : ℕ) : χ (k * q + i) = χ i := by
    simp only [ZMod.natCast_self, mul_zero, zero_add]
  simpa only [hterm] using sum_one_period_eq_zero χ hχ

lemma sum_mul_period_eq_zero (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    ∀ k : ℕ, ∑ i ∈ range (k * q), χ i = 0 := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Nat.succ_mul, sum_range_add, ih, zero_add]
      simpa [Nat.add_comm] using sum_aligned_period_eq_zero χ hχ k

/-- A nonprincipal character has every prefix sum bounded by its modulus. -/
lemma norm_sum_range_character_le_modulus (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (N : ℕ) :
    ‖∑ n ∈ range N, χ n‖ ≤ q := by
  have hq : 0 < q := NeZero.pos q
  have hN : N = (N / q) * q + N % q := by
    simpa [Nat.mul_comm] using (Nat.div_add_mod N q).symm
  rw [hN, sum_range_add, sum_mul_period_eq_zero χ hχ, zero_add]
  have hshift (i : ℕ) : χ (((N / q) * q + i : ℕ)) = χ i := by
    simp only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, mul_zero, zero_add]
  simp_rw [hshift]
  calc
    ‖∑ i ∈ range (N % q), χ i‖ ≤ ∑ i ∈ range (N % q), ‖χ i‖ := norm_sum_le _ _
    _ ≤ ∑ _i ∈ range (N % q), (1 : ℝ) := sum_le_sum fun i _ => character_norm_le_one χ i
    _ = ((N % q : ℕ) : ℝ) := by simp
    _ ≤ q := by exact_mod_cast (Nat.le_of_lt (Nat.mod_lt N hq))

omit [NeZero q] in
/-- Finite Abel summation for a Dirichlet character. -/
lemma abel_Ico (χ : DirichletCharacter ℂ q) (f : ℕ → ℂ) {m n : ℕ} (hmn : m < n) :
    ∑ i ∈ Ico m n, f i * χ i =
      f (n - 1) * (∑ i ∈ range n, χ i) - f m * (∑ i ∈ range m, χ i) -
        ∑ i ∈ Ico m (n - 1), (f (i + 1) - f i) * (∑ j ∈ range (i + 1), χ j) := by
  simpa only [smul_eq_mul] using Finset.sum_Ico_by_parts f (fun i : ℕ => χ i) hmn

omit [NeZero q] in
/-- Exact finite partial summation for the weight `k ↦ k⁻ˢ`. -/
lemma dirichlet_cpow_abel_Ico (χ : DirichletCharacter ℂ q) (s : ℂ) {m n : ℕ}
    (hmn : m < n) :
    ∑ k ∈ Ico m n, (k : ℂ) ^ (-s) * χ k =
      (n - 1 : ℕ) ^ (-s) * (∑ k ∈ range n, χ k) -
        (m : ℂ) ^ (-s) * (∑ k ∈ range m, χ k) -
        ∑ k ∈ Ico m (n - 1),
          (((k + 1 : ℕ) : ℂ) ^ (-s) - (k : ℂ) ^ (-s)) *
            (∑ j ∈ range (k + 1), χ j) := by
  exact abel_Ico χ (fun k : ℕ => (k : ℂ) ^ (-s)) hmn

omit [NeZero q] in
/-- Exact finite Abel summation for the derivative weight
`-log(k) k⁻ˢ`. -/
lemma dirichlet_derivative_weight_abel_Ico (χ : DirichletCharacter ℂ q) (s : ℂ)
    {m n : ℕ} (hmn : m < n) :
    ∑ k ∈ Ico m n, (-(Complex.log k) * (k : ℂ) ^ (-s)) * χ k =
      (-(Complex.log ((n - 1 : ℕ) : ℂ)) * ((n - 1 : ℕ) : ℂ) ^ (-s)) *
          (∑ k ∈ range n, χ k) -
        (-(Complex.log (m : ℂ)) * (m : ℂ) ^ (-s)) * (∑ k ∈ range m, χ k) -
        ∑ k ∈ Ico m (n - 1),
          ((-(Complex.log ((k + 1 : ℕ) : ℂ)) * ((k + 1 : ℕ) : ℂ) ^ (-s)) -
            (-(Complex.log (k : ℂ)) * (k : ℂ) ^ (-s))) *
              (∑ j ∈ range (k + 1), χ j) := by
  exact abel_Ico χ (fun k : ℕ => -(Complex.log k) * (k : ℂ) ^ (-s)) hmn

end DirichletLWeakStripDerivative