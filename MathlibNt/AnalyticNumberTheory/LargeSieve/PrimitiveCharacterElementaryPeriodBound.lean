import MathlibNt.AnalyticNumberTheory.LargeSieve.PrimitiveCharacters
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.Tactic

namespace AnalyticNumberTheory.LargeSieve

open Finset
open scoped BigOperators

noncomputable section

/-- A primitive character of modulus greater than one is nonprincipal. -/
theorem primitiveCharacter_ne_one {q : ℕ} (hq : 1 < q)
    (χ : PrimitiveCharacter q) : χ.1 ≠ 1 := by
  letI : NeZero q := ⟨by omega⟩
  intro hχ
  have hc : χ.1.conductor = 1 :=
    (DirichletCharacter.eq_one_iff_conductor_eq_one).mp hχ
  have hp : χ.1.conductor = q := χ.2
  omega

/-- The sum of a primitive character over the residue ring is zero when `q > 1`. -/
theorem primitiveCharacter_sum_zmod_eq_zero {q : ℕ} [NeZero q] (hq : 1 < q)
    (χ : PrimitiveCharacter q) :
    ∑ a : ZMod q, χ.1 a = 0 := by
  exact MulChar.sum_eq_zero_of_ne_one (primitiveCharacter_ne_one hq χ)

/-- The usual natural representatives `0, ..., q-1` also give a zero complete period. -/
theorem primitiveCharacter_sum_range_period_eq_zero {q : ℕ} (hq : 1 < q)
    (χ : PrimitiveCharacter q) :
    ∑ n ∈ range q, χ.1 (n : ZMod q) = 0 := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : q ≠ 0)
  letI : NeZero r.succ := ⟨by omega⟩
  calc
    (∑ n ∈ range r.succ, χ.1 (n : ZMod r.succ)) =
        ∑ i : Fin r.succ, χ.1 ((i : ℕ) : ZMod r.succ) := by
          symm
          exact Fin.sum_univ_eq_sum_range
            (fun n : ℕ => χ.1 (n : ZMod r.succ)) r.succ
    _ = ∑ a : ZMod r.succ, χ.1 a := by
      apply Fintype.sum_equiv (ZMod.finEquiv r.succ).toEquiv
      intro i
      congr 1
      exact ZMod.natCast_zmod_val (ZMod.finEquiv r.succ i)
    _ = 0 := primitiveCharacter_sum_zmod_eq_zero hq χ

private theorem sum_range_mul_period_eq_zero {E : Type*} [AddCommMonoid E]
    (f : ℕ → E) (q : ℕ) (hperiod : ∀ k n, f (k * q + n) = f n)
    (hzero : ∑ n ∈ range q, f n = 0) :
    ∀ k : ℕ, ∑ n ∈ range (k * q), f n = 0 := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Nat.succ_mul, sum_range_add, ih, zero_add]
      rw [← hzero]
      exact Finset.sum_congr rfl fun n _ => hperiod k n

/-- Every prefix of a primitive character has the elementary complete-period bound `q`. -/
theorem primitiveCharacter_prefix_norm_le {q M : ℕ} (hq : 1 < q)
    (χ : PrimitiveCharacter q) :
    ‖∑ n ∈ range M, χ.1 (n : ZMod q)‖ ≤ q := by
  have hperiod : ∀ k n : ℕ,
      χ.1 ((k * q + n : ℕ) : ZMod q) = χ.1 (n : ZMod q) := by
    intro k n
    congr 1
    simp
  have hblocks : ∀ k : ℕ,
      ∑ n ∈ range (k * q), χ.1 (n : ZMod q) = 0 :=
    sum_range_mul_period_eq_zero (fun n : ℕ => χ.1 (n : ZMod q)) q hperiod
      (primitiveCharacter_sum_range_period_eq_zero hq χ)
  rw [← Nat.div_add_mod M q, Nat.mul_comm q (M / q), sum_range_add,
    hblocks, zero_add]
  calc
    ‖∑ n ∈ range (M % q), χ.1 (((M / q) * q + n : ℕ) : ZMod q)‖
        ≤ ∑ n ∈ range (M % q), ‖χ.1 (((M / q) * q + n : ℕ) : ZMod q)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _n ∈ range (M % q), (1 : ℝ) := by
      exact sum_le_sum fun n _ => DirichletCharacter.norm_le_one χ.1 _
    _ = (M % q : ℕ) := by simp
    _ ≤ q := by
      exact_mod_cast Nat.le_of_lt (Nat.mod_lt M (by omega))

/-- Every half-open interval has norm at most `2q`, by subtraction of two prefixes. -/
theorem primitiveCharacter_interval_norm_le_two_mul {q A B : ℕ} (hq : 1 < q)
    (χ : PrimitiveCharacter q) :
    ‖∑ n ∈ Ico A B, χ.1 (n : ZMod q)‖ ≤ 2 * q := by
  by_cases hAB : A ≤ B
  · rw [sum_Ico_eq_sub _ hAB]
    calc
      ‖(∑ n ∈ range B, χ.1 (n : ZMod q)) -
          ∑ n ∈ range A, χ.1 (n : ZMod q)‖
          ≤ ‖∑ n ∈ range B, χ.1 (n : ZMod q)‖ +
              ‖∑ n ∈ range A, χ.1 (n : ZMod q)‖ := norm_sub_le _ _
      _ ≤ q + q := add_le_add
        (primitiveCharacter_prefix_norm_le hq χ)
        (primitiveCharacter_prefix_norm_le hq χ)
      _ = 2 * q := by ring
  · rw [Finset.Ico_eq_empty (by omega)]
    simp

private theorem finite_summation_by_parts (f : ℕ → ℂ) (w : ℕ → ℂ) (M : ℕ) :
    (∑ k ∈ range M, w k * f k) =
      w M * (∑ k ∈ range M, f k) +
        ∑ k ∈ range M,
          (w k - w (k + 1)) * (∑ j ∈ range (k + 1), f j) := by
  induction M with
  | zero => simp
  | succ M ih =>
      simp only [sum_range_succ, ih]
      ring

private theorem shifted_prefix_eq_Ico (f : ℕ → ℂ) (N : ℕ) :
    (∑ k ∈ range N, f (k + 1)) = ∑ m ∈ Ico 1 (N + 1), f m := by
  simpa [Nat.add_comm] using (Finset.sum_Ico_add f 0 N 1)

/-- Abel summation with the elementary interval bound gives a completely
algebraic logarithmic-weight estimate.  The constant `4` comes from using the
safe `2q` interval estimate for shifted prefixes. -/
theorem primitiveCharacter_logWeight_range_norm_le {q M : ℕ} (hq : 1 < q)
    (χ : PrimitiveCharacter q) :
    ‖∑ k ∈ range M,
        (Real.log (k + 1) : ℂ) * χ.1 ((k + 1 : ℕ) : ZMod q)‖
      ≤ 4 * q * Real.log (M + 1) := by
  let f : ℕ → ℂ := fun k => χ.1 ((k + 1 : ℕ) : ZMod q)
  let w : ℕ → ℂ := fun k => (Real.log (k + 1) : ℂ)
  let S : ℕ → ℂ := fun n => ∑ k ∈ range n, f k
  have hS (n : ℕ) : ‖S n‖ ≤ 2 * q := by
    change ‖∑ k ∈ range n, χ.1 ((k + 1 : ℕ) : ZMod q)‖ ≤ 2 * q
    have heq : (∑ k ∈ range n, χ.1 ((k + 1 : ℕ) : ZMod q)) =
        ∑ m ∈ Ico 1 (n + 1), χ.1 (m : ZMod q) := by
      simpa only [Nat.add_comm] using
        shifted_prefix_eq_Ico (fun m : ℕ => χ.1 (m : ZMod q)) n
    rw [heq]
    exact primitiveCharacter_interval_norm_le_two_mul hq χ
  have hwmono (k : ℕ) : Real.log (k + 1) ≤ Real.log (k + 2) := by
    apply Real.strictMonoOn_log.monotoneOn
    · change 0 < (k : ℝ) + 1
      positivity
    · change 0 < (k : ℝ) + 2
      positivity
    · exact_mod_cast (by omega : k + 1 ≤ k + 2)
  have htel (N : ℕ) :
      (∑ k ∈ range N,
          (Real.log (k + 2) - Real.log (k + 1))) = Real.log (N + 1) := by
    induction N with
    | zero => norm_num
    | succ N ih =>
        rw [sum_range_succ, ih]
        push_cast
        ring
  have hlognonneg (n : ℕ) : 0 ≤ Real.log ((n : ℝ) + 1) := by
    rw [← Nat.cast_one, ← Nat.cast_add]
    exact Real.log_natCast_nonneg (n + 1)
  rw [show (∑ k ∈ range M,
      (Real.log (k + 1) : ℂ) * χ.1 ((k + 1 : ℕ) : ZMod q)) =
      ∑ k ∈ range M, w k * f k by rfl,
    finite_summation_by_parts f w M]
  calc
    ‖w M * S M + ∑ k ∈ range M, (w k - w (k + 1)) * S (k + 1)‖
        ≤ ‖w M * S M‖ +
            ‖∑ k ∈ range M, (w k - w (k + 1)) * S (k + 1)‖ :=
      norm_add_le _ _
    _ ≤ Real.log (M + 1) * (2 * q) +
          ∑ k ∈ range M,
            (Real.log (k + 2) - Real.log (k + 1)) * (2 * q) := by
      apply add_le_add
      · rw [norm_mul, show ‖w M‖ = Real.log (M + 1) by
          simp [w, abs_of_nonneg (hlognonneg M)]]
        exact mul_le_mul_of_nonneg_left (hS M) (hlognonneg M)
      · refine le_trans (norm_sum_le _ _) ?_
        apply sum_le_sum
        intro k hk
        rw [norm_mul]
        have habs : ‖w k - w (k + 1)‖ =
            Real.log (k + 2) - Real.log (k + 1) := by
          have hwk1 : w (k + 1) = (Real.log ((k : ℝ) + 2) : ℂ) := by
            simp only [w, Nat.cast_add, Nat.cast_one]
            congr 2 <;> ring
          rw [show w k = (Real.log ((k : ℝ) + 1) : ℂ) by rfl, hwk1,
            ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
          rw [abs_of_nonpos (sub_nonpos.mpr (hwmono k))]
          ring
        rw [habs]
        exact mul_le_mul_of_nonneg_left (hS (k + 1)) (sub_nonneg.mpr (hwmono k))
    _ = Real.log (M + 1) * (2 * q) + Real.log (M + 1) * (2 * q) := by
      rw [← sum_mul, htel]
    _ = 4 * q * Real.log (M + 1) := by ring

/-- The same logarithmic-weight estimate in the conventional `1 ≤ m ≤ M`
form. -/
theorem primitiveCharacter_logWeight_Icc_norm_le {q M : ℕ} (hq : 1 < q)
    (χ : PrimitiveCharacter q) :
    ‖∑ m ∈ Icc 1 M, (Real.log m : ℂ) * χ.1 (m : ZMod q)‖
      ≤ 4 * q * Real.log (M + 1) := by
  by_cases hM : M = 0
  · subst M
    simp
  · have hMpos : 0 < M := Nat.pos_of_ne_zero hM
    have hsets : Icc 1 M = Ico 1 (M + 1) := by
      ext m
      simp
    rw [hsets, ← shifted_prefix_eq_Ico
      (fun m : ℕ => (Real.log m : ℂ) * χ.1 (m : ZMod q)) M]
    simpa only [Nat.cast_add, Nat.cast_one] using
      primitiveCharacter_logWeight_range_norm_le hq χ

end

end AnalyticNumberTheory.LargeSieve
