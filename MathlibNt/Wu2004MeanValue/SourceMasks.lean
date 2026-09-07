import MathlibNt.Wu2004MeanValue.ActualAP

/-! Exact source splitting. The split exponent need not equal the final
modulus-level exponent subsequently chosen by the small-source theorem. -/

namespace Wu2004MeanValue

open Classical Finset
open scoped BigOperators

noncomputable section

def sourceMask (S : Finset ℕ) (f : ℕ → ℝ) (m : ℕ) : ℝ :=
  if m ∈ S then f m else 0

theorem abs_sourceMask_le (S : Finset ℕ) (f : ℕ → ℝ) (F : ℝ)
    (hF : 0 ≤ F) (hf : ∀ m ∈ S, |f m| ≤ F) (m : ℕ) :
    |sourceMask S f m| ≤ F := by
  by_cases hm : m ∈ S
  · simpa only [sourceMask, if_pos hm] using hf m hm
  · simpa only [sourceMask, if_neg hm, abs_zero] using hF

theorem actualAPSum_split_source (S : Finset ℕ) (f r : ℕ → ℝ)
    (L U d b : ℕ) (hS : S ⊆ Icc 1 U) :
    actualAPSum S f r d b =
      actualAPSum (S.filter (fun m => m ≤ L)) f r d b +
        actualAPSum (Ioc L U) (sourceMask S f) r d b := by
  have hhigh : actualAPSum (S.filter (fun m => ¬ m ≤ L)) f r d b =
      actualAPSum (Ioc L U) (sourceMask S f) r d b := by
    have hsub : S.filter (fun m => ¬ m ≤ L) ⊆ Ioc L U := by
      intro m hm
      obtain ⟨hmS, hmL⟩ := mem_filter.mp hm
      exact mem_Ioc.mpr ⟨by omega, (mem_Icc.mp (hS hmS)).2⟩
    unfold actualAPSum
    calc
      _ = ∑ m ∈ S.filter (fun m => ¬ m ≤ L),
          if m.Coprime d then sourceMask S f m * ebar ((m : ℝ) * r m) d b m else 0 := by
        apply sum_congr rfl
        intro m hm
        rw [sourceMask, if_pos (mem_filter.mp hm).1]
      _ = _ := by
        apply sum_subset hsub
        intro m hm hn
        have hmS : m ∉ S := by
          intro h
          exact hn (mem_filter.mpr ⟨h, by have := (mem_Ioc.mp hm).1; omega⟩)
        simp only [sourceMask, if_neg hmS, zero_mul, ite_self]
  rw [← hhigh]
  unfold actualAPSum
  rw [sum_filter, sum_filter]
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro m _
  by_cases hm : m ≤ L <;> simp [hm]

theorem sourceMask_endpoint_extension (S : Finset ℕ) (f r : ℕ → ℝ)
    (x : ℝ) (hS : ∀ m ∈ S, 0 ≤ r m ∧ (m : ℝ) * r m ≤ x)
    (hx : 0 ≤ x) :
    (∀ m, 0 ≤ (if m ∈ S then r m else 0) ∧
      (m : ℝ) * (if m ∈ S then r m else 0) ≤ x) ∧
    ∀ T d b, actualAPSum T (sourceMask S f) (fun m => if m ∈ S then r m else 0) d b =
      actualAPSum T (sourceMask S f) r d b := by
  constructor
  · intro m
    by_cases hm : m ∈ S
    · simpa only [if_pos hm] using hS m hm
    · simp only [if_neg hm, mul_zero]
      exact ⟨le_rfl, hx⟩
  · intro T d b
    unfold actualAPSum
    apply sum_congr rfl
    intro m _
    by_cases hm : m ∈ S
    · simp only [if_pos hm]
    · simp only [sourceMask, if_neg hm, zero_mul, ite_self]

theorem ceil_log_source_cutoff (x b : ℝ) (hlog : 2 ≤ Real.log x) (hb : 0 ≤ b) :
    Real.log x ^ (2 * b) ≤ (⌈Real.log x ^ (2 * b)⌉₊ : ℝ) ∧
      (⌈Real.log x ^ (2 * b)⌉₊ : ℝ) ≤ Real.log x ^ (2 * b + 1) := by
  have hlog0 : 0 < Real.log x := by linarith
  have hpow1 : 1 ≤ Real.log x ^ (2 * b) :=
    Real.one_le_rpow (by linarith) (by positivity)
  constructor
  · exact Nat.le_ceil _
  · calc
      _ ≤ Real.log x ^ (2 * b) + 1 := (Nat.ceil_lt_add_one (by positivity)).le
      _ ≤ 2 * Real.log x ^ (2 * b) := by linarith
      _ ≤ Real.log x ^ (2 * b) * Real.log x := by nlinarith
      _ = _ := by rw [Real.rpow_add hlog0, Real.rpow_one]

theorem legal_source_endpoint_extension (S : Finset ℕ) (f r : ℕ → ℝ)
    (x : ℝ) (hS : ∀ m ∈ S, 2 ≤ r m ∧ (m : ℝ) * r m ≤ x)
    (hx : 4 ≤ x) :
    (∀ m : ℕ, (m : ℝ) ≤ Real.sqrt x →
      2 ≤ (if m ∈ S then r m else 2) ∧
        (m : ℝ) * (if m ∈ S then r m else 2) ≤ x) ∧
    ∀ T d b, actualAPSum T (sourceMask S f) (fun m => if m ∈ S then r m else 2) d b =
      actualAPSum T (sourceMask S f) r d b := by
  constructor
  · intro m hm
    by_cases hmS : m ∈ S
    · simpa only [if_pos hmS] using hS m hmS
    · rw [if_neg hmS]
      have hx0 : 0 ≤ x := by linarith
      have hroot : 2 ≤ Real.sqrt x := (Real.le_sqrt (by norm_num) hx0).mpr (by norm_num; exact hx)
      have hsquare := Real.sq_sqrt hx0
      constructor
      · rfl
      · nlinarith
  · intro T d b
    unfold actualAPSum
    apply sum_congr rfl
    intro m _
    by_cases hm : m ∈ S
    · simp only [if_pos hm]
    · simp only [sourceMask, if_neg hm, zero_mul, ite_self]

end
end Wu2004MeanValue