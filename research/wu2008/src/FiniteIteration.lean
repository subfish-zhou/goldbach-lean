import FeedbackSystem

namespace ActualNineFeedback
open Wu2008DoubleSieve NodeExtension
open scoped BigOperators

noncomputable def matrixApply {m n : ℕ} (M : Fin m → Fin n → ℝ)
    (z : Fin n → ℝ) (i : Fin m) : ℝ := ∑ k, M i k * z k

 theorem matrixApply_nonneg {m n : ℕ} {M : Fin m → Fin n → ℝ}
    (hM : ∀ i k, 0 ≤ M i k) {z : Fin n → ℝ} (hz : ∀ k, 0 ≤ z k) (i : Fin m) :
    0 ≤ matrixApply M z i :=
  Finset.sum_nonneg (fun k _ => mul_nonneg (hM i k) (hz k))

 theorem matrixApply_mono {m n : ℕ} {M : Fin m → Fin n → ℝ}
    (hM : ∀ i k, 0 ≤ M i k) {x y : Fin n → ℝ} (hxy : ∀ k, x k ≤ y k) (i : Fin m) :
    matrixApply M x i ≤ matrixApply M y i :=
  Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_left (hxy k) (hM i k))

 theorem matrixApply_sub_mul {m n : ℕ} (M : Fin m → Fin n → ℝ)
    (x y : Fin n → ℝ) (a : ℝ) (i : Fin m) :
    matrixApply M (fun k => x k - a * y k) i =
      matrixApply M x i - a * matrixApply M y i := by
  simp only [matrixApply, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  ring

noncomputable def lowerIterate : ℕ → Fin 9 → ℝ
  | 0 => fun _ => 0
  | n + 1 => fun i => max 0 (base i + matrixApply feedbackMatrix (lowerIterate n) i)

noncomputable def debitIterate : ℕ → Fin 9 → ℝ
  | 0 => fun _ => 0
  | n + 1 => fun i => loss i + matrixApply feedbackMatrix (debitIterate n) i

 theorem lowerIterate_nonneg (n : ℕ) (i : Fin 9) : 0 ≤ lowerIterate n i := by
  cases n with
  | zero => exact le_rfl
  | succ n => exact le_max_left _ _

 theorem debitIterate_nonneg (n : ℕ) (i : Fin 9) : 0 ≤ debitIterate n i := by
  induction n generalizing i with
  | zero => exact le_rfl
  | succ n ih =>
    exact add_nonneg (loss_nonneg i)
      (matrixApply_nonneg feedbackMatrix_nonneg ih i)

 theorem lowerIterate_step (n : ℕ) : ∀ i, lowerIterate n i ≤ lowerIterate (n + 1) i := by
  induction n with
  | zero => exact lowerIterate_nonneg 1
  | succ n ih =>
    intro i
    exact max_le_max le_rfl (add_le_add_right (matrixApply_mono feedbackMatrix_nonneg ih i) _)

 theorem debitIterate_step (n : ℕ) : ∀ i, debitIterate n i ≤ debitIterate (n + 1) i := by
  induction n with
  | zero => exact debitIterate_nonneg 1
  | succ n ih =>
    intro i
    exact add_le_add_right (matrixApply_mono feedbackMatrix_nonneg ih i) _

 theorem lowerIterate_monotone (i : Fin 9) : Monotone (fun n => lowerIterate n i) :=
  monotone_nat_of_le_succ (fun n => lowerIterate_step n i)

 theorem debitIterate_monotone (i : Fin 9) : Monotone (fun n => debitIterate n i) :=
  monotone_nat_of_le_succ (fun n => debitIterate_step n i)

/-- Every finite symbolic iterate bounds the genuine nine nodes. -/
 theorem finite_actual_nine {δ : ℝ} (hd : 0 < δ) (hh : δ ≤ 1 / 10) (n : ℕ) :
    ∀ i, lowerIterate n i - deltaLoss δ * debitIterate n i ≤ actualNine δ i := by
  have hz := actualNine_nonneg hd hh
  have hl := deltaLoss_nonneg hd hh
  induction n with
  | zero => simpa only [lowerIterate, debitIterate, mul_zero, sub_zero] using hz
  | succ n ih =>
    intro i
    have hm := matrixApply_mono feedbackMatrix_nonneg ih i
    rw [matrixApply_sub_mul] at hm
    have hs := (actual_nine_system hd hh).2.2.2.1 i
    change base i - deltaLoss δ * loss i +
      matrixApply feedbackMatrix (actualNine δ) i ≤ actualNine δ i at hs
    change max 0 (base i + matrixApply feedbackMatrix (lowerIterate n) i) -
      deltaLoss δ * (loss i + matrixApply feedbackMatrix (debitIterate n) i) ≤ _
    by_cases hp : 0 ≤ base i + matrixApply feedbackMatrix (lowerIterate n) i
    · rw [max_eq_right hp]
      nlinarith only [hm, hs]
    · rw [max_eq_left (le_of_not_ge hp)]
      have hn := mul_nonneg hl (debitIterate_nonneg (n + 1) i)
      change 0 ≤ deltaLoss δ * (loss i + matrixApply feedbackMatrix (debitIterate n) i) at hn
      linarith only [hn, hz i]

/-- Transfer to the original twenty-one actual lower-improvement nodes. -/
 theorem finite_actual_twentyone {δ : ℝ} (hd : 0 < δ) (hh : δ ≤ 1 / 10)
    (n : ℕ) (j : Fin 21) :
    matrixApply transferMatrix (lowerIterate n) j -
      deltaLoss δ * matrixApply transferMatrix (debitIterate n) j ≤
        wuImprovementLimit false δ (rNode (j.val + 1)) := by
  have hm := matrixApply_mono transferMatrix_nonneg (finite_actual_nine hd hh n) j
  rw [matrixApply_sub_mul] at hm
  exact hm.trans (actual_twentyone_matrix hd hh j)

end ActualNineFeedback
