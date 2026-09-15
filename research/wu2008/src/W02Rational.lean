import W02Transfer
import Wu04BypassActual

namespace WuTarget.W02
open NodeExtension ActualNineFeedback
open scoped BigOperators

def qNode (i : ℕ) : ℚ := 2 + (i : ℚ) / 10

def qUpper (k : Fin 9) : ℚ := (22 + (k.val : ℚ)) / 10

def qLeft (k : Fin 9) : ℚ := if k.val = 0 then 1 else (21 + (k.val : ℚ)) / 10

def qTail (S : ℚ) (k : Fin 9) : ℚ :=
  let a := max (qLeft k) (S - 2)
  let b := qUpper k
  if a ≤ b then (b - a) * (a + b - 2 * (S - 2)) / (2 * b * (b + 1)) else 0

def qPaid (i : ℕ) (k : Fin 9) : ℚ :=
  if 2 ≤ i ∧ i ≤ 10 then (if i - 2 = k.val then 1 else 0) else qTail (qNode i) k

def qLogLower (a b : ℚ) : ℚ := (b - a) / b

def qMatrix (j : Fin 21) (k : Fin 9) : ℚ :=
  (if k.val = 0 then 1 else 0) *
      qLogLower (qNode (j.val + 1) - 1) (qNode (gridStart (j.val + 1))) +
    ∑ i ∈ gridIndices j, qPaid i k * qLogLower (qNode (i - 1)) (qNode i)

def qV8 : Fin 9 → ℚ :=
  ![8039587/500000000, 7748071/500000000, 14133223/1000000000,
    12015063/1000000000, 2111073/200000000, 79677/10000000,
    5286731/1000000000, 129933/40000000, 1412473/500000000]

def qOutput (j : Fin 21) : ℚ := ∑ k : Fin 9, qMatrix j k * qV8 k

theorem qNode_cast (i : ℕ) : (qNode i : ℝ) = rNode i := by
  simp [qNode, rNode]

theorem qUpper_cast (k : Fin 9) : (qUpper k : ℝ) = upperNode k := by
  simp [qUpper, upperNode]

theorem qLeft_cast (k : Fin 9) : (qLeft k : ℝ) = upperLeft k := by
  by_cases hk : k.val = 0 <;> simp [qLeft, upperLeft, hk]

theorem qTail_cast (S : ℚ) (k : Fin 9) : (qTail S k : ℝ) = tailCell S k := by
  unfold qTail tailCell tailLeft Wu04Bypass.cell
  have he : max (qLeft k) (S - 2) ≤ qUpper k ↔
      max (upperLeft k) ((S : ℝ) - 2) ≤ upperNode k := by
    rw [← qLeft_cast, ← qUpper_cast]
    exact_mod_cast Iff.rfl
  by_cases h : max (qLeft k) (S - 2) ≤ qUpper k
  · simp only [if_pos h, if_pos (he.mp h)]
    push_cast
    rw [qLeft_cast, qUpper_cast]
  · simp only [if_neg h, if_neg (mt he.mpr h), Rat.cast_zero]

theorem qPaid_cast (i : ℕ) (k : Fin 9) : (qPaid i k : ℝ) = paidNode i k := by
  by_cases h : 2 ≤ i ∧ i ≤ 10
  · simp only [qPaid, paidNode, if_pos h, dif_pos h, nodeBasis]
    have he : (⟨i - 2, by omega⟩ : Fin 9) = k ↔ i - 2 = k.val := Fin.ext_iff
    by_cases hk : i - 2 = k.val <;> simp [he, hk]
  · simp [qPaid, paidNode, h, qTail_cast, qNode_cast]

theorem qLogLower_cast (a b : ℚ) : (qLogLower a b : ℝ) = logLower a b := by
  simp [qLogLower, logLower]

theorem qMatrix_cast (j : Fin 21) (k : Fin 9) : (qMatrix j k : ℝ) = rationalMatrix j k := by
  unfold qMatrix rationalMatrix
  simp only [Rat.cast_add, Rat.cast_mul, Rat.cast_sum, qLogLower_cast, qPaid_cast,
    Rat.cast_sub, Rat.cast_one, qNode_cast]
  have he : (0 : Fin 9) = k ↔ k.val = 0 := by
    rw [eq_comm, Fin.ext_iff]
    rfl
  by_cases hk : k.val = 0 <;> simp [nodeBasis, he, hk]

theorem qV8_cast (k : Fin 9) : (qV8 k : ℝ) = Wu04Bypass.v8 k := by
  fin_cases k <;> norm_num [qV8, Wu04Bypass.v8]

theorem qOutput_cast (j : Fin 21) :
    (qOutput j : ℝ) = matrixApply rationalMatrix Wu04Bypass.v8 j := by
  simp [qOutput, matrixApply, qMatrix_cast, qV8_cast]

theorem qMatrix_nonneg (j : Fin 21) (k : Fin 9) : 0 ≤ qMatrix j k := by
  have h := rationalMatrix_nonneg j k
  rw [← qMatrix_cast] at h
  exact_mod_cast h

theorem qMatrix_le_transfer (j : Fin 21) (k : Fin 9) :
    (qMatrix j k : ℝ) ≤ transferMatrix j k := by
  rw [qMatrix_cast]
  exact rationalMatrix_le_transferMatrix j k

theorem apply_lower {z : Fin 9 → ℝ} (hz : ∀ k, 0 ≤ z k) (j : Fin 21) :
    matrixApply rationalMatrix z j ≤ matrixApply transferMatrix z j :=
  Finset.sum_le_sum (fun k _ =>
    mul_le_mul_of_nonneg_right (rationalMatrix_le_transferMatrix j k) (hz k))

theorem apply_lower_keeps_sigma {z : Fin 9 → ℝ} (hz : ∀ k, 0 ≤ z k) (j : Fin 21) :
    matrixApply rationalMatrix z j + aProfile (nineProfile z) * sigmaWeight j ≤
      matrixApply transferMatrix z j := by
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun k _ =>
    mul_le_mul_of_nonneg_right (rationalMatrix_lower_keeps_sigma j k) (hz k))
  rw [aProfile_expansion]
  simp only [matrixApply, add_mul, Finset.sum_add_distrib, Finset.sum_mul] at hh ⊢
  simpa only [mul_comm, mul_left_comm, mul_assoc] using hh

theorem v8_output_le_transfer (j : Fin 21) :
    (qOutput j : ℝ) ≤ matrixApply transferMatrix Wu04Bypass.v8 j := by
  rw [qOutput_cast]
  exact apply_lower Wu04Bypass.v8_nonneg j

theorem v8_output_keeps_sigma (j : Fin 21) :
    (qOutput j : ℝ) + aProfile (nineProfile Wu04Bypass.v8) * sigmaWeight j ≤
      matrixApply transferMatrix Wu04Bypass.v8 j := by
  rw [qOutput_cast]
  exact apply_lower_keeps_sigma Wu04Bypass.v8_nonneg j

theorem v8_rational_actual : ∃ d : ℝ, 0 < d ∧ d ≤ 1/10 ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ d →
      (∀ i : Fin 9, Wu04Bypass.v8 i ≤ actualNine δ i) ∧
      (∀ j : Fin 21, (qOutput j : ℝ) ≤
        Wu2008DoubleSieve.wuImprovementLimit false δ (rNode (j.val + 1))) ∧
      (∀ j : Fin 21, (qOutput j : ℝ) +
          aProfile (nineProfile Wu04Bypass.v8) * sigmaWeight j ≤
        Wu2008DoubleSieve.wuImprovementLimit false δ (rNode (j.val + 1))) := by
  obtain ⟨d, hd, hcap, hh⟩ := Wu04Bypass.new_nine_and_twentyone_actual
  refine ⟨d, hd, hcap, ?_⟩
  intro δ hδ hr
  have hs := hh δ hδ hr
  exact ⟨hs.1, fun j => (v8_output_le_transfer j).trans (hs.2 j),
    fun j => (v8_output_keeps_sigma j).trans (hs.2 j)⟩

end WuTarget.W02
