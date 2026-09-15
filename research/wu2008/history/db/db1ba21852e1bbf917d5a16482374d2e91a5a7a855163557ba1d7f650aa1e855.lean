import DirectLoss

namespace WuTarget.W03
open Set MeasureTheory QuarterTrim DirectFiniteF6 ActualNineFeedback NodeExtension
open scoped Classical BigOperators
noncomputable section

def basis (j k : Fin 21) : ℝ := if k = j then 1 else 0

theorem basis_nonneg (j k : Fin 21) : 0 ≤ basis j k := by
  unfold basis
  split_ifs <;> norm_num

theorem eval_expansion (L : List (Fin 21)) (w : Fin 21 → ℝ) (s : ℝ) :
    Wu08Staircase.eval (L.map (row w)) s =
      ∑ j : Fin 21, w j * Wu08Staircase.eval (L.map (row (basis j))) s := by
  induction L with
  | nil => simp [Wu08Staircase.eval]
  | cons k L ih =>
    simp only [List.map_cons, row, Wu08Staircase.eval]
    by_cases h : (originalRow k).1 < s ∧ s ≤ (originalRow k).2.1
    · simp [h, basis]
    · simpa only [if_neg h] using ih

theorem profile_expansion (w : Fin 21 → ℝ) (s : ℝ) :
    profile w s = ∑ j : Fin 21, w j * profile (basis j) s :=
  eval_expansion _ w s

theorem uniform_expansion (w : Fin 21 → ℝ) (t : ℝ) (v : ℝ × ℝ) :
    uniform w t v = ∑ j : Fin 21, w j * uniform (basis j) t v := by
  unfold uniform
  by_cases h : v ∈ StaircaseShrink.domain t
  · simp only [if_pos h, kernel, profile_expansion w, Finset.sum_div]
    simp only [mul_div_assoc]
  · simp [h]

def weight (j : Fin 21) : ℝ := Gamma (basis j) 0

theorem weight_nonneg (j : Fin 21) : 0 ≤ weight j :=
  Gamma_nonneg (basis_nonneg j) le_rfl

theorem Gamma_expansion (w : Fin 21 → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    Gamma w t = ∑ j : Fin 21, Gamma (basis j) t * w j := by
  unfold Gamma
  simp_rw [uniform_expansion w]
  rw [integral_finset_sum _ (fun j _ => (uniform_integrable (basis j) ht).const_mul (w j))]
  simp only [integral_const_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem Gamma_eq_weights (w : Fin 21 → ℝ) :
    Gamma w 0 = ∑ j : Fin 21, weight j * w j :=
  Gamma_expansion w le_rfl

theorem lower_weights_consumer {q w : Fin 21 → ℝ}
    (hq : ∀ j, q j ≤ weight j) (hw : ∀ j, 0 ≤ w j) :
    (∑ j : Fin 21, q j * w j) ≤ Gamma w 0 := by
  rw [Gamma_eq_weights]
  exact Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_right (hq j) (hw j))

theorem originalRow_left (j : Fin 21) : (originalRow j).1 = rNode j.val := by
  fin_cases j <;> norm_num [originalRow, Wu08Staircase.table, rNode]

def cell (j : Fin 21) (s : ℝ) : Prop :=
  rNode j.val < s ∧ s ≤ rNode (j.val + 1)

theorem cell_unique {i j : Fin 21} {s : ℝ} (hi : cell i s) (hj : cell j s) :
    i = j := by
  apply Fin.ext
  have h1 : ¬ i.val < j.val := by
    intro h
    exact (not_lt_of_ge (hi.2.trans (rNode_mono (show i.val + 1 ≤ j.val by omega)))) hj.1
  have h2 : ¬ j.val < i.val := by
    intro h
    exact (not_lt_of_ge (hj.2.trans (rNode_mono (show j.val + 1 ≤ i.val by omega)))) hi.1
  omega

theorem eval_basis (L : List (Fin 21)) (j : Fin 21) (s : ℝ) :
    Wu08Staircase.eval (L.map (row (basis j))) s =
      if j ∈ L ∧ cell j s then 1 else 0 := by
  induction L with
  | nil => simp [Wu08Staircase.eval]
  | cons k L ih =>
    simp only [List.map_cons, row, Wu08Staircase.eval, originalRow_left, originalRow_node]
    change (if cell k s then basis j k else _) = _
    by_cases hk : cell k s
    · rw [if_pos hk]
      by_cases hkj : k = j
      · subst k
        simp [basis, hk]
      · have hj : ¬ cell j s := fun hj => hkj (cell_unique hk hj)
        simp [basis, hkj, hj]
    · rw [if_neg hk, ih]
      by_cases hkj : k = j
      · subst k
        simp [hk]
      · simp [List.mem_cons, Ne.symm hkj]

theorem profile_basis (j : Fin 21) (s : ℝ) :
    profile (basis j) s = if cell j s then 1 else 0 := by
  simpa only [List.mem_finRange, true_and] using eval_basis (List.finRange 21) j s

theorem uniform_basis (j : Fin 21) (v : ℝ × ℝ) :
    uniform (basis j) 0 v =
      if v ∈ StaircaseShrink.domain 0 ∧ cell j (u v.1 v.2)
      then 1 / (v.1 * v.2 * (1/2-v.1-v.2)) else 0 := by
  simp only [uniform, kernel, profile_basis]
  split_ifs <;> simp_all

theorem weight_integral (j : Fin 21) :
    weight j = 4 * ∫ v : ℝ × ℝ,
      if v ∈ StaircaseShrink.domain 0 ∧ cell j (u v.1 v.2)
      then 1 / (v.1 * v.2 * (1/2-v.1-v.2)) else 0 := by
  simp only [weight, Gamma, uniform_basis]

end
end WuTarget.W03
