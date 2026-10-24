import MathlibNt.Wu2004MeanValue.GammaFiveLossBudgetMeasurable
import MathlibNt.Wu2004MeanValue.GammaFiveLossBudget

/-!
# Triangular Gamma₅ loss budgets

The loss kernel vanishes at both support endpoints. On the two pieces, the
inequality `log x ≤ x - 1` gives affine upper bounds meeting at the same
height. Integrating these bounds halves the earlier rectangular estimate.

The four strict debits, including the second functional's factor 1/5, are
1/1500, 1/1000, 9/8000 and 1/2000. Actual count identities and the remaining
signed terms must still be supplied before these bounds can close Ξ₂.
-/

open Real Set MeasureTheory
open scoped Interval
namespace Wu2004MeanValue.GammaFiveLossBudget

theorem generalKernel_left_linear {S B v : ℝ}
    (hS : 0 < S) (hB : 1/3 ≤ B) (hBhi : B < 1/2)
    (hA : 5/4 ≤ S*(1-2*B))
    (hv : v ∈ Icc (S*(1-2*B)) (S*(1-B)/2)) :
    generalKernel S B v ≤ 12/(25*S*(1-B))*(v-S*(1-2*B)) := by
  have hB0 : 0 < B := by linarith
  have hB1 : 0 < 1-B := by linarith
  have he : v ≤ S/3 := by nlinarith [hv.2]
  obtain ⟨hp0,hp⟩ := kernel_prefactor_bounds hS (hA.trans hv.1) he
  have hvS : v/S ≤ (1-B)/2 := (div_le_iff₀ hS).mpr (by nlinarith [hv.2])
  have hd : 0 < 1-v/S-B := by linarith
  have hn : 0 ≤ v-S*(1-2*B) := sub_nonneg.mpr hv.1
  have hratio : B/(1-v/S-B)-1 = (v-S*(1-2*B))/(S*(1-v/S-B)) := by
    rw [div_sub_one hd.ne', div_mul_eq_div_div]
    congr 1
    field_simp
    ring
  have hden : S*(1-B)/2 ≤ S*(1-v/S-B) := by nlinarith
  have hc : (v-S*(1-2*B))/(S*(1-v/S-B)) ≤
      (v-S*(1-2*B))/(S*(1-B)/2) :=
    div_le_div_of_nonneg_left hn (by positivity) hden
  have hl := (Real.log_le_sub_one_of_pos (div_pos hB0 hd))
  rw [hratio] at hl
  have hlin0 : 0 ≤ (v-S*(1-2*B))/(S*(1-B)/2) := by positivity
  rw [generalKernel, if_pos (show S*(1-2*B) ≤ v ∧ v ≤ S*(1-B)/2 from hv)]
  have hm := (mul_le_mul_of_nonneg_left (hl.trans hc) hp0).trans
    (mul_le_mul_of_nonneg_right hp hlin0)
  calc
    _ ≤ ((6/5)*((v-S*(1-2*B))/(S*(1-B)/2)))/5 :=
      div_le_div_of_nonneg_right hm (by norm_num)
    _ = _ := by field_simp; ring

theorem generalKernel_right_linear {S B v : ℝ}
    (hS : 0 < S) (hB : 1/3 ≤ B) (hBhi : B < 1/2)
    (hA : 5/4 ≤ S*(1-2*B))
    (hv : v ∈ Icc (S*(1-B)/2) (S/3)) :
    generalKernel S B v ≤ 36/(25*S*(1-B))*(S/3-v) := by
  have hB1 : 0 < 1-B := by linarith
  have hmid : S*(1-2*B) ≤ S*(1-B)/2 := by nlinarith
  by_cases heq : v = S*(1-B)/2
  · subst v
    apply (generalKernel_upper hS hB hBhi hA _).trans_eq
    field_simp
    ring
  have hvc : S*(1-B)/2 < v := lt_of_le_of_ne hv.1 (Ne.symm heq)
  have hn : ¬ (S*(1-2*B) ≤ v ∧ v ≤ S*(1-B)/2) := by
    intro h
    linarith [h.2]
  by_cases hve : v < S/3
  · obtain ⟨hp0,hp⟩ := kernel_prefactor_bounds hS (hA.trans (hmid.trans hv.1)) hv.2
    have hv0 : 0 < v := lt_of_lt_of_le (by positivity : 0 < S*(1-B)/2) hv.1
    have hnum : 0 ≤ 3*(S/3-v) := by linarith
    have hratio : (S-2*v)/v-1 = 3*(S/3-v)/v := by field_simp; ring
    have hl := Real.log_le_sub_one_of_pos
      (div_pos (by linarith : 0 < S-2*v) hv0)
    rw [hratio] at hl
    have hc := div_le_div_of_nonneg_left hnum
      (by positivity : 0 < S*(1-B)/2) hv.1
    have hlin0 : 0 ≤ 3*(S/3-v)/(S*(1-B)/2) := by positivity
    rw [generalKernel, if_neg hn, if_pos ⟨hvc,hve⟩]
    have hm := (mul_le_mul_of_nonneg_left (hl.trans hc) hp0).trans
      (mul_le_mul_of_nonneg_right hp hlin0)
    calc
      _ ≤ ((6/5)*(3*(S/3-v)/(S*(1-B)/2)))/5 :=
        div_le_div_of_nonneg_right hm (by norm_num)
      _ = _ := by field_simp; ring
  · have he : v = S/3 := by linarith [hv.2]
    rw [generalKernel, if_neg hn, if_neg (by simp [hve]), he]
    simp

/-- The two linear bounds pay half the constant-height rectangle budget. -/
theorem general_weighted_triangle_bound {S B : ℝ}
    (hS : 0 < S) (hB : 1/3 ≤ B) (hBhi : B < 1/2)
    (hA : 5/4 ≤ S*(1-2*B)) (hE : S/3 ≤ 3)
    (H : ℝ → ℝ) (hH : ∀ v ∈ Icc (S*(1-2*B)) (S/3), 0 ≤ H v ∧ H v ≤ 1)
    (hi : IntervalIntegrable (fun v => H v * generalKernel S B v)
      volume (S*(1-2*B)) (S/3)) :
    (∫ v in (1 : ℝ)..3, H v * generalKernel S B v) ≤
      (3/25)*((3*B-1)/(1-B))*(S/3-S*(1-2*B)) := by
  let A := S*(1-2*B)
  let C := S*(1-B)/2
  let E := S/3
  have hAC : A ≤ C := by dsimp [A,C]; nlinarith
  have hCE : C ≤ E := by dsimp [C,E]; nlinarith
  have hAE := hAC.trans hCE
  have hiL := hi.mono_set (show uIcc A C ⊆ uIcc A E by
    rw [uIcc_of_le hAC,uIcc_of_le hAE]
    exact fun _ hv => ⟨hv.1,hv.2.trans hCE⟩)
  have hiR := hi.mono_set (show uIcc C E ⊆ uIcc A E by
    rw [uIcc_of_le hCE,uIcc_of_le hAE]
    exact fun _ hv => ⟨hAC.trans hv.1,hv.2⟩)
  have hl : (∫ v in A..C, H v * generalKernel S B v) ≤
      (12/(25*S*(1-B)))*(C-A)^2/2 := by
    calc
      _ ≤ ∫ v in A..C, (12/(25*S*(1-B)))*(v-A) := by
        apply intervalIntegral.integral_mono_on hAC hiL
          ((continuous_const.mul (continuous_id.sub continuous_const)).intervalIntegrable _ _)
        intro v hv
        exact (mul_le_of_le_one_left (generalKernel_nonneg hS hB hBhi v)
          (hH v ⟨hv.1,hv.2.trans hCE⟩).2).trans
          (generalKernel_left_linear hS hB hBhi hA hv)
      _ = _ := by
        rw [intervalIntegral.integral_const_mul,
          intervalIntegral.integral_sub (f := fun v : ℝ => v)
            (continuous_id.intervalIntegrable _ _) intervalIntegrable_const]
        simp only [integral_id,intervalIntegral.integral_const,smul_eq_mul]
        ring
  have hr : (∫ v in C..E, H v * generalKernel S B v) ≤
      (36/(25*S*(1-B)))*(E-C)^2/2 := by
    calc
      _ ≤ ∫ v in C..E, (36/(25*S*(1-B)))*(E-v) := by
        apply intervalIntegral.integral_mono_on hCE hiR
          ((continuous_const.mul (continuous_const.sub continuous_id)).intervalIntegrable _ _)
        intro v hv
        exact (mul_le_of_le_one_left (generalKernel_nonneg hS hB hBhi v)
          (hH v ⟨hAC.trans hv.1,hv.2⟩).2).trans
          (generalKernel_right_linear hS hB hBhi hA hv)
      _ = _ := by
        rw [intervalIntegral.integral_const_mul,
          intervalIntegral.integral_sub (g := fun v : ℝ => v)
            intervalIntegrable_const (continuous_id.intervalIntegrable _ _)]
        simp only [integral_id,intervalIntegral.integral_const,smul_eq_mul]
        ring
  have hs : Function.support (fun v => H v * generalKernel S B v) ⊆ Ioc A E := by
    intro v hv
    apply generalKernel_support hS hB hBhi
    intro he
    exact hv (by simp [he])
  have hs' : Function.support (fun v => H v * generalKernel S B v) ⊆ Ioc (1 : ℝ) 3 := by
    intro v hv
    obtain ⟨hl,hu⟩ := hs hv
    dsimp [A,E] at hl hu
    exact ⟨by linarith,hu.trans hE⟩
  rw [intervalIntegral.integral_eq_integral_of_support_subset hs',
    ← intervalIntegral.integral_eq_integral_of_support_subset hs,
    ← intervalIntegral.integral_add_adjacent_intervals hiL hiR]
  apply (add_le_add hl hr).trans_eq
  dsimp [A,C,E]
  have hB1 : 1-B ≠ 0 := by linarith
  field_simp
  ring

/-- All four row debits can be halved without assuming any stronger bound on H. -/
theorem original_row_triangle_budget (i : Fin 4) (H : ℝ → ℝ)
    (hH : ∀ v ∈ Icc ((rowParameters i).1*(1-2*(rowParameters i).2))
      ((rowParameters i).1/3), 0 ≤ H v ∧ H v ≤ 1)
    (hi : IntervalIntegrable (fun v => H v * generalKernel (rowParameters i).1
      (rowParameters i).2 v) volume ((rowParameters i).1*(1-2*(rowParameters i).2))
      ((rowParameters i).1/3)) :
    (∫ v in (1 : ℝ)..3, H v * generalKernel (rowParameters i).1
      (rowParameters i).2 v) < rowDebit i / 2 := by
  have hp : 0 < (rowParameters i).1 ∧ 1/3 ≤ (rowParameters i).2 ∧
      (rowParameters i).2 < 1/2 ∧ 5/4 ≤ (rowParameters i).1*(1-2*(rowParameters i).2) ∧
      (rowParameters i).1/3 ≤ 3 := by
    fin_cases i <;> norm_num [rowParameters]
  apply (general_weighted_triangle_bound hp.1 hp.2.1 hp.2.2.1 hp.2.2.2.1
    hp.2.2.2.2 H hH hi).trans_lt
  fin_cases i <;> norm_num [rowParameters,rowDebit]

/-- Fourth-row specialization, including the one-fifth normalization. -/
theorem fourth_row_triangle_budget (H : ℝ → ℝ)
    (hH : ∀ v ∈ Icc (9373/7275 : ℝ) (103/75), 0 ≤ H v ∧ H v ≤ 1)
    (hi : IntervalIntegrable (fun v => H v * kernel v) volume (9373/7275) (103/75)) :
    (∫ v in (1 : ℝ)..3, H v * kernel v) < 1/2000 := by
  rw [kernel_eq_general] at hi ⊢
  have h := original_row_triangle_budget (3 : Fin 4) H
  rw [show rowParameters (3 : Fin 4) = ((103/25 : ℝ), (100/291 : ℝ)) from rfl,
    show rowDebit (3 : Fin 4) = (1/1000 : ℝ) from rfl] at h
  norm_num only [Prod.fst, Prod.snd] at h
  exact h hH hi

end Wu2004MeanValue.GammaFiveLossBudget
