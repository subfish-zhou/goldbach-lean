import FiniteIteration

namespace FiniteFeedbackComparison
open ActualNineFeedback
open scoped BigOperators
noncomputable section

theorem matrixApply_scale {n : ℕ} (M : Fin n → Fin n → ℝ) (r : ℝ) (z : Fin n → ℝ) (i : Fin n) :
    matrixApply M (fun k => r*z k) i = r*matrixApply M z i := by
  simp only [matrixApply,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- Genuine positive forcing propagates through the retained terminal feedback. -/
theorem supersolution_pos {n : ℕ} {M : Fin n → Fin n → ℝ}
    (e a : Fin n) (ha : a ≠ e) (hM : ∀ i k, 0 ≤ M i k) (hlink : 0 < M e a)
    {b z : Fin n → ℝ}
    (hb : ∀ i,0≤b i) (hbp : ∀ i : Fin n,i≠e → 0<b i)
    (hz : ∀ i,0≤z i) (hs : ∀ i,b i+matrixApply M z i≤z i) :
    ∀ i,0<z i := by
  have hn i := matrixApply_nonneg hM hz i
  have h0 : 0<z a := (lt_add_of_pos_of_le (hbp a ha) (hn a)).trans_le (hs a)
  intro i
  by_cases hi : i=e
  · subst i
    have hterm : M e a*z a ≤ matrixApply M z e :=
      Finset.single_le_sum (fun k _ => mul_nonneg (hM e k) (hz k))
        (Finset.mem_univ a)
    exact (mul_pos hlink h0).trans_le
      (hterm.trans ((le_add_of_nonneg_left (hb e)).trans (hs e)))
  · exact (lt_add_of_pos_of_le (hbp i hi) (hn i)).trans_le (hs i)

/-- Maximum-ratio comparison with one possibly zero forcing entry.
A positive matrix link from that entry to a positive-forcing entry closes the strict comparison. -/
theorem subsolution_le_supersolution {n : ℕ} {M : Fin n → Fin n → ℝ}
    (e a : Fin n) (ha : a ≠ e) (hM : ∀ i k, 0 ≤ M i k) (hlink : 0 < M e a)
    {b x z : Fin n → ℝ}
    (hb : ∀ i,0≤b i) (hbp : ∀ i : Fin n,i≠e → 0<b i)
    (hz : ∀ i,0≤z i)
    (hx : ∀ i,x i≤b i+matrixApply M x i)
    (hs : ∀ i,b i+matrixApply M z i≤z i) : ∀ i,x i≤z i := by
  classical
  have hp := supersolution_pos e a ha hM hlink hb hbp hz hs
  obtain ⟨j,_,hj⟩ := Finset.exists_max_image Finset.univ (fun i : Fin n => x i/z i) ⟨a, Finset.mem_univ a⟩
  let r : ℝ := x j/z j
  have hall : ∀ i,x i≤r*z i := by
    intro i
    exact (div_le_iff₀ (hp i)).mp (hj i (Finset.mem_univ i))
  have he : x j=r*z j := (div_mul_cancel₀ (x j) (ne_of_gt (hp j))).symm
  have hr : r≤1 := by
    by_contra h
    have hr1 : 1<r := lt_of_not_ge h
    have hr0 : 0≤r := by linarith only [hr1]
    have hm (i : Fin n) : matrixApply M x i≤r*matrixApply M z i := by
      rw [← matrixApply_scale]
      exact matrixApply_mono hM hall i
    have hstrict (i : Fin n) (hi : i≠e) : x i<r*z i := by
      have hbi := hbp i hi
      have hprod := mul_pos (sub_pos.mpr hr1) hbi
      have hscaled := mul_le_mul_of_nonneg_left (hs i) hr0
      nlinarith only [hx i,hm i,hscaled,hprod]
    by_cases hje : j=e
    · have hme : matrixApply M x e<r*matrixApply M z e := by
        rw [← matrixApply_scale]
        apply Finset.sum_lt_sum
        · intro k _
          exact mul_le_mul_of_nonneg_left (hall k) (hM e k)
        · exact ⟨a,Finset.mem_univ a,mul_lt_mul_of_pos_left (hstrict a ha) hlink⟩
      have hscaled := mul_le_mul_of_nonneg_left (hs e) hr0
      have hprod := mul_nonneg (sub_nonneg.mpr hr1.le) (hb e)
      rw [hje] at he
      nlinarith only [hx e,hme,hscaled,hprod,he]
    · exact (hstrict j hje).ne he
  intro i
  exact (hall i).trans (by nlinarith only [hr,hz i])

end
end FiniteFeedbackComparison
