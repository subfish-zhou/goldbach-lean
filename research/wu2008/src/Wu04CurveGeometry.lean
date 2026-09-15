import Wu04RecoverPaid

namespace Wu04CurveGeometry
open Wu2008DoubleSieve Set MeasureTheory Real
open SecondFunctionalParameters SecondFunctionalPositive SecondFunctionalJointTail SecondFunctionalFourSevenths
open Wu04RecoverRectangle
noncomputable section

/-- Forced endpoint on the original lower z face. -/
def rc : ℝ := (2-b-c)/4
/-- The open v face prevents any double payment with the old rectangle. -/
def T : Set (Fin 3 → ℝ) := {t | a≤t 0 ∧ t 0≤b ∧ r<t 1 ∧ t 1≤rc ∧
  c≤t 2 ∧ t 2≤2-b-4*t 1}

theorem geometry : 0<a ∧ a≤b ∧ b<r ∧ r<rc ∧ rc<c ∧ c<f := by
  norm_num [a,b,c,f,r,rc,row1]

theorem T_measurable : MeasurableSet T := by
  unfold T
  exact (measurableSet_le measurable_const (measurable_pi_apply 0)).inter
    ((measurableSet_le (measurable_pi_apply 0) measurable_const).inter
    ((measurableSet_lt measurable_const (measurable_pi_apply 1)).inter
    ((measurableSet_le (measurable_pi_apply 1) measurable_const).inter
    ((measurableSet_le measurable_const (measurable_pi_apply 2)).inter
    (measurableSet_le (measurable_pi_apply 2)
      ((measurable_const.sub measurable_const).sub (measurable_const.mul (measurable_pi_apply 1))))))))

theorem T_subset : T ⊆ LowerTripleContinuous.D (1/row1.S) (1/row1.kappa1)
    (1/row1.kappa2) (1/row1.kappa3) (1/row1.s) 3 := by
  intro t ht
  obtain ⟨h0,h0',h1,h1',h2,h2'⟩ := ht
  change a≤t 0 ∧ t 0≤b ∧ b≤t 1 ∧ t 1≤c ∧ c≤t 2 ∧ t 2≤f ∧ t 0≤t 1 ∧ t 1≤t 2
  have hb : b≤t 1 := (geometry.2.2.1.trans h1).le
  have hc : t 1≤c := h1'.trans geometry.2.2.2.2.1.le
  have hf : t 2≤f := by unfold r at h1; linarith
  exact ⟨h0,h0',hb,hc,h2,hf,h0'.trans hb,hc.trans h2⟩

theorem T_cube : T ⊆ continuousCube 3 :=
  T_subset.trans (LowerTripleContinuous.D_subset_cube (original_compact 0) 3)

theorem T_argument {phi : ℝ} (hphi : 2≤phi) {t : Fin 3 → ℝ} (ht : t∈T) :
    3≤(phi-(t 0+t 1+t 2))/t 1 := by
  have hp : 0<t 1 := by linarith [(T_cube ht 1 (mem_univ 1)).1]
  apply (le_div_iff₀ hp).2
  obtain ⟨_,hx,_,_,_,hz⟩ := ht
  linarith

theorem R_T_disjoint : Disjoint Wu04RecoverRectangle.R T := by
  apply Set.disjoint_left.mpr
  intro t hr ht
  exact (not_lt_of_ge (R_literal.mp hr).2.2.2.1) ht.2.2.1

/-- Original density includes the selected coordinate twice. -/
theorem weight_literal (t : Fin 3 → ℝ) :
    geometricWeight 1 t = 1/(t 0*(t 1)^2*t 2) := by
  simp [geometricWeight,continuousDensity,Fin.prod_univ_succ]
  ring

theorem weight_lower {t : Fin 3 → ℝ} (ht : t∈T) :
    1/(b*rc^2*f) ≤ geometricWeight 1 t := by
  have hc := T_cube ht
  have h0 : 0<t 0 := by linarith [(hc 0 (mem_univ 0)).1]
  have h1 : 0<t 1 := by linarith [(hc 1 (mem_univ 1)).1]
  have h2 : 0<t 2 := by linarith [(hc 2 (mem_univ 2)).1]
  have ht' := T_subset ht
  have hz : t 2≤f := ht'.2.2.2.2.2.1
  rw [weight_literal]
  apply one_div_le_one_div_of_le (mul_pos (mul_pos h0 (sq_pos_of_pos h1)) h2)
  have hs : (t 1)^2 ≤ rc^2 := (sq_le_sq₀ h1.le (by norm_num [rc,b,c,row1])).mpr ht.2.2.2.1
  exact mul_le_mul (mul_le_mul ht.2.1 hs (sq_nonneg _) (by norm_num [b,row1]))
    hz h2.le (mul_nonneg (by norm_num [b,row1]) (sq_nonneg rc))

end
end Wu04CurveGeometry
