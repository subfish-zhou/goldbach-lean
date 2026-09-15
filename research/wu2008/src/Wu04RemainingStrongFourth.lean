import Wu04RemainingStrongGammaMass

namespace Wu04RemainingStrongFourth
open Wu2008DoubleSieve Set MeasureTheory Real Wu04RemainingCore
open SecondFunctionalGeometricMass SecondFunctionalJointTail SecondFunctionalFourSevenths
noncomputable section

def a (i : Fin 3) : ℝ := 1/(row i).S
def b (i : Fin 3) : ℝ := 1/(row i).kappa1
def c (i : Fin 3) : ℝ := 1/(row i).kappa2
def f (i : Fin 3) : ℝ := 1/(row i).s
def r (i : Fin 3) : ℝ := (2-b i-f i)/4
def rc (i : Fin 3) : ℝ := (2-b i-c i)/4
/-- Clip only at the original fourth-domain upper endpoint. -/
def v (i : Fin 3) : ℝ := min (rc i) (c i)
def R (i : Fin 3) : Set (Fin 3 → ℝ) := continuousRectangle ![a i,b i,c i] ![b i,r i,f i]
def T (i : Fin 3) : Set (Fin 3 → ℝ) := {t | a i≤t 0 ∧ t 0≤b i ∧
  r i<t 1 ∧ t 1≤v i ∧ c i≤t 2 ∧ t 2≤2-b i-4*t 1}

theorem geometry (i : Fin 3) : 0<a i ∧ a i<b i ∧ b i<r i ∧ r i<v i ∧ v i≤c i ∧ c i<f i := by
  revert i
  simp only [a,b,c,f,r,rc,v,row,ActualNineFeedback.coupledRow,SecondFunctionalPositive.parameters,
    Fin.forall_fin_succ,Fin.forall_fin_zero,and_true,Matrix.cons_val_zero,Matrix.cons_val_succ]
  norm_num [SecondFunctionalParameters.row2,SecondFunctionalParameters.row3,SecondFunctionalParameters.row4]

theorem clip_le (i : Fin 3) : v i≤rc i := min_le_left _ _

theorem last_clip : rc 2>c 2 ∧ v 2=c 2 := by
  change (2-1/SecondFunctionalParameters.row4.kappa1-1/SecondFunctionalParameters.row4.kappa2)/4 >
    1/SecondFunctionalParameters.row4.kappa2 ∧
    min ((2-1/SecondFunctionalParameters.row4.kappa1-1/SecondFunctionalParameters.row4.kappa2)/4)
      (1/SecondFunctionalParameters.row4.kappa2) = 1/SecondFunctionalParameters.row4.kappa2
  norm_num [SecondFunctionalParameters.row4]

theorem R_literal (i : Fin 3) {t : Fin 3 → ℝ} : t∈R i ↔
    a i≤t 0 ∧ t 0≤b i ∧ b i≤t 1 ∧ t 1≤r i ∧ c i≤t 2 ∧ t 2≤f i := by
  simp only [R,continuousRectangle,mem_pi,mem_univ,forall_const,Fin.forall_fin_succ,
    Fin.forall_fin_zero,and_true,Matrix.cons_val_zero,Matrix.cons_val_succ,mem_Icc]
  tauto

theorem R_measurable (i : Fin 3) : MeasurableSet (R i) :=
  MeasurableSet.univ_pi (fun _ => measurableSet_Icc)

theorem T_measurable (i : Fin 3) : MeasurableSet (T i) := by
  unfold T
  exact (measurableSet_le measurable_const (measurable_pi_apply 0)).inter
    ((measurableSet_le (measurable_pi_apply 0) measurable_const).inter
    ((measurableSet_lt measurable_const (measurable_pi_apply 1)).inter
    ((measurableSet_le (measurable_pi_apply 1) measurable_const).inter
    ((measurableSet_le measurable_const (measurable_pi_apply 2)).inter
    (measurableSet_le (measurable_pi_apply 2)
      ((measurable_const.sub measurable_const).sub (measurable_const.mul (measurable_pi_apply 1))))))))

theorem R_subset (i : Fin 3) : R i⊆LowerTripleContinuous.D (1/(row i).S) (1/(row i).kappa1)
    (1/(row i).kappa2) (1/(row i).kappa3) (1/(row i).s) 3 := by
  intro t ht
  obtain ⟨h0,h0',h1,h1',h2,h2'⟩ := (R_literal i).mp ht
  have g := geometry i
  have hrc := g.2.2.2.1.le.trans g.2.2.2.2.1
  change a i≤t 0 ∧ t 0≤b i ∧ b i≤t 1 ∧ t 1≤c i ∧ c i≤t 2 ∧ t 2≤f i ∧ t 0≤t 1 ∧ t 1≤t 2
  exact ⟨h0,h0',h1,h1'.trans hrc,h2,h2',h0'.trans h1,(h1'.trans hrc).trans h2⟩

theorem T_subset (i : Fin 3) : T i⊆LowerTripleContinuous.D (1/(row i).S) (1/(row i).kappa1)
    (1/(row i).kappa2) (1/(row i).kappa3) (1/(row i).s) 3 := by
  intro t ht
  obtain ⟨h0,h0',h1,h1',h2,h2'⟩ := ht
  have g := geometry i
  have hb := (g.2.2.1.trans h1).le
  have hc := h1'.trans g.2.2.2.2.1
  have hf : t 2≤f i := by unfold r at h1; linarith only [h1,h2']
  change a i≤t 0 ∧ t 0≤b i ∧ b i≤t 1 ∧ t 1≤c i ∧ c i≤t 2 ∧ t 2≤f i ∧ t 0≤t 1 ∧ t 1≤t 2
  exact ⟨h0,h0',hb,hc,h2,hf,h0'.trans hb,hc.trans h2⟩

theorem R_argument (i : Fin 3) {φ : ℝ} (hφ : 2≤φ) {t : Fin 3 → ℝ} (ht : t∈R i) :
    3≤(φ-(t 0+t 1+t 2))/t 1 := by
  obtain ⟨_,h0,h1,h1',_,h2⟩ := (R_literal i).mp ht
  have hp := ((geometry i).1.trans (geometry i).2.1).trans_le h1
  apply (le_div_iff₀ hp).mpr
  unfold r at h1'
  linarith only [hφ,h0,h1',h2]

theorem T_argument (i : Fin 3) {φ : ℝ} (hφ : 2≤φ) {t : Fin 3 → ℝ} (ht : t∈T i) :
    3≤(φ-(t 0+t 1+t 2))/t 1 := by
  have cube := LowerTripleContinuous.D_subset_cube (original_compact i.succ) 3 (T_subset i ht)
  have hp : 0<t 1 := by linarith [(cube 1 (mem_univ 1)).1]
  apply (le_div_iff₀ hp).mpr
  obtain ⟨_,hx,_,_,_,hz⟩ := ht
  linarith only [hφ,hx,hz]

theorem disjoint (i : Fin 3) : Disjoint (R i) (T i) := by
  apply Set.disjoint_left.mpr
  intro t hr ht
  exact (not_lt_of_ge ((R_literal i).mp hr).2.2.2.1) ht.2.2.1

theorem weight_lower (i : Fin 3) {t : Fin 3 → ℝ} (ht : t∈T i) :
    1/(b i*(v i)^2*f i)≤geometricWeight 1 t := by
  have cube := LowerTripleContinuous.D_subset_cube (original_compact i.succ) 3 (T_subset i ht)
  have hp (j : Fin 3) : 0<t j := by linarith [(cube j (mem_univ j)).1]
  have g := geometry i
  have hb := g.1.trans g.2.1
  have hv := (hb.trans g.2.2.1).trans g.2.2.2.1
  have hz := (T_subset i ht).2.2.2.2.2.1
  rw [Wu04CurveGeometry.weight_literal]
  apply one_div_le_one_div_of_le (mul_pos (mul_pos (hp 0) (sq_pos_of_pos (hp 1))) (hp 2))
  have hs : (t 1)^2≤(v i)^2 := (sq_le_sq₀ (hp 1).le hv.le).mpr ht.2.2.2.1
  exact mul_le_mul (mul_le_mul ht.2.1 hs (sq_nonneg _) hb.le) hz (hp 2).le
    (mul_nonneg hb.le (sq_nonneg _))
end
end Wu04RemainingStrongFourth
