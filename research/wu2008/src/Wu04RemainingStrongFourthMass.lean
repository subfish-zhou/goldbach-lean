import Wu04RemainingStrongFourthVolume

namespace Wu04RemainingStrongFourthMass
open Wu2008DoubleSieve Set MeasureTheory Real Wu04RemainingCore Wu04RemainingStrongFourth
open Wu04RemainingStrongFourthVolume SecondFunctionalGeometricMass SecondFunctionalJointTail SecondFunctionalFourSevenths
noncomputable section

def rectLower (i : Fin 3) : ℝ := Wu04FactorEnvelopes.lower (b i/a i)*
  (1/b i-1/r i)*Wu04FactorEnvelopes.lower (f i/c i)
def curveLower (i : Fin 3) : ℝ := (b i-a i)*area i/(b i*(v i)^2*f i)
def gain (i : Fin 3) : ℝ := (Wu04MainTail.cap-Wu04ThreeTail.cap)*(rectLower i+curveLower i)

theorem rect_exact (i : Fin 3) : geometricMass 1 (R i)=
    log (b i/a i)*(1/b i-1/r i)*log (f i/c i) := by
  have g := geometry i
  have hb := g.1.trans g.2.1
  have hc := ((hb.trans g.2.2.1).trans g.2.2.2.1).trans_le g.2.2.2.2.1
  exact triple_rectangle_mass g.1 hb hc g.2.1.le g.2.2.1.le g.2.2.2.2.2.le

theorem rect_factors (i : Fin 3) : 0<Wu04FactorEnvelopes.lower (b i/a i) ∧
    0<1/b i-1/r i ∧ 0<Wu04FactorEnvelopes.lower (f i/c i) := by
  revert i
  simp only [a,b,c,f,r,row,ActualNineFeedback.coupledRow,SecondFunctionalPositive.parameters,
    Fin.forall_fin_succ,Fin.forall_fin_zero,and_true,Matrix.cons_val_zero,Matrix.cons_val_succ]
  norm_num [SecondFunctionalParameters.row2,SecondFunctionalParameters.row3,SecondFunctionalParameters.row4,
    Wu04FactorEnvelopes.lower,Wu04FactorEnvelopes.leftFactor,Wu04FactorEnvelopes.rightFactor,
    SharpLogRecurrence.lowerLog]

theorem rect_paid (i : Fin 3) : rectLower i≤geometricMass 1 (R i) := by
  rw [rect_exact]
  have g := geometry i
  have hb := g.1.trans g.2.1
  have hc := ((hb.trans g.2.2.1).trans g.2.2.2.1).trans_le g.2.2.2.2.1
  have hx := Wu04FactorEnvelopes.lower_le_log ((one_le_div g.1).mpr g.2.1.le)
  have hz := Wu04FactorEnvelopes.lower_le_log ((one_le_div hc).mpr g.2.2.2.2.2.le)
  obtain ⟨hx0,hd,hz0⟩ := rect_factors i
  exact mul_le_mul (mul_le_mul_of_nonneg_right hx hd.le) hz hz0.le
    (mul_nonneg (hx0.le.trans hx) hd.le)

theorem curve_paid (i : Fin 3) : curveLower i≤geometricMass 1 (T i) := by
  have hi : IntegrableOn (fun _ : Fin 3 → ℝ => 1/(b i*(v i)^2*f i)) (T i) :=
    integrableOn_const (by rw [T_volume]; exact ENNReal.ofReal_ne_top)
  have cube := (T_subset i).trans (LowerTripleContinuous.D_subset_cube (original_compact i.succ) 3)
  have hh := setIntegral_mono_on hi (geometricWeight_integrable 1 cube)
    (T_measurable i) (fun _ ht => weight_lower i ht)
  rw [setIntegral_const,T_volume_real] at hh
  change _≤geometricMass 1 (T i) at hh
  convert hh using 1
  simp only [smul_eq_mul]
  unfold curveLower
  ring

theorem gain_pos (i : Fin 3) : 0<gain i := by
  obtain ⟨hx,hd,hz⟩ := rect_factors i
  have g := geometry i
  have hb := g.1.trans g.2.1
  have hv := (hb.trans g.2.2.1).trans g.2.2.2.1
  have hf := (hv.trans_le g.2.2.2.2.1).trans g.2.2.2.2.2
  have hr : 0<rectLower i := mul_pos (mul_pos hx hd) hz
  have hc : 0<curveLower i := div_pos (mul_pos (sub_pos.mpr g.2.1) (area_pos i))
    (mul_pos (mul_pos hb (sq_pos_of_pos hv)) hf)
  exact mul_pos (sub_pos.mpr Wu04ThreeTail.cap_lt_main) (add_pos hr hc)

theorem union_mass (i : Fin 3) : geometricMass 1 (R i∪T i)=
    geometricMass 1 (R i)+geometricMass 1 (T i) := by
  unfold geometricMass
  exact setIntegral_union (disjoint i) (T_measurable i)
    (geometricWeight_integrable 1 ((R_subset i).trans
      (LowerTripleContinuous.D_subset_cube (original_compact i.succ) 3)))
    (geometricWeight_integrable 1 ((T_subset i).trans
      (LowerTripleContinuous.D_subset_cube (original_compact i.succ) 3)))

/-- One full-kernel inequality on the disjoint original rectangle/curve union. -/
theorem kernel_paid (i : Fin 3) {φ : ℝ} (hφ : 2≤φ) :
    LowerTripleContinuous.K (1/(row i).S) (1/(row i).kappa1) (1/(row i).kappa2)
      (1/(row i).kappa3) (1/(row i).s) 3 φ≤Wu04MainTail.cap*lowerMass (row i) 3-gain i := by
  have hk := Wu04RemainingTail.subdomain_paid i 3 ((R_measurable i).union (T_measurable i))
    (union_subset (R_subset i) (T_subset i)) hφ
    (fun _ ht => ht.elim (R_argument i hφ) (T_argument i hφ))
  rw [union_mass] at hk
  have hm := mul_le_mul_of_nonneg_left (add_le_add (rect_paid i) (curve_paid i))
    (sub_nonneg.mpr Wu04ThreeTail.cap_lt_main.le)
  unfold gain
  linarith only [hk,hm]
end
end Wu04RemainingStrongFourthMass
