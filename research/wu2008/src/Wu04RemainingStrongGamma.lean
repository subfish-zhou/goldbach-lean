import Wu04RemainingStrongPrefixCost

namespace Wu04RemainingStrongGamma
open Wu2008DoubleSieve Set MeasureTheory Real Wu04RemainingCore
open SecondFunctionalGeometricMass SecondFunctionalJointTail
noncomputable section

def lo (i : Fin 3) : ℝ := 1/(row i).kappa1
def hi (i : Fin 3) : ℝ := 1/(row i).kappa3
def cut (i : Fin 3) : ℝ := (2-hi i)/5

theorem geometry (i : Fin 3) : 1/10≤lo i ∧ 0<lo i ∧ lo i<cut i ∧ cut i<hi i := by
  revert i
  simp only [lo,hi,cut,row,ActualNineFeedback.coupledRow,SecondFunctionalPositive.parameters,
    Fin.forall_fin_succ,Fin.forall_fin_zero,and_true,Matrix.cons_val_zero,Matrix.cons_val_succ]
  norm_num [SecondFunctionalParameters.row2,SecondFunctionalParameters.row3,SecondFunctionalParameters.row4]

/-- The deficit is measured for Gamma9's own phi; no joint-kernel phi is identified. -/
theorem deficit_nonneg (i : Fin 3) {φ a b c : ℝ} (hφ : 2≤φ)
    (ha : a∈Icc (lo i) (hi i)) (hb : b∈Icc (lo i) (hi i))
    (hc : c∈Icc (lo i) (hi i)) : 0≤Wu04RecoverGamma.D φ a b c := by
  have g := geometry i
  have hk := Wu04RemainingGamma.kernel_paid hφ (Wu04RemainingGamma.original_gates i).2.2
    (g.2.1.trans_le ha.1) (g.2.1.trans_le hb.1) (g.2.1.trans_le hc.1) ha.2 hb.2 hc.2
  unfold Wu04RecoverGamma.D Wu04RecoverGamma.W
  rw [Omega3ElementaryRegularity.extension_eq (g.1.trans ha.1) (g.1.trans hb.1) (g.1.trans hc.1),
    omega3XIntegralKernelExtension_eq (g.1.trans ha.1) (g.1.trans hb.1) (g.1.trans hc.1)]
  linarith only [hk]

theorem deficit_small (i : Fin 3) {φ a b c : ℝ} (hφ : 2≤φ)
    (ha : a∈Icc (lo i) (cut i)) (hb : b∈Icc a (cut i))
    (hc : c∈Icc (cut i) (hi i)) :
    Wu04RecoverGamma.d*Wu04RecoverGamma.W a b c≤Wu04RecoverGamma.D φ a b c := by
  have g := geometry i
  have hb0 := (g.2.1.trans_le ha.1).trans_le hb.1
  have hu : 3≤(φ-a-b-c)/b := by
    apply (le_div_iff₀ hb0).mpr
    have hr := hb.2
    unfold cut at hr
    linarith only [hφ,hb.1,hr,hc.2]
  have hd := div_le_div_of_nonneg_right (Wu04ThreeTail.buchstab_le hu)
    (show 0≤a*b^2*c by
      have ha0 := g.2.1.trans_le ha.1
      have hc0 := (g.2.1.trans g.2.2.1).trans_le hc.1
      positivity)
  unfold Wu04RecoverGamma.D Wu04RecoverGamma.W Wu04RecoverGamma.d
  rw [Omega3ElementaryRegularity.extension_eq (g.1.trans ha.1)
      ((g.1.trans ha.1).trans hb.1) ((g.1.trans g.2.2.1.le).trans hc.1),
    omega3XIntegralKernelExtension_eq (g.1.trans ha.1)
      ((g.1.trans ha.1).trans hb.1) ((g.1.trans g.2.2.1.le).trans hc.1)]
  unfold omega3XIntegralKernel
  simp only [div_eq_mul_inv] at hd ⊢
  nlinarith only [hd]

/-- Continuous nonnegative ordered integrals retain a smaller actual cap domain. -/
theorem ordered_restrict {l r h : ℝ} (hlr : l≤r) (hrh : r≤h)
    {F : ℝ→ℝ→ℝ→ℝ} (hF : Continuous (fun p : ℝ×ℝ×ℝ => F p.1 p.2.1 p.2.2))
    (hn : ∀ a∈Icc l h,∀ b∈Icc a h,∀ c∈Icc b h,0≤F a b c) :
    (∫ a in l..r, ∫ b in a..r, ∫ c in r..h, F a b c)≤
    ∫ a in l..h, ∫ b in a..h, ∫ c in b..h, F a b c := by
  have ci (a b : ℝ) : Continuous (F a b) := hF.comp (show Continuous (fun c : ℝ => (a,b,c)) by fun_prop)
  have cm : Continuous (fun p : ℝ×ℝ => ∫ c in p.2..h, F p.1 p.2 c) :=
    Omega3ElementaryRegularity.continuous_moving
      (hF.comp (show Continuous (fun p : (ℝ×ℝ)×ℝ => (p.1.1,p.1.2,p.2)) by fun_prop))
      continuous_snd continuous_const
  have cb : Continuous (fun p : ℝ×ℝ => ∫ c in r..h, F p.1 p.2 c) :=
    Omega3ElementaryRegularity.continuous_moving
      (hF.comp (show Continuous (fun p : (ℝ×ℝ)×ℝ => (p.1.1,p.1.2,p.2)) by fun_prop))
      continuous_const continuous_const
  have co : Continuous (fun a => ∫ b in a..h, ∫ c in b..h, F a b c) :=
    Omega3ElementaryRegularity.continuous_moving cm continuous_id continuous_const
  have cr : Continuous (fun a => ∫ b in a..r, ∫ c in r..h, F a b c) :=
    Omega3ElementaryRegularity.continuous_moving cb continuous_id continuous_const
  have inner (a b : ℝ) (ha : a∈Icc l r) (hb : b∈Icc a r) :
      (∫ c in r..h,F a b c)≤∫ c in b..h,F a b c :=
    Wu04RecoverGamma.subinterval hb.2 hrh le_rfl
      (fun _ hc => hn a ⟨ha.1,ha.2.trans hrh⟩ b ⟨hb.1,hb.2.trans hrh⟩ _ hc)
      ((ci a b).intervalIntegrable _ _)
  have middle (a : ℝ) (ha : a∈Icc l r) :
      (∫ b in a..r,∫ c in r..h,F a b c)≤∫ b in a..h,∫ c in b..h,F a b c := by
    have cb' : Continuous (fun b => ∫ c in r..h,F a b c) := cb.comp (show Continuous (fun b : ℝ => (a,b)) by fun_prop)
    have cm' : Continuous (fun b => ∫ c in b..h,F a b c) := cm.comp (show Continuous (fun b : ℝ => (a,b)) by fun_prop)
    exact (intervalIntegral.integral_mono_on ha.2 (cb'.intervalIntegrable _ _)
      (cm'.intervalIntegrable _ _) (fun _ hb => inner a _ ha hb)).trans
      (Wu04RecoverGamma.subinterval le_rfl ha.2 hrh
        (fun b hb => intervalIntegral.integral_nonneg hb.2
          (fun c hc => hn a ⟨ha.1,ha.2.trans hrh⟩ b hb c hc)) (cm'.intervalIntegrable _ _))
  exact (intervalIntegral.integral_mono_on hlr (cr.intervalIntegrable _ _)
    (co.intervalIntegrable _ _) middle).trans
    (Wu04RecoverGamma.subinterval le_rfl hlr hrh
      (fun a ha => intervalIntegral.integral_nonneg ha.2
        (fun b hb => intervalIntegral.integral_nonneg hb.2 (fun c hc => hn a ha b hb c hc)))
      (co.intervalIntegrable _ _))

/-- The smaller cap is paid from the actual deficit on the full ordered Gamma9 domain. -/
theorem deficit_paid (i : Fin 3) {φ : ℝ} (hφ : 2≤φ) :
    Wu04RecoverGamma.d*(∫ a in lo i..cut i, ∫ b in a..cut i,
      ∫ c in cut i..hi i,Wu04RecoverGamma.W a b c) ≤
    ∫ a in lo i..hi i,∫ b in a..hi i,∫ c in b..hi i,Wu04RecoverGamma.D φ a b c := by
  let F := Wu04RecoverGamma.D φ
  let W := Wu04RecoverGamma.W
  have g := geometry i
  have cmD : Continuous (fun p : ℝ×ℝ => ∫ c in cut i..hi i,F p.1 p.2 c) :=
    Omega3ElementaryRegularity.continuous_moving
      ((Wu04RecoverGamma.D_cont φ).comp (show Continuous (fun p : (ℝ×ℝ)×ℝ => (p.1.1,p.1.2,p.2)) by fun_prop)) continuous_const continuous_const
  have cmW : Continuous (fun p : ℝ×ℝ => ∫ c in cut i..hi i,W p.1 p.2 c) :=
    Omega3ElementaryRegularity.continuous_moving
      (Wu04RecoverGamma.W_cont.comp (show Continuous (fun p : (ℝ×ℝ)×ℝ => (p.1.1,p.1.2,p.2)) by fun_prop)) continuous_const continuous_const
  have coD : Continuous (fun a => ∫ b in a..cut i, ∫ c in cut i..hi i,F a b c) := Omega3ElementaryRegularity.continuous_moving cmD continuous_id (continuous_const (y:=cut i))
  have coW : Continuous (fun a => ∫ b in a..cut i, ∫ c in cut i..hi i,W a b c) := Omega3ElementaryRegularity.continuous_moving cmW continuous_id (continuous_const (y:=cut i))
  have inner (a b : ℝ) (ha : a∈Icc (lo i) (cut i)) (hb : b∈Icc a (cut i)) :
      Wu04RecoverGamma.d*(∫ c in cut i..hi i,W a b c)≤∫ c in cut i..hi i,F a b c := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_mono_on g.2.2.2.le
      ((((Wu04RecoverGamma.W_cont).comp (show Continuous (fun c : ℝ => (a,b,c)) by fun_prop)).const_mul _).intervalIntegrable _ _)
      (((Wu04RecoverGamma.D_cont φ).comp (show Continuous (fun c : ℝ => (a,b,c)) by fun_prop)).intervalIntegrable _ _)
      (fun c hc => deficit_small i hφ ha hb hc)
  have middle (a : ℝ) (ha : a∈Icc (lo i) (cut i)) :
      Wu04RecoverGamma.d*(∫ b in a..cut i,∫ c in cut i..hi i,W a b c)≤
      ∫ b in a..cut i,∫ c in cut i..hi i,F a b c := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_mono_on ha.2
      (((cmW.comp (show Continuous (fun b : ℝ => (a,b)) by fun_prop)).const_mul _).intervalIntegrable _ _)
      ((cmD.comp (show Continuous (fun b : ℝ => (a,b)) by fun_prop)).intervalIntegrable _ _) (fun b hb => inner a b ha hb)
  have hsmall : Wu04RecoverGamma.d*(∫ a in lo i..cut i,∫ b in a..cut i,
      ∫ c in cut i..hi i,W a b c)≤∫ a in lo i..cut i,∫ b in a..cut i,
      ∫ c in cut i..hi i,F a b c := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_mono_on g.2.2.1.le
      ((coW.const_mul _).intervalIntegrable _ _) (coD.intervalIntegrable _ _) middle
  exact hsmall.trans (ordered_restrict g.2.2.1.le g.2.2.2.le (Wu04RecoverGamma.D_cont φ)
    (fun a ha b hb c hc => deficit_nonneg i hφ ha ⟨ha.1.trans hb.1,hb.2⟩
      ⟨(ha.1.trans hb.1).trans hc.1,hc.2⟩))
end
end Wu04RemainingStrongGamma
