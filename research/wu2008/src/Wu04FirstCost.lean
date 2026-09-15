import Wu04FirstIntegration

namespace Wu04FirstCost
open Wu2008DoubleSieve ActualNineFeedback Set MeasureTheory Real
open Wu04RecoverGamma Wu04FirstIntegration
open SecondFunctionalGeometricMass
noncomputable section

def lo (i : Fin 5) : ℝ := 1/firstS i
def hi (i : Fin 5) : ℝ := 1/firstNode i
/-- Forced by a≤b and the original upper c endpoint; no new numerical cut. -/
def cut (i : Fin 5) : ℝ := (2-hi i)/5

theorem geometry (i : Fin 5) : 1/10≤lo i ∧ 0<lo i ∧ lo i≤cut i ∧ cut i≤hi i := by
  revert i
  simp only [lo,hi,cut,firstNode,firstS,Fin.forall_fin_succ,Fin.forall_fin_zero,
    and_true,Matrix.cons_val_zero,Matrix.cons_val_succ]
  norm_num

theorem deficit_nonneg (i : Fin 5) {φ a b c : ℝ} (hφ : 2≤φ)
    (ha : a∈Icc (lo i) (hi i)) (hb : b∈Icc a (hi i)) (hc : c∈Icc b (hi i)) :
    0≤D φ a b c := by
  have g := geometry i
  have ha0 := g.2.1.trans_le ha.1
  have hb0 := ha0.trans_le hb.1
  have hc0 := hb0.trans_le hc.1
  have ha1 := g.1.trans ha.1
  have hb1 := ha1.trans hb.1
  have hc1 := hb1.trans hc.1
  have paid := Wu04RemainingGamma.kernel_paid hφ (Wu04FirstCore.cost_geometry i).2.2
    ha0 hb0 hc0 ha.2 hb.2 hc.2
  unfold D W
  rw [Omega3ElementaryRegularity.extension_eq ha1 hb1 hc1,
    omega3XIntegralKernelExtension_eq ha1 hb1 hc1]
  linarith only [paid]

theorem deficit_small (i : Fin 5) {φ a b c : ℝ} (hφ : 2≤φ)
    (ha : a∈Icc (lo i) (cut i)) (hb : b∈Icc a (cut i)) (hc : c∈Icc (cut i) (hi i)) :
    d*W a b c≤D φ a b c := by
  have g := geometry i
  have ha0 := g.2.1.trans_le ha.1
  have hb0 := ha0.trans_le hb.1
  have hc0 := (g.2.1.trans_le g.2.2.1).trans_le hc.1
  have arg : 3≤(φ-a-b-c)/b := by
    apply (le_div_iff₀ hb0).mpr
    have hh := hb.2
    unfold cut at hh
    linarith only [hφ,hb.1,hh,hc.2]
  have paid := div_le_div_of_nonneg_right (Wu04ThreeTail.buchstab_le arg)
    (show 0≤a*b^2*c by positivity)
  have ha1 := g.1.trans ha.1
  have hb1 := ha1.trans hb.1
  have hc1 := (g.1.trans g.2.2.1).trans hc.1
  unfold D W d
  rw [Omega3ElementaryRegularity.extension_eq ha1 hb1 hc1,
    omega3XIntegralKernelExtension_eq ha1 hb1 hc1]
  unfold omega3XIntegralKernel
  simp only [div_eq_mul_inv] at paid ⊢
  nlinarith only [paid]

/-- Actual selected-square mass, not an assumed cost certificate. -/
theorem deficit_paid (i : Fin 5) {φ : ℝ} (hφ : 2≤φ) :
    d*(∫ a in lo i..cut i,∫ b in a..cut i,∫ c in cut i..hi i,W a b c)≤
      ∫ a in lo i..hi i,∫ b in a..hi i,∫ c in b..hi i,D φ a b c := by
  have g := geometry i
  have subpaid := block_mono (F:=fun a b c => d*W a b c) (G:=D φ)
    (W_cont.const_mul d) (D_cont φ) g.2.2.1 g.2.2.2
    (fun a ha b hb c hc => deficit_small i hφ ha hb hc)
  simp only [intervalIntegral.integral_const_mul] at subpaid
  exact subpaid.trans (Wu04RemainingStrongGamma.ordered_restrict (F:=D φ) g.2.2.1 g.2.2.2
    (D_cont φ) (fun a ha b hb c hc => deficit_nonneg i hφ ha hb hc))

theorem weight_integral (i : Fin 5) :
    (∫ a in lo i..hi i,∫ b in a..hi i,∫ c in b..hi i,W a b c)=
      Elementary.elementaryMomentOne 1 (lo i) (hi i) := by
  have g := geometry i
  have hlh := g.2.2.1.trans g.2.2.2
  calc
    _ = ∫ a in lo i..hi i,∫ b in a..hi i,∫ c in b..hi i,(1:ℝ)/(a*b^2*c) := by
      apply intervalIntegral.integral_congr
      intro a ha
      rw [uIcc_of_le hlh] at ha
      exact Omega3ElementaryRegularity.middle_eq (g.1.trans ha.1) ha.2
    _ = _ := Omega3ElementaryMass.nested_eq_elementary g.2.1 hlh

theorem kernel_integral (i : Fin 5) (φ : ℝ) :
    (∫ a in lo i..hi i,∫ b in a..hi i,∫ c in b..hi i,omega3XIntegralKernelExtension φ a b c)=
      omega3XIntegral (firstNode i) (firstS i) φ := by
  have g := geometry i
  exact omega3XIntegralExtension_eq g.1 (g.2.2.1.trans g.2.2.2)

/-- Exact linearity, before paying or taking the unbounded-phi supremum. -/
theorem deficit_identity (i : Fin 5) (φ : ℝ) :
    (∫ a in lo i..hi i,∫ b in a..hi i,∫ c in b..hi i,D φ a b c)=
      Wu04MainTail.cap*Elementary.elementaryMomentOne 1 (lo i) (hi i)-
      omega3XIntegral (firstNode i) (firstS i) φ := by
  have hk : Continuous (fun p : ℝ×ℝ×ℝ => omega3XIntegralKernelExtension φ p.1 p.2.1 p.2.2) :=
    omega3XIntegralKernelExtension_continuous.comp
      (f:=fun p : ℝ×ℝ×ℝ => (φ,p.1,p.2.1,p.2.2))
      (show Continuous (fun p : ℝ×ℝ×ℝ => (φ,p.1,p.2.1,p.2.2)) by fun_prop)
  have h := ordered_sub (F:=fun a b c => Wu04MainTail.cap*W a b c)
    (G:=fun a b c => omega3XIntegralKernelExtension φ a b c)
    (W_cont.const_mul Wu04MainTail.cap) hk (lo i) (hi i)
  simp only [intervalIntegral.integral_const_mul,weight_integral,kernel_integral] at h
  exact h
end
end Wu04FirstCost
