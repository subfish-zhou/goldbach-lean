import Wu04RecoverCost

namespace Wu04RecoverGamma
open Wu2008DoubleSieve Set MeasureTheory Real
open SecondFunctionalParameters SecondFunctionalGeometricMass SecondFunctionalJointTail
open SharpLogRecurrence JointLogTotalComparison
noncomputable section

def lo : ℝ := 1/row1.kappa1
def hi : ℝ := 1/row1.kappa3
/-- Forced by a≤b and the original c upper endpoint in a+4b+c≤2. -/
def r : ℝ := (2-hi)/5
def d : ℝ := Wu04MainTail.cap-Wu04ThreeTail.cap

theorem geometry : 1/10≤lo ∧ 0<lo ∧ lo<r ∧ r<hi ∧ hi=25/61 := by
  norm_num [lo,hi,r,row1]
theorem d_pos : 0<d := sub_pos.mpr Wu04ThreeTail.cap_lt_main

def W := Omega3ElementaryRegularity.extension
def D (phi a b c : ℝ) : ℝ := Wu04MainTail.cap*W a b c-omega3XIntegralKernelExtension phi a b c

theorem W_cont : Continuous (fun p : ℝ × ℝ × ℝ => W p.1 p.2.1 p.2.2) :=
  Omega3ElementaryRegularity.extension_continuous

theorem D_cont (phi : ℝ) : Continuous (fun p : ℝ × ℝ × ℝ => D phi p.1 p.2.1 p.2.2) := by
  have hB : Continuous (fun p : ℝ × ℝ × ℝ => omega3XIntegralKernelExtension phi p.1 p.2.1 p.2.2) :=
    omega3XIntegralKernelExtension_continuous.comp
      (f := fun p : ℝ × ℝ × ℝ => (phi,p.1,p.2.1,p.2.2))
      (show Continuous (fun p : ℝ × ℝ × ℝ => (phi,p.1,p.2.1,p.2.2)) by fun_prop)
  have hW : Continuous (fun p : ℝ × ℝ × ℝ => Wu04MainTail.cap * W p.1 p.2.1 p.2.2) :=
    W_cont.const_mul Wu04MainTail.cap
  exact hW.sub hB

theorem D_nonneg {phi a b c : ℝ} (hp : 2≤phi)
    (ha : a∈Icc lo hi) (hb : b∈Icc lo hi) (hc : c∈Icc lo hi) : 0≤D phi a b c := by
  have h := Wu04MainCost.omega_kernel hp (geometry.2.2.2.2 ▸ ha.2)
    (geometry.2.2.2.2 ▸ hb.2) (geometry.2.2.2.2 ▸ hc.2)
    (geometry.2.1.trans_le ha.1) (geometry.2.1.trans_le hb.1) (geometry.2.1.trans_le hc.1)
  unfold D W
  rw [Omega3ElementaryRegularity.extension_eq (geometry.1.trans ha.1) (geometry.1.trans hb.1)
      (geometry.1.trans hc.1), omega3XIntegralKernelExtension_eq
      (geometry.1.trans ha.1) (geometry.1.trans hb.1) (geometry.1.trans hc.1)]
  linarith only [h]

theorem small_argument {phi a b c : ℝ} (hp : 2≤phi) (ha : a≤b)
    (hb0 : 0<b) (hb : b≤r) (hc : c≤hi) : 3≤(phi-a-b-c)/b := by
  apply (le_div_iff₀ hb0).2
  unfold r at hb
  linarith

theorem D_small {phi a b c : ℝ} (hp : 2≤phi) (ha : a∈Icc lo r)
    (hb : b∈Icc a r) (hc : c∈Icc r hi) : d*W a b c≤D phi a b c := by
  have ha0 := geometry.2.1.trans_le ha.1
  have hb0 := ha0.trans_le hb.1
  have hc0 := (geometry.2.1.trans geometry.2.2.1).trans_le hc.1
  have h := div_le_div_of_nonneg_right
    (Wu04ThreeTail.buchstab_le (small_argument hp hb.1 hb0 hb.2 hc.2))
    (show 0≤a*b^2*c by positivity)
  unfold D W d
  rw [Omega3ElementaryRegularity.extension_eq (geometry.1.trans ha.1)
      ((geometry.1.trans ha.1).trans hb.1) ((geometry.1.trans geometry.2.2.1.le).trans hc.1),
    omega3XIntegralKernelExtension_eq (geometry.1.trans ha.1)
      ((geometry.1.trans ha.1).trans hb.1) ((geometry.1.trans geometry.2.2.1.le).trans hc.1)]
  unfold omega3XIntegralKernel
  simp only [div_eq_mul_inv] at h ⊢
  nlinarith only [h]

/-- Monotonicity is used on the actual nonnegative deficit, not on Buchstab itself. -/
theorem subinterval {F : ℝ→ℝ} {a b c e : ℝ} (hc : c≤a) (hab : a≤b) (he : b≤e)
    (hn : ∀ x∈Icc c e, 0≤F x) (hf : IntervalIntegrable F volume c e) :
    (∫ x in a..b, F x)≤∫ x in c..e, F x := by
  apply intervalIntegral.integral_mono_interval hc hab he _ hf
  exact (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall
    (fun x hx => hn x ⟨hx.1.le,hx.2⟩))

def inner (phi a b : ℝ) : ℝ := ∫ c in b..hi, D phi a b c
def middle (phi a : ℝ) : ℝ := ∫ b in a..hi, inner phi a b
def blockInner (a b : ℝ) : ℝ := ∫ c in r..hi, W a b c
def blockMiddle (a : ℝ) : ℝ := ∫ b in a..r, blockInner a b

theorem inner_cont (phi : ℝ) : Continuous (fun p : ℝ×ℝ => inner phi p.1 p.2) := by
  apply Omega3ElementaryRegularity.continuous_moving
  · exact (D_cont phi).comp (show Continuous (fun p : (ℝ×ℝ)×ℝ => (p.1.1,p.1.2,p.2)) by fun_prop)
  · fun_prop
  · fun_prop

theorem middle_cont (phi : ℝ) : Continuous (middle phi) := by
  exact Omega3ElementaryRegularity.continuous_moving (inner_cont phi) continuous_id continuous_const

theorem blockInner_cont : Continuous (fun p : ℝ×ℝ => blockInner p.1 p.2) := by
  apply Omega3ElementaryRegularity.continuous_moving
  · exact W_cont.comp (show Continuous (fun p : (ℝ×ℝ)×ℝ => (p.1.1,p.1.2,p.2)) by fun_prop)
  · fun_prop
  · fun_prop

theorem blockMiddle_cont : Continuous blockMiddle :=
  Omega3ElementaryRegularity.continuous_moving blockInner_cont continuous_id continuous_const

theorem inner_nonneg {phi a b : ℝ} (hp : 2≤phi) (ha : a∈Icc lo hi)
    (hb : b∈Icc a hi) : 0≤ inner phi a b := by
  apply intervalIntegral.integral_nonneg hb.2
  intro c hc
  exact D_nonneg hp ha ⟨ha.1.trans hb.1,hb.2⟩ ⟨(ha.1.trans hb.1).trans hc.1,hc.2⟩

theorem middle_nonneg {phi a : ℝ} (hp : 2≤phi) (ha : a∈Icc lo hi) : 0≤middle phi a :=
  intervalIntegral.integral_nonneg ha.2 (fun _ hb => inner_nonneg hp ha hb)

theorem inner_paid {phi a b : ℝ} (hp : 2≤phi) (ha : a∈Icc lo r) (hb : b∈Icc a r) :
    d*blockInner a b≤ inner phi a b := by
  have hiD : Continuous (fun c => D phi a b c) := (D_cont phi).comp
    (show Continuous (fun c : ℝ => (a,b,c)) by fun_prop)
  have hiW : Continuous (fun c => W a b c) := W_cont.comp
    (show Continuous (fun c : ℝ => (a,b,c)) by fun_prop)
  have h1 : d*blockInner a b≤∫ c in r..hi, D phi a b c := by
    unfold blockInner
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_mono_on geometry.2.2.2.1.le
      ((hiW.const_mul d).intervalIntegrable _ _) (hiD.intervalIntegrable _ _)
      (fun _ hc => D_small hp ha hb hc)
  exact h1.trans (subinterval hb.2 geometry.2.2.2.1.le le_rfl
    (fun c hc => D_nonneg hp ⟨ha.1,ha.2.trans geometry.2.2.2.1.le⟩
      ⟨ha.1.trans hb.1,hb.2.trans geometry.2.2.2.1.le⟩
      ⟨(ha.1.trans hb.1).trans hc.1,hc.2⟩) (hiD.intervalIntegrable _ _))

theorem middle_paid {phi a : ℝ} (hp : 2≤phi) (ha : a∈Icc lo r) :
    d*blockMiddle a≤middle phi a := by
  have hiI : Continuous (inner phi a) := (inner_cont phi).comp
    (show Continuous (fun b : ℝ => (a,b)) by fun_prop)
  have hiB : Continuous (blockInner a) := blockInner_cont.comp
    (show Continuous (fun b : ℝ => (a,b)) by fun_prop)
  have h1 : d*blockMiddle a≤∫ b in a..r, inner phi a b := by
    unfold blockMiddle
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_mono_on ha.2
      ((hiB.const_mul d).intervalIntegrable _ _) (hiI.intervalIntegrable _ _)
      (fun _ hb => inner_paid hp ha hb)
  exact h1.trans (subinterval le_rfl ha.2 geometry.2.2.2.1.le
    (fun _ hb => inner_nonneg hp ⟨ha.1,ha.2.trans geometry.2.2.2.1.le⟩ hb)
    (hiI.intervalIntegrable _ _))

theorem deficit_paid {phi : ℝ} (hp : 2≤phi) :
    d*(∫ a in lo..r, blockMiddle a)≤∫ a in lo..hi, middle phi a := by
  have h1 : d*(∫ a in lo..r, blockMiddle a)≤∫ a in lo..r, middle phi a := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_mono_on geometry.2.2.1.le
      ((blockMiddle_cont.const_mul d).intervalIntegrable _ _) ((middle_cont phi).intervalIntegrable _ _)
      (fun _ ha => middle_paid hp ha)
  exact h1.trans (subinterval le_rfl geometry.2.2.1.le geometry.2.2.2.1.le
    (fun _ ha => middle_nonneg hp ha) ((middle_cont phi).intervalIntegrable _ _))
end
end Wu04RecoverGamma
