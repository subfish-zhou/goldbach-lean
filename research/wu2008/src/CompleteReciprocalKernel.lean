import KernelCurvatureWindowGain

namespace Wu2008DoubleSieve.Phase16
open Real Set MeasureTheory HighSixPhase9 SingleUpperHSource SingleUpperHIntegral Phase11 Phase12
open Phase13 (κh κH κh_pos κH_pos)
open Phase14 (w0 q1 q2 poly q1_pos q2_pos poly_nonneg)
noncomputable section

def L0 : ℝ := 407/2654
def r0 : ℝ := 1/4
def movingRight (δ : ℝ) : ℝ := (1/2-δ)/2
def U : ℝ := 53429911/125193600
def V : ℝ := 2343083/1017198
def f0 (t : ℝ) : ℝ := poly (t-L0)/(t*(1/2-t))
def logPrimitive (t : ℝ) : ℝ := -q2*t+U*log t-V*log (1/2-t)
def Gamma : ℝ := 2*(-q2*w0+U*log (r0/L0)+V*log ((1/2-L0)/(1/2-r0)))
def M : ℝ := poly w0/(L0*(1/2-r0))
def C16 : ℝ := Ctail+Cmid+Gamma
def movingC (δ : ℝ) : ℝ := Ctail+Cmid+2*∫ t in L0..movingRight δ, f0 t

theorem fixed_geometry : 0 < L0 ∧ L0 < r0 ∧ r0 < (1/2 : ℝ) ∧ r0-L0 = w0 := by
  norm_num [L0,r0,w0]

theorem moving_geometry {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100) :
    shapeLeft δ = L0-δ ∧ shapeLeft δ ≤ L0 ∧ L0 < movingRight δ ∧
      movingRight δ ≤ r0 ∧ r0-movingRight δ = δ/2 := by
  dsimp [shapeLeft,L0,movingRight,r0,truncatedSixthLowerAlpha]
  constructor
  · ring
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

theorem poly_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) : poly x ≤ poly y := by
  have h1 := mul_le_mul_of_nonneg_left hxy q1_pos.le
  have h2 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx hxy 2) q2_pos.le
  unfold poly
  linarith only [h1,h2]

theorem poly_pos {x : ℝ} (hx : 0 ≤ x) : 0 < poly x := by
  have h1 := mul_nonneg q1_pos.le hx
  have h2 := mul_nonneg q2_pos.le (sq_nonneg x)
  unfold poly
  linarith only [κH_pos,h1,h2]

theorem f0_partial_fraction {t : ℝ} (ht : 0 < t) (htc : t < 1/2) :
    f0 t = -q2+U/t+V/(1/2-t) := by
  have ht' : t ≠ 0 := ne_of_gt ht
  have hc : 1/2-t ≠ 0 := ne_of_gt (sub_pos.mpr htc)
  unfold f0
  field_simp [ht',hc]
  norm_num [poly,L0,q1,q2,U,V,κH,κh,truncatedSixthLowerAlpha]
  field_simp [show 1-t*2 ≠ 0 by linarith]
  ring

theorem f0_continuous : ContinuousOn f0 (Icc L0 r0) := by
  apply ContinuousOn.div
  · unfold poly
    fun_prop
  · fun_prop
  · intro t ht
    exact ne_of_gt (mul_pos (lt_of_lt_of_le fixed_geometry.1 ht.1)
      (sub_pos.mpr (lt_of_le_of_lt ht.2 fixed_geometry.2.2.1)))

theorem f0_integrable {a b : ℝ} (ha : L0 ≤ a) (hab : a ≤ b) (hb : b ≤ r0) :
    IntervalIntegrable f0 volume a b :=
  (f0_continuous.mono (Icc_subset_Icc ha hb)).intervalIntegrable_of_Icc hab

theorem logPrimitive_deriv {t : ℝ} (ht : 0 < t) (htc : t < 1/2) :
    HasDerivAt logPrimitive (f0 t) t := by
  have h := (hasDerivAt_const t (1/2 : ℝ)).sub (hasDerivAt_id t)
  have hd := (((hasDerivAt_id t).const_mul (-q2)).add
    ((hasDerivAt_log (ne_of_gt ht)).const_mul U)).sub
      ((h.log (ne_of_gt (sub_pos.mpr htc))).const_mul V)
  rw [f0_partial_fraction ht htc]
  convert hd using 1 <;> first | rfl | (dsimp; ring)

theorem fixed_integral_closed : Gamma = 2*∫ t in L0..r0, f0 t := by
  have hi := f0_integrable le_rfl fixed_geometry.2.1.le le_rfl
  have hf := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => logPrimitive_deriv
      (lt_of_lt_of_le fixed_geometry.1 (uIcc_of_le fixed_geometry.2.1.le ▸ ht).1)
      (lt_of_le_of_lt (uIcc_of_le fixed_geometry.2.1.le ▸ ht).2 fixed_geometry.2.2.1)) hi
  rw [hf]
  unfold Gamma logPrimitive
  rw [Real.log_div (ne_of_gt (by norm_num [r0])) (ne_of_gt fixed_geometry.1),
    Real.log_div (ne_of_gt (by norm_num [L0])) (ne_of_gt (by norm_num [r0]))]
  rw [← fixed_geometry.2.2.2]
  ring

theorem M_exact : M = (181693565869/73599926400 : ℝ) := by
  norm_num [M,poly,w0,L0,r0,q1,q2,κH,κh,truncatedSixthLowerAlpha]
theorem M_pos : 0 < M := by rw [M_exact]; norm_num

theorem f0_bounds {t : ℝ} (ht : t ∈ Icc L0 r0) : 0 < f0 t ∧ f0 t ≤ M := by
  have ht0 := lt_of_lt_of_le fixed_geometry.1 ht.1
  have hc := sub_pos.mpr (lt_of_le_of_lt ht.2 fixed_geometry.2.2.1)
  have hp := poly_pos (sub_nonneg.mpr ht.1)
  have hpoly := poly_mono (sub_nonneg.mpr ht.1)
    (show t-L0 ≤ w0 by rw [← fixed_geometry.2.2.2]; linarith only [ht.2])
  have hden : L0*(1/2-r0) ≤ t*(1/2-t) :=
    mul_le_mul ht.1 (by linarith only [ht.2]) (by norm_num [r0]) ht0.le
  constructor
  · exact div_pos hp (mul_pos ht0 hc)
  · exact div_le_div₀ (hp.le.trans hpoly) hpoly (by norm_num [L0,r0]) hden

theorem strip_bounds {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100) :
    0 ≤ 2*∫ t in movingRight δ..r0, f0 t ∧
      2*∫ t in movingRight δ..r0, f0 t ≤ M*δ := by
  have hg := moving_geometry hδ hδhi
  have hi := f0_integrable hg.2.2.1.le hg.2.2.2.1 le_rfl
  have hn := intervalIntegral.integral_nonneg (μ := volume) (a := movingRight δ) (b := r0)
    hg.2.2.2.1 (fun t ht => (f0_bounds ⟨hg.2.2.1.le.trans ht.1,ht.2⟩).1.le)
  have hm := intervalIntegral.integral_mono_on hg.2.2.2.1 hi
    (intervalIntegrable_const (c := M))
    (fun t ht => (f0_bounds ⟨hg.2.2.1.le.trans ht.1,ht.2⟩).2)
  rw [intervalIntegral.integral_const] at hm
  simp only [smul_eq_mul] at hm
  rw [hg.2.2.2.2] at hm
  constructor <;> linarith only [hn,hm]

theorem movingC_bounds {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100) :
    0 ≤ movingC δ ∧ movingC δ ≤ C16 ∧ C16-M*δ ≤ movingC δ := by
  have hg := moving_geometry hδ hδhi
  have hi := intervalIntegral.integral_add_adjacent_intervals
    (f0_integrable le_rfl hg.2.2.1.le hg.2.2.2.1)
    (f0_integrable hg.2.2.1.le hg.2.2.2.1 le_rfl)
  have hs := strip_bounds hδ hδhi
  have hn := intervalIntegral.integral_nonneg (μ := volume) hg.2.2.1.le
    (fun t ht => (f0_bounds ⟨ht.1,ht.2.trans hg.2.2.2.1⟩).1.le)
  unfold movingC C16
  rw [fixed_integral_closed]
  constructor
  · linarith only [Ctail_pos,Cmid_pos,hn]
  constructor <;> linarith only [hi,hs.1,hs.2]

/-- Strict comparison of pure fixed functions, not an H instance at zero. -/
theorem quartic_comparison {t : ℝ} (ht : t ∈ Icc L0 r0) :
    poly (t-L0)*(16+256*(r0-t)^2) ≤ f0 t := by
  have ht0 := lt_of_lt_of_le fixed_geometry.1 ht.1
  have hc := sub_pos.mpr (lt_of_le_of_lt ht.2 fixed_geometry.2.2.1)
  have he : (16+256*(r0-t)^2)*(t*(1/2-t)) = 1-256*(r0-t)^4 := by
    unfold r0
    ring
  have hh : (16+256*(r0-t)^2)*(t*(1/2-t)) ≤ 1 := by
    rw [he]
    nlinarith only [sq_nonneg ((r0-t)^2)]
  have hp := mul_le_mul_of_nonneg_left hh (poly_nonneg (sub_nonneg.mpr ht.1))
  apply (le_div_iff₀ (mul_pos ht0 hc)).2
  calc
    _ = poly (t-L0)*((16+256*(r0-t)^2)*(t*(1/2-t))) := by ring
    _ ≤ poly (t-L0) := by simpa only [mul_one] using hp

theorem quartic_strict_midpoint :
    poly ((L0+r0)/2-L0)*(16+256*(r0-(L0+r0)/2)^2) < f0 ((L0+r0)/2) := by
  norm_num [poly,f0,L0,r0,q1,q2,κH,κh,truncatedSixthLowerAlpha]

theorem Gamma_strict : 2*Phase15.fullMass w0 < Gamma := by
  have hp : Continuous (fun t : ℝ => poly (t-L0)*(16+256*(r0-t)^2)) := by
    unfold poly
    fun_prop
  have hi := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
    fixed_geometry.2.1 hp.continuousOn f0_continuous
    (fun t ht => quartic_comparison ⟨ht.1.le,ht.2⟩)
    ⟨(L0+r0)/2, by constructor <;> linarith only [fixed_geometry.2.1], quartic_strict_midpoint⟩
  have he := Phase15.curvature_polynomial_integral L0 r0 1
  simp only [one_mul] at he
  rw [fixed_geometry.2.2.2] at he
  rw [he] at hi
  rw [fixed_integral_closed]
  linarith only [hi]

theorem C15_identity : Phase15.C15 = Ctail+Cmid+2*Phase15.fullMass w0 := by
  have he := Phase15.curvature_coefficient_identity
  have hp := Phase14.polynomial_coefficient_identity
  unfold Phase15.C15 Phase14.C14 Cfull Phase15.fullMass Phase15.deltaKernel
  have hc : Cgeo = 32*q2/3*w0^3 := by
    norm_num [Cgeo,q2,w0,truncatedSixthLowerAlpha]
  rw [hc]
  unfold Phase14.deltaC Phase14.primitive
  ring

theorem C16_strict : Phase15.C15 < C16 := by
  rw [C15_identity]
  unfold C16
  linarith only [Gamma_strict]

theorem C16_pos : 0 < C16 := Phase15.C15_pos.trans C16_strict

end
end Wu2008DoubleSieve.Phase16
