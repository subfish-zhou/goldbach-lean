import CompleteReciprocalKernel
import CoupledEndpointFeedback

namespace Wu2008DoubleSieve.Phase18
open Real Set MeasureTheory HighSixPhase9 SingleUpperHSource SingleUpperHIntegral Phase11 Phase12
open Phase16 (L0 r0 movingRight fixed_geometry moving_geometry)
noncomputable section

structure Coeff where
  k0 : ℝ
  k1 : ℝ
  k2 : ℝ

def Coeff.Nonneg (k : Coeff) : Prop := 0 ≤ k.k0 ∧ 0 ≤ k.k1 ∧ 0 ≤ k.k2

def poly (k : Coeff) (v : ℝ) : ℝ := k.k0+k.k1*v+k.k2*v^2

def U (k : Coeff) : ℝ := (k.k0-k.k1*L0+k.k2*L0^2)/(1/2)
def V (k : Coeff) : ℝ := (k.k0+k.k1*(1/2-L0)+k.k2*(1/2-L0)^2)/(1/2)
def f (k : Coeff) (t : ℝ) : ℝ := poly k (t-L0)/(t*(1/2-t))
def logPrimitive (k : Coeff) (t : ℝ) : ℝ := -k.k2*t+U k*log t-V k*log (1/2-t)
def Gamma (k : Coeff) : ℝ := 2*(-k.k2*Phase14.w0+U k*log (r0/L0)+V k*log ((1/2-L0)/(1/2-r0)))
def M (k : Coeff) : ℝ := poly k Phase14.w0/(L0*(1/2-r0))
def C (k : Coeff) : ℝ := Ctail+Cmid+Gamma k
def movingC (k : Coeff) (δ : ℝ) : ℝ := Ctail+Cmid+2*∫ t in L0..movingRight δ, f k t

theorem poly_nonneg {k : Coeff} (hk : k.Nonneg) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ poly k x := by
  exact add_nonneg (add_nonneg hk.1 (mul_nonneg hk.2.1 hx)) (mul_nonneg hk.2.2 (sq_nonneg x))

theorem poly_mono {k : Coeff} (hk : k.Nonneg) {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) : poly k x ≤ poly k y := by
  have h1 := mul_le_mul_of_nonneg_left hxy hk.2.1
  have h2 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx hxy 2) hk.2.2
  unfold poly
  linarith only [h1,h2]

theorem partial_fraction (k : Coeff) {t : ℝ} (ht : 0 < t) (htc : t < 1/2) :
    f k t = -k.k2+U k/t+V k/(1/2-t) := by
  have ht' : t ≠ 0 := ne_of_gt ht
  have hc : 1/2-t ≠ 0 := ne_of_gt (sub_pos.mpr htc)
  unfold f poly U V
  field_simp [ht',hc,show 1-t*2 ≠ 0 by linarith]
  ring

theorem f_continuous (k : Coeff) : ContinuousOn (f k) (Icc L0 r0) := by
  apply ContinuousOn.div
  · unfold poly
    fun_prop
  · fun_prop
  · intro t ht
    exact ne_of_gt (mul_pos (lt_of_lt_of_le fixed_geometry.1 ht.1)
      (sub_pos.mpr (lt_of_le_of_lt ht.2 fixed_geometry.2.2.1)))

theorem f_integrable (k : Coeff) {a b : ℝ} (ha : L0 ≤ a) (hab : a ≤ b) (hb : b ≤ r0) :
    IntervalIntegrable (f k) volume a b :=
  ((f_continuous k).mono (Icc_subset_Icc ha hb)).intervalIntegrable_of_Icc hab

theorem logPrimitive_deriv (k : Coeff) {t : ℝ} (ht : 0 < t) (htc : t < 1/2) :
    HasDerivAt (logPrimitive k) (f k t) t := by
  have h := (hasDerivAt_const t (1/2 : ℝ)).sub (hasDerivAt_id t)
  have hd := (((hasDerivAt_id t).const_mul (-k.k2)).add
    ((hasDerivAt_log (ne_of_gt ht)).const_mul (U k))).sub
      ((h.log (ne_of_gt (sub_pos.mpr htc))).const_mul (V k))
  rw [partial_fraction k ht htc]
  convert hd using 1 <;> first | rfl | (dsimp; ring)

theorem fixed_integral_closed (k : Coeff) : Gamma k = 2*∫ t in L0..r0, f k t := by
  have hi := f_integrable k le_rfl fixed_geometry.2.1.le le_rfl
  have hf := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => logPrimitive_deriv k
      (lt_of_lt_of_le fixed_geometry.1 (uIcc_of_le fixed_geometry.2.1.le ▸ ht).1)
      (lt_of_le_of_lt (uIcc_of_le fixed_geometry.2.1.le ▸ ht).2 fixed_geometry.2.2.1)) hi
  rw [hf]
  unfold Gamma logPrimitive
  rw [Real.log_div (ne_of_gt (by norm_num [Phase16.r0])) (ne_of_gt fixed_geometry.1),
    Real.log_div (ne_of_gt (by norm_num [Phase16.L0])) (ne_of_gt (by norm_num [Phase16.r0]))]
  rw [← fixed_geometry.2.2.2]
  ring

theorem f_bounds {k : Coeff} (hk : k.Nonneg) {t : ℝ} (ht : t ∈ Icc L0 r0) :
    0 ≤ f k t ∧ f k t ≤ M k := by
  have ht0 := lt_of_lt_of_le fixed_geometry.1 ht.1
  have hc := sub_pos.mpr (lt_of_le_of_lt ht.2 fixed_geometry.2.2.1)
  have hp := poly_nonneg hk (sub_nonneg.mpr ht.1)
  have hpoly := poly_mono hk (sub_nonneg.mpr ht.1)
    (show t-L0 ≤ Phase14.w0 by rw [← fixed_geometry.2.2.2]; linarith only [ht.2])
  have hden : L0*(1/2-r0) ≤ t*(1/2-t) :=
    mul_le_mul ht.1 (by linarith only [ht.2]) (by norm_num [Phase16.r0]) ht0.le
  constructor
  · exact div_nonneg hp (mul_pos ht0 hc).le
  · exact div_le_div₀ (hp.trans hpoly) hpoly (by norm_num [Phase16.L0,Phase16.r0]) hden

theorem strip_bounds {k : Coeff} (hk : k.Nonneg) {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100) :
    0 ≤ 2*∫ t in movingRight δ..r0, f k t ∧
      2*∫ t in movingRight δ..r0, f k t ≤ M k*δ := by
  have hg := moving_geometry hδ hδhi
  have hi := f_integrable k hg.2.2.1.le hg.2.2.2.1 le_rfl
  have hn := intervalIntegral.integral_nonneg (μ := volume) (a := movingRight δ) (b := r0)
    hg.2.2.2.1 (fun t ht => (f_bounds hk ⟨hg.2.2.1.le.trans ht.1,ht.2⟩).1)
  have hm := intervalIntegral.integral_mono_on hg.2.2.2.1 hi
    (intervalIntegrable_const (c := M k))
    (fun t ht => (f_bounds hk ⟨hg.2.2.1.le.trans ht.1,ht.2⟩).2)
  rw [intervalIntegral.integral_const] at hm
  simp only [smul_eq_mul] at hm
  rw [hg.2.2.2.2] at hm
  constructor <;> linarith only [hn,hm]

theorem movingC_bounds {k : Coeff} (hk : k.Nonneg) {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100) :
    0 ≤ movingC k δ ∧ movingC k δ ≤ C k ∧ C k-M k*δ ≤ movingC k δ := by
  have hg := moving_geometry hδ hδhi
  have hi := intervalIntegral.integral_add_adjacent_intervals
    (f_integrable k le_rfl hg.2.2.1.le hg.2.2.2.1)
    (f_integrable k hg.2.2.1.le hg.2.2.2.1 le_rfl)
  have hs := strip_bounds hk hδ hδhi
  have hn := intervalIntegral.integral_nonneg (μ := volume) hg.2.2.1.le
    (fun t ht => (f_bounds hk ⟨ht.1,ht.2.trans hg.2.2.2.1⟩).1)
  unfold movingC C
  rw [fixed_integral_closed k]
  constructor
  · linarith only [Ctail_pos,Cmid_pos,hn]
  constructor <;> linarith only [hi,hs.1,hs.2]

def old : Coeff := ⟨64/56511,21232/363285,1760929/187200⟩
def coupled : Coeff := ⟨3136/2360151,3333424/51136605,1760929/187200⟩
def Gamma18 : ℝ := Gamma coupled
def C18 : ℝ := C coupled
def M18 : ℝ := M coupled

theorem coupled_nonneg : coupled.Nonneg := by norm_num [Coeff.Nonneg,coupled]
theorem coupled_exact : U coupled = (41737566031/98182281600 : ℝ) ∧
    V coupled = (141660751/61363926 : ℝ) ∧
    M18 = (99532000231537/39960188611200 : ℝ) := by
  norm_num [U,V,M18,M,poly,coupled,Phase16.L0,Phase16.r0,Phase14.w0]

theorem old_poly (v : ℝ) : poly old v = Phase14.poly v := by
  norm_num [poly,old,Phase14.poly,Phase14.q1,Phase14.q2,Phase13.κH,Phase13.κh,truncatedSixthLowerAlpha]

theorem old_f (t : ℝ) : f old t = Phase16.f0 t := by rw [f,Phase16.f0,old_poly]
theorem old_Gamma : Gamma old = Phase16.Gamma := by
  rw [fixed_integral_closed,Phase16.fixed_integral_closed]
  simp_rw [old_f]
theorem old_C : C old = Phase16.C16 := by rw [C,Phase16.C16,old_Gamma]

theorem coupled_poly_strict {v : ℝ} (hv : 0 ≤ v) : poly old v < poly coupled v := by
  have hp : 0 ≤ (214103488/31755831705 : ℝ)*v := mul_nonneg (by norm_num) hv
  norm_num [poly,old,coupled] at *
  linarith only [hp]

theorem coupled_f_strict {t : ℝ} (ht : t ∈ Icc L0 r0) : f old t < f coupled t := by
  apply (div_lt_div_iff_of_pos_right (mul_pos (fixed_geometry.1.trans_le ht.1)
    (sub_pos.mpr (ht.2.trans_lt fixed_geometry.2.2.1)))).2
  exact coupled_poly_strict (sub_nonneg.mpr ht.1)

theorem Gamma18_strict : Phase16.Gamma < Gamma18 := by
  have hi := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
    fixed_geometry.2.1 (f_continuous old) (f_continuous coupled)
    (fun t ht => (coupled_f_strict ⟨ht.1.le,ht.2⟩).le)
    ⟨(L0+r0)/2, by constructor <;> linarith only [fixed_geometry.2.1],
      coupled_f_strict (by constructor <;> linarith only [fixed_geometry.2.1])⟩
  rw [← old_Gamma,fixed_integral_closed]
  unfold Gamma18
  rw [fixed_integral_closed]
  linarith only [hi]

theorem C18_strict : Phase16.C16 < C18 := by
  unfold Phase16.C16 C18 C
  have h := Gamma18_strict
  change Phase16.Gamma < Gamma coupled at h
  linarith only [h]
theorem C18_pos : 0 < C18 := Phase16.C16_pos.trans C18_strict
theorem M18_pos : 0 < M18 := by rw [coupled_exact.2.2]; norm_num

end
end Wu2008DoubleSieve.Phase18
