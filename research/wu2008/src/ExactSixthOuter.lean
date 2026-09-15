import ExactSixthInner

namespace Wu2008DoubleSieve.Phase25
open Real Set MeasureTheory ClassicalAnalyticLeaves SharpLogRecurrence SharpMassBalance
open PositiveSixthFTC DynamicSixthEnvelope
open scoped Interval
noncomputable section

def reciprocalPart (c : ℝ) : ℝ :=
  -T2 c (2*a)*(1/(c-b)-1/(2*a))-
  (T3 c (2*a)/2)*(1/(c-b)^2-1/(2*a)^2)-
  (T4 c (2*a)/3)*(1/(c-b)^3-1/(2*a)^3)
def rationalInner (c : ℝ) : ℝ :=
  (S c (2*a)*(lowerLog ((c-b)/(2*a))+lowerLog ((c-2*a)/b))+reciprocalPart c)/(1/2-c)

theorem endpoint_difference {c : ℝ} (hcb : 0 < c-b) (hca : 0 < c-2*a) :
    P c (2*a) (c-b)-P c (2*a) (2*a) =
      S c (2*a)*(log ((c-b)/(2*a))+log ((c-2*a)/b))+reciprocalPart c := by
  have ha : 2*a ≠ 0 := mul_ne_zero (by norm_num) geometry.1.ne'
  rw [log_div hcb.ne' ha,log_div hca.ne' geometry.2.2.1.ne']
  have he : c-(c-b) = b := by ring
  unfold P reciprocalPart
  rw [he]
  simp only [div_eq_mul_inv,← inv_pow]
  ring

theorem movingExact_endpoint (x : ℝ) :
    movingExact x = (P (1/2-x) (2*a) (1/2-x-b)-P (1/2-x) (2*a) (2*a))/x := by
  have he : 1/2-x-(lam-x) = 2*a := by unfold lam; ring
  unfold movingExact innerPrimitive
  rw [he]
  ring

theorem outer_geometry {x : ℝ} (hx : x ∈ Icc a b) :
    0 < x ∧ 0 < 1/2-x ∧ 0 < 1/2-x-b ∧ 0 < 1/2-x-2*a ∧
      2*a+b ≤ 1/2-x := by
  have hg := mask_geometry hx (left_mem_Icc.mpr (moving_geometry hx).1)
  have hb := geometry.2.2.1
  have hu := (moving_geometry hx).1
  dsimp [lam] at hu
  exact ⟨hg.1,hg.2.2.1,hg.2.2.2.1,by linarith,by linarith⟩

theorem rationalInner_lower {x : ℝ} (hx : x ∈ Icc a b) :
    rationalInner (1/2-x) ≤ movingExact x := by
  have hg := outer_geometry hx
  have h1 : 1 ≤ (1/2-x-b)/(2*a) :=
    (le_div_iff₀ (mul_pos (by norm_num) geometry.1)).mpr (by linarith [hg.2.2.2.2])
  have h2 : 1 ≤ (1/2-x-2*a)/b :=
    (le_div_iff₀ geometry.2.2.1).mpr (by linarith [hg.2.2.2.2])
  have hs := S_pos (h := 2*a) hg.2.1 (by linarith [hg.2.2.2.1])
  have hl := mul_le_mul_of_nonneg_left (add_le_add (log_lower h1) (log_lower h2)) hs.le
  rw [movingExact_endpoint,endpoint_difference hg.2.2.1 hg.2.2.2.1]
  unfold rationalInner
  have he : (1/2 : ℝ)-(1/2-x) = x := by ring
  rw [he]
  exact div_le_div_of_nonneg_right (add_le_add hl (le_refl _)) hg.1.le

/-- Original lowerLog, merely cleared into its fixed linear denominators. -/
theorem rationalInner_form {c : ℝ} :
    rationalInner c = (S c (2*a)*
      (2*((c-b-2*a)/(c-b+2*a))+(2/3)*((c-b-2*a)/(c-b+2*a))^3+
        (2*((c-2*a-b)/(c-2*a+b))+(2/3)*((c-2*a-b)/(c-2*a+b))^3))+
      reciprocalPart c)/(1/2-c) := by
  unfold rationalInner lowerLog
  have ha : (2*a : ℝ) ≠ 0 := mul_ne_zero (by norm_num) geometry.1.ne'
  have hb := geometry.2.2.1.ne'
  have ratio (u v : ℝ) (hv : v ≠ 0) : (u/v-1)/(u/v+1) = (u-v)/(u+v) := by
    have hn : u/v-1 = (u-v)/v := by field_simp
    have hd : u/v+1 = (u+v)/v := by field_simp
    rw [hn,hd,div_div_div_cancel_right₀ hv]
  rw [ratio (c-b) (2*a) ha,ratio (c-2*a) b hb]
  ring

theorem rationalInner_integrable :
    IntervalIntegrable (fun x => rationalInner (1/2-x)) volume a b := by
  apply ContinuousOn.intervalIntegrable
  have hg (x : ℝ) (hx : x ∈ uIcc a b) := outer_geometry (uIcc_of_le geometry.2.1 ▸ hx)
  have hi : ContinuousOn (fun x : ℝ => x⁻¹) (uIcc a b) :=
    continuousOn_id.inv₀ (fun x hx => (hg x hx).1.ne')
  have hc : ContinuousOn (fun x : ℝ => (1/2-x)⁻¹) (uIcc a b) :=
    (continuousOn_const.sub continuousOn_id).inv₀ (fun x hx => (hg x hx).2.1.ne')
  have hb : ContinuousOn (fun x : ℝ => (1/2-x-b)⁻¹) (uIcc a b) :=
    ((continuousOn_const.sub continuousOn_id).sub continuousOn_const).inv₀
      (fun x hx => (hg x hx).2.2.1.ne')
  have hp : ContinuousOn (fun x : ℝ => (1/2-x-b+2*a)⁻¹) (uIcc a b) :=
    (((continuousOn_const.sub continuousOn_id).sub continuousOn_const).add continuousOn_const).inv₀
      (fun x hx => ne_of_gt (by dsimp; linarith [(hg x hx).2.2.1,geometry.1]))
  have hm : ContinuousOn (fun x : ℝ => (1/2-x-2*a+b)⁻¹) (uIcc a b) :=
    (((continuousOn_const.sub continuousOn_id).sub continuousOn_const).add continuousOn_const).inv₀
      (fun x hx => ne_of_gt (by dsimp; linarith [(hg x hx).2.2.2.1,geometry.2.2.1]))
  simp only [rationalInner_form,S,reciprocalPart,T2,T3,T4]
  have he (x : ℝ) : (1/2 : ℝ)-(1/2-x) = x := by ring
  simp only [he]
  simp only [div_eq_mul_inv,mul_inv_rev,← inv_pow]
  simp only [div_eq_mul_inv] at hc hb hp hm
  fun_prop

/-- One comparison with the actual F6 integral, with the complement paid once. -/
theorem actual_sixth_ge_rationalInner :
    (4*∫ x in a..b, rationalInner (1/2-x)) ≤ truncatedSixthLowerF6lin := by
  have hc : Continuous (fun v : ℝ × ℝ => truncatedSixthZeroDeltaRegular 0 (v.1,v.2)) :=
    truncatedSixthZeroDelta_regular_continuous.comp (f := fun v : ℝ × ℝ => (0,v)) (by fun_prop)
  have hinner : Continuous (fun x : ℝ => ∫ y in b..s, truncatedSixthZeroDeltaRegular 0 (x,y)) := by
    apply gamma5Gain_moving_integral
      (f := fun x y : ℝ => truncatedSixthZeroDeltaRegular 0 (x,y)) hc <;> fun_prop
  have hpoint (x : ℝ) (hx : x ∈ Icc a b) : rationalInner (1/2-x) ≤
      ∫ y in b..s, truncatedSixthZeroDeltaRegular 0 (x,y) := by
    have hc1 := hc.comp (f := fun y : ℝ => (x,y)) (by fun_prop)
    have hi := intervalIntegral.integral_mono_on (μ := volume) (moving_geometry hx).1
      (inner_integrable hx) (hc1.intervalIntegrable b (lam-x))
      (fun y hy => retained_exact_lower hx hy)
    rw [inner_ftc hx] at hi
    have hn : 0 ≤ ∫ y in (lam-x)..s, truncatedSixthZeroDeltaRegular 0 (x,y) :=
      intervalIntegral.integral_nonneg (moving_geometry hx).2
        (fun y hy => ClassicalPositiveBounds.sixth_regular_nonneg hx
          ⟨(moving_geometry hx).1.trans hy.1,hy.2⟩)
    have he := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (hc1.intervalIntegrable b (lam-x)) (hc1.intervalIntegrable (lam-x) s)
    simp only [Function.comp_apply] at hi he
    linarith [rationalInner_lower hx]
  have hi := intervalIntegral.integral_mono_on (μ := volume) geometry.2.1
    rationalInner_integrable (hinner.intervalIntegrable a b) hpoint
  have he := truncatedSixthZeroDelta_extension_eq (by norm_num : (0 : ℝ) ≤ 0)
  change (4*∫ x in a..b, ∫ y in b..s, truncatedSixthZeroDeltaRegular 0 (x,y)) =
    truncatedSixthLowerF6lin at he
  linarith

def polez : ℝ := (0/1 : ℝ)
def qz1 : ℝ := (-49567200438732775104505597343750/23008349855801338564177287 : ℝ)
def qz2 : ℝ := (1075528748514450781250000/74431051250800938669 : ℝ)
def qz3 : ℝ := (-37286775935937500000000/74431051250800938669 : ℝ)
def poleb : ℝ := (25/206 : ℝ)
def qb1 : ℝ := (11427930937637312/1247524545012993 : ℝ)
def qb2 : ℝ := (-12231922384000/31987808846487 : ℝ)
def qb3 : ℝ := (13579520000/820200226833 : ℝ)
def polem : ℝ := (-8025/273362 : ℝ)
def qm1 : ℝ := (5881521176595880647341526130945946624/3729428911866529810567814389353 : ℝ)
def qm2 : ℝ := (3363828436053428489284198400/160576045277259764403081 : ℝ)
def qm3 : ℝ := (1790845239135518720000/9174662665813102599 : ℝ)
def polep : ℝ := (8025/273362 : ℝ)
def qp1 : ℝ := (47281093382566382680686050047210345/81907349569106498625605362704 : ℝ)
def qp2 : ℝ := (-24028082877059327513590975/3966594372121038683058 : ℝ)
def qp3 : ℝ := (3023249857471697500/79142529336307767 : ℝ)
def kx : ℝ := (12963658609426086898463268417154149083835937/3930690938520897436844665512632963691908496 : ℝ)

theorem outer_partial_fractions {c : ℝ} (hc : c ≠ 0) (hb : c-b ≠ 0)
    (hm : c-b+2*a ≠ 0) (hp : c-2*a+b ≠ 0) (hx : 1/2-c ≠ 0) :
    rationalInner c = qz1/(c-polez)^1+qz2/(c-polez)^2+qz3/(c-polez)^3+qb1/(c-poleb)^1+qb2/(c-poleb)^2+qb3/(c-poleb)^3+qm1/(c-polem)^1+qm2/(c-polem)^2+qm3/(c-polem)^3+qp1/(c-polep)^1+qp2/(c-polep)^2+qp3/(c-polep)^3+kx/(1/2-c) := by
  rw [rationalInner_form]
  have em : c-b+2*a = c-polem := by
    norm_num [polem,a,b,truncatedSixthLowerAlpha,truncatedSixthLowerBeta]
    ring
  have ep : c-2*a+b = c-polep := by
    norm_num [polep,a,b,truncatedSixthLowerAlpha,truncatedSixthLowerBeta]
    ring
  rw [em] at hm
  rw [ep] at hp
  unfold S reciprocalPart T2 T3 T4
  rw [em,ep]
  change c-b ≠ 0 at hb
  have hz : c-polez ≠ 0 := by simpa only [polez,zero_div,sub_zero] using hc
  have hb' : c-poleb ≠ 0 := hb
  have hx' : 1-2*c ≠ 0 := by intro h; apply hx; linarith
  field_simp [hc,hb,hm,hp,hx,hx',hz,hb',geometry.1.ne']
  norm_num [qz1,qz2,qz3,qb1,qb2,qb3,qm1,qm2,qm3,qp1,qp2,qp3,kx,polez,poleb,polem,polep,a,b,truncatedSixthLowerAlpha,truncatedSixthLowerBeta]
  field_simp [hx']
  ring

theorem denom_z {x : ℝ} (hx : x ∈ Icc a b) : (1/2-x-polez) ≠ 0 := by
  have hl := hx.1
  have hu := hx.2
  norm_num [polez,a,b,truncatedSixthLowerAlpha,truncatedSixthLowerBeta] at hl hu ⊢
  linarith

theorem denom_b {x : ℝ} (hx : x ∈ Icc a b) : (1/2-x-poleb) ≠ 0 := by
  have hl := hx.1
  have hu := hx.2
  norm_num [poleb,a,b,truncatedSixthLowerAlpha,truncatedSixthLowerBeta] at hl hu ⊢
  linarith

theorem denom_m {x : ℝ} (hx : x ∈ Icc a b) : (1/2-x-polem) ≠ 0 := by
  have hl := hx.1
  have hu := hx.2
  norm_num [polem,a,b,truncatedSixthLowerAlpha,truncatedSixthLowerBeta] at hl hu ⊢
  linarith

theorem denom_p {x : ℝ} (hx : x ∈ Icc a b) : (1/2-x-polep) ≠ 0 := by
  have hl := hx.1
  have hu := hx.2
  norm_num [polep,a,b,truncatedSixthLowerAlpha,truncatedSixthLowerBeta] at hl hu ⊢
  linarith

def outerPrimitive (x : ℝ) : ℝ := -qz1*log (1/2-x-polez)+qz2/(1/2-x-polez)+(qz3/2)/(1/2-x-polez)^2+-qb1*log (1/2-x-poleb)+qb2/(1/2-x-poleb)+(qb3/2)/(1/2-x-poleb)^2+-qm1*log (1/2-x-polem)+qm2/(1/2-x-polem)+(qm3/2)/(1/2-x-polem)^2+-qp1*log (1/2-x-polep)+qp2/(1/2-x-polep)+(qp3/2)/(1/2-x-polep)^2+kx*log x

theorem outer_derivative {x : ℝ} (hx : x ∈ Icc a b) :
    HasDerivAt outerPrimitive (rationalInner (1/2-x)) x := by
  have hg := outer_geometry hx
  have hplus : 1/2-x-b+2*a ≠ 0 := ne_of_gt (by linarith [hg.2.2.1,geometry.1])
  have hminus : 1/2-x-2*a+b ≠ 0 := ne_of_gt (by linarith [hg.2.2.2.1,geometry.2.2.1])
  have he : (1/2 : ℝ)-(1/2-x) = x := by ring
  rw [outer_partial_fractions hg.2.1.ne' hg.2.2.1.ne' hplus hminus (by rw [he]; exact hg.1.ne')]
  have hi := hasDerivAt_id x
  have hz := ((hasDerivAt_const x (1/2)).sub hi).sub_const polez
  have nz := denom_z hx
  have hb := ((hasDerivAt_const x (1/2)).sub hi).sub_const poleb
  have nb := denom_b hx
  have hm := ((hasDerivAt_const x (1/2)).sub hi).sub_const polem
  have nm := denom_m hx
  have hp := ((hasDerivAt_const x (1/2)).sub hi).sub_const polep
  have np := denom_p hx
  have hh := ((((((((((((((hz.log nz).const_mul (-qz1)).add ((hasDerivAt_const x qz2).div hz nz)).add ((hasDerivAt_const x (qz3/2)).div (hz.pow 2) (pow_ne_zero 2 nz))).add ((hb.log nb).const_mul (-qb1))).add ((hasDerivAt_const x qb2).div hb nb)).add ((hasDerivAt_const x (qb3/2)).div (hb.pow 2) (pow_ne_zero 2 nb))).add ((hm.log nm).const_mul (-qm1))).add ((hasDerivAt_const x qm2).div hm nm)).add ((hasDerivAt_const x (qm3/2)).div (hm.pow 2) (pow_ne_zero 2 nm))).add ((hp.log np).const_mul (-qp1))).add ((hasDerivAt_const x qp2).div hp np)).add ((hasDerivAt_const x (qp3/2)).div (hp.pow 2) (pow_ne_zero 2 np))).add ((hasDerivAt_log hg.1.ne').const_mul kx))
  convert hh using 1 <;> first | rfl | (dsimp; rw [he]; field_simp; ring)

theorem outer_ftc : (∫ x in a..b, rationalInner (1/2-x)) = outerPrimitive b-outerPrimitive a := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ rationalInner_integrable
  intro x hx
  exact outer_derivative (uIcc_of_le geometry.2.1 ▸ hx)

def endpointRational : ℝ := (33678387181268310556885537322035150708517049568461764641271526987249685214570003715110614375/4738584818907605306315465904230855025476857806725356199958508881763696755498190989580206 : ℝ)
theorem endpointRational_identity : endpointRational = qz2*(1/(1/2-b-polez)-1/(1/2-a-polez))+(qz3/2)*(1/(1/2-b-polez)^2-1/(1/2-a-polez)^2)+qb2*(1/(1/2-b-poleb)-1/(1/2-a-poleb))+(qb3/2)*(1/(1/2-b-poleb)^2-1/(1/2-a-poleb)^2)+qm2*(1/(1/2-b-polem)-1/(1/2-a-polem))+(qm3/2)*(1/(1/2-b-polem)^2-1/(1/2-a-polem)^2)+qp2*(1/(1/2-b-polep)-1/(1/2-a-polep))+(qp3/2)*(1/(1/2-b-polep)^2-1/(1/2-a-polep)^2) := by
  norm_num [endpointRational,qz1,qz2,qz3,qb1,qb2,qb3,qm1,qm2,qm3,qp1,qp2,qp3,kx,polez,poleb,polem,polep,a,b,truncatedSixthLowerAlpha,truncatedSixthLowerBeta]

def ratioz : ℝ := (1/2-a-polez)/(1/2-b-polez)
def ratiob : ℝ := (1/2-a-poleb)/(1/2-b-poleb)
def ratiom : ℝ := (1/2-a-polem)/(1/2-b-polem)
def ratiop : ℝ := (1/2-a-polep)/(1/2-b-polep)
theorem endpoint_exact : outerPrimitive b-outerPrimitive a = endpointRational+qz1*log ratioz+qb1*log ratiob+qm1*log ratiom+qp1*log ratiop+kx*log (b/a) := by
  rw [endpointRational_identity]
  have ha := left_mem_Icc.mpr geometry.2.1
  have hb := right_mem_Icc.mpr geometry.2.1
  simp only [ratioz,ratiob,ratiom,ratiop]
  rw [log_div (denom_z ha) (denom_z hb),log_div (denom_b ha) (denom_b hb),log_div (denom_m ha) (denom_m hb),log_div (denom_p ha) (denom_p hb),log_div geometry.2.2.1.ne' geometry.1.ne']
  unfold outerPrimitive
  ring

theorem residue_sum : qz1+qb1+qm1+qp1 = kx := by
  norm_num [qz1,qb1,qm1,qp1,kx]

def newSixth : ℝ := 4*(endpointRational+kx*lowerLog ratioz+
  qb1*lowerLog (ratiob/ratioz)-qm1*upperLog (ratioz/ratiom)+
  qp1*lowerLog (ratiop/ratioz)+kx*lowerLog (b/a))

theorem newSixth_lower : newSixth ≤ 4*(outerPrimitive b-outerPrimitive a) := by
  have h0 := log_lower (t := ratioz) (by norm_num [ratioz,ratiob,ratiom,ratiop,polez,poleb,polem,polep,a,b,truncatedSixthLowerAlpha,truncatedSixthLowerBeta])
  have h1 := log_lower (t := ratiob/ratioz) (by norm_num [ratioz,ratiob,ratiom,ratiop,polez,poleb,polem,polep,a,b,truncatedSixthLowerAlpha,truncatedSixthLowerBeta])
  have h2 := log_upper (t := ratioz/ratiom) (by norm_num [ratioz,ratiob,ratiom,ratiop,polez,poleb,polem,polep,a,b,truncatedSixthLowerAlpha,truncatedSixthLowerBeta])
  have h3 := log_lower (t := ratiop/ratioz) (by norm_num [ratioz,ratiob,ratiom,ratiop,polez,poleb,polem,polep,a,b,truncatedSixthLowerAlpha,truncatedSixthLowerBeta])
  have h4 := log_lower (t := b/a) (by norm_num [ratioz,ratiob,ratiom,ratiop,polez,poleb,polem,polep,a,b,truncatedSixthLowerAlpha,truncatedSixthLowerBeta])
  have nz : ratioz ≠ 0 := by norm_num [ratioz,ratiob,ratiom,ratiop,polez,poleb,polem,polep,a,b,truncatedSixthLowerAlpha,truncatedSixthLowerBeta]
  have nb : ratiob ≠ 0 := by norm_num [ratioz,ratiob,ratiom,ratiop,polez,poleb,polem,polep,a,b,truncatedSixthLowerAlpha,truncatedSixthLowerBeta]
  have nm : ratiom ≠ 0 := by norm_num [ratioz,ratiob,ratiom,ratiop,polez,poleb,polem,polep,a,b,truncatedSixthLowerAlpha,truncatedSixthLowerBeta]
  have np : ratiop ≠ 0 := by norm_num [ratioz,ratiob,ratiom,ratiop,polez,poleb,polem,polep,a,b,truncatedSixthLowerAlpha,truncatedSixthLowerBeta]
  rw [log_div nb nz] at h1
  rw [log_div nz nm] at h2
  rw [log_div np nz] at h3
  have p0 : 0 ≤ kx := by norm_num [kx]
  have p1 : 0 ≤ qb1 := by norm_num [qb1]
  have p2 : 0 ≤ qm1 := by norm_num [qm1]
  have p3 : 0 ≤ qp1 := by norm_num [qp1]
  have h0p := mul_le_mul_of_nonneg_left h0 p0
  have h1p := mul_le_mul_of_nonneg_left h1 p1
  have h2p := mul_le_mul_of_nonneg_left h2 p2
  have h3p := mul_le_mul_of_nonneg_left h3 p3
  have h4p := mul_le_mul_of_nonneg_left h4 p0
  rw [endpoint_exact]
  unfold newSixth
  have hs := residue_sum
  nlinarith only [h0p,h1p,h2p,h3p,h4p,congrArg (fun t => t*log ratioz) hs]

theorem actual_sixth_ge_new : newSixth ≤ truncatedSixthLowerF6lin := by
  have hh := actual_sixth_ge_rationalInner
  rw [outer_ftc] at hh
  exact newSixth_lower.trans hh

theorem strict_sixth_improvement :
    RationalMovingSixth.rationalSixth+SixthReciprocalCorrection.deltaSixth+
      SixthLogCubicCorrection.deltaLog < newSixth := by
  rw [SixthReciprocalCorrection.deltaSixth_exact,SixthLogCubicCorrection.deltaLog_exact]
  norm_num [newSixth,endpointRational,kx,qb1,qm1,qp1,ratioz,ratiob,ratiom,ratiop,polez,poleb,polem,polep,a,b,truncatedSixthLowerAlpha,truncatedSixthLowerBeta,lowerLog,upperLog,
    RationalMovingSixth.rationalSixth,RationalMovingSixth.quadraticCoefficient,
    RationalMovingSixth.linearCoefficient,RationalMovingSixth.constantCoefficient,
    RationalMovingSixth.initialLogCoefficient,RationalMovingSixth.terminalLogCoefficient,
    RationalMovingSixth.e,m,lam]


end
end Wu2008DoubleSieve.Phase25
