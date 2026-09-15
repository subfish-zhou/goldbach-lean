import WSrcFourEnclosureCompare

noncomputable section
open Real Set MeasureTheory Wu2008DoubleSieve FourRoughClosedMass
open Wu08OriginalFourWeights

namespace WuSource.SrcFourEnclosure

def cut : ℝ := 1/10
def smallW (x : ℝ) : ℝ :=
  (36/5)*(log x-log (1-x)-(log alpha-log (1-alpha)))
def smallQ (x : ℝ) : ℝ := (36/5)*(1/alpha-1/x)+smallW x*(1-1/x)
def largeW (x : ℝ) : ℝ := smallW cut+8*(log x-log cut)
def largeQ (x : ℝ) : ℝ :=
  smallQ cut+(smallW cut+8)/cut-(largeW x+8)/x
def smallF (x : ℝ) : ℝ := smallQ x*cross x/x
def largeF (x : ℝ) : ℝ := largeQ x*cross x/x

theorem smallW_derivative {x : ℝ} (hx0 : x ≠ 0) (hx1 : 1-x ≠ 0) :
    HasDerivAt smallW ((36/5)/(x*(1-x))) x := by
  have hd := (((hasDerivAt_log hx0).sub
    (((hasDerivAt_id x).const_sub 1).log hx1)).sub_const
      (log alpha-log (1-alpha))).const_mul (36/5)
  convert hd using 1 <;> first | rfl | (dsimp; field_simp; ring)

theorem smallQ_derivative {x : ℝ} (hx0 : x ≠ 0) (hx1 : 1-x ≠ 0) :
    HasDerivAt smallQ (smallW x/x^2) x := by
  have hrec := (hasDerivAt_const x (1 : ℝ)).div (hasDerivAt_id x) hx0
  have hd := ((hrec.const_sub (1/alpha)).const_mul (36/5)).add
    ((smallW_derivative hx0 hx1).mul (hrec.const_sub 1))
  convert hd using 1 <;> first | rfl | (dsimp; field_simp; ring)

theorem largeW_derivative {x : ℝ} (hx0 : x ≠ 0) :
    HasDerivAt largeW (8/x) x := by
  convert (((hasDerivAt_log hx0).sub_const (log cut)).const_mul 8).const_add
    (smallW cut) using 1 <;> rfl

theorem largeQ_derivative {x : ℝ} (hx0 : x ≠ 0) :
    HasDerivAt largeQ (largeW x/x^2) x := by
  have hd := (((largeW_derivative hx0).add_const 8).div (hasDerivAt_id x) hx0).const_sub
    (smallQ cut+(smallW cut+8)/cut)
  convert hd using 1 <;> first | rfl | (dsimp; field_simp; ring)

theorem primitives_boundary :
    smallW alpha = 0 ∧ smallQ alpha = 0 ∧
      largeW cut = smallW cut ∧ largeQ cut = smallQ cut ∧ G beta = 0 ∧ H beta = 0 := by
  simp [smallW,smallQ,largeW,largeQ,G,H]

theorem reduction_piece {a b : ℝ} {W Q w : ℝ → ℝ}
    (ha : alpha ≤ a) (hab : a ≤ b) (hb : b ≤ beta)
    (hW : ∀ x ∈ Icc a b, HasDerivAt W (w x) x)
    (hQ : ∀ x ∈ Icc a b, HasDerivAt Q (W x/x^2) x)
    (hw : ContinuousOn w (Icc a b)) :
    (∫ x in a..b, w x*H x) =
      W b*H b-W a*H a+Q b*G b-Q a*G a+
        ∫ x in a..b, Q x*density x := by
  have hWc : ContinuousOn W (Icc a b) :=
    fun x hx => (hW x hx).continuousAt.continuousWithinAt
  have hWi : IntervalIntegrable (fun x => W x/x^2) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hab]
    exact hWc.div (continuousOn_id.pow 2) (fun x hx =>
      pow_ne_zero _ (geometry.1.trans_le (ha.trans hx.1)).ne')
  have h1 := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (fun x _ => H_derivative x)
    (fun x hx => hW x (by rwa [uIcc_of_le hab] at hx))
    ((H_integrand_continuous.neg).intervalIntegrable (μ := volume) a b)
    (by rw [← uIcc_of_le hab] at hw; exact hw.intervalIntegrable)
  have h2 := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (fun x _ => G_derivative x)
    (fun x hx => hQ x (by rwa [uIcc_of_le hab] at hx))
    ((density_continuous.neg).intervalIntegrable (μ := volume) a b) hWi
  have e1 : (∫ x in a..b, (-(G x/(clamp x)^2))*W x) =
      -(∫ x in a..b, G x*(W x/x^2)) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le hab] at hx
    dsimp only
    rw [clamp_eq ⟨ha.trans hx.1,hx.2.trans hb⟩]
    ring
  have e2 : (∫ x in a..b, (-density x)*Q x) =
      -(∫ x in a..b, Q x*density x) := by
    rw [← intervalIntegral.integral_neg]
    congr 1
    funext x
    ring
  rw [e1] at h1
  rw [e2] at h2
  have e0 : (∫ x in a..b, w x*H x) = ∫ x in a..b, H x*w x := by
    congr 1
    funext x
    ring
  rw [e0]
  linarith only [h1,h2]

theorem mass_one_dimensional :
    mass = (∫ x in alpha..cut, smallF x)+(∫ x in cut..beta, largeF x) := by
  have hac : alpha ≤ cut := geometry.2.2.2.2.2.1
  have hcb : cut ≤ beta := geometry.2.2.2.2.2.2
  have hlow := reduction_piece (W := smallW) (Q := smallQ)
    (w := fun x => (36/5)/(x*(1-x))) (le_refl alpha) hac hcb
    (fun x hx => smallW_derivative (geometry.1.trans_le hx.1).ne' (by
      have hx1 : x ≤ (1/10 : ℝ) := hx.2
      linarith only [hx1]))
    (fun x hx => smallQ_derivative (geometry.1.trans_le hx.1).ne' (by
      have hx1 : x ≤ (1/10 : ℝ) := hx.2
      linarith only [hx1]))
    (continuousOn_const.div (continuousOn_id.mul (continuousOn_const.sub continuousOn_id))
      (fun x hx => mul_ne_zero (geometry.1.trans_le hx.1).ne' (by
        have hx1 : x ≤ (1/10 : ℝ) := hx.2
        linarith only [hx1])))
  have hhigh := reduction_piece (W := largeW) (Q := largeQ)
    (w := fun x => 8/x) hac hcb (le_refl beta)
    (fun x hx => largeW_derivative (geometry.1.trans_le (hac.trans hx.1)).ne')
    (fun x hx => largeQ_derivative (geometry.1.trans_le (hac.trans hx.1)).ne')
    (continuousOn_const.div continuousOn_id
      (fun x hx => (geometry.1.trans_le (hac.trans hx.1)).ne'))
  obtain ⟨hwa,hqa,hwc,hqc,hgb,hhb⟩ := primitives_boundary
  rw [hwa,hqa,zero_mul,zero_mul] at hlow
  rw [hwc,hqc,hgb,hhb,mul_zero,mul_zero] at hhigh
  have elo : (36/5)*(∫ x in alpha..cut, outerMass x/(1-x)) =
      ∫ x in alpha..cut, (36/5)/(x*(1-x))*H x := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le hac] at hx
    dsimp only
    rw [outerMass,clamp_eq ⟨hx.1,hx.2.trans hcb⟩]
    simp only [div_mul_eq_div_div]
    ring
  have ehi : 8*(∫ x in cut..beta, outerMass x) =
      ∫ x in cut..beta, (8/x)*H x := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le hcb] at hx
    dsimp only
    rw [outerMass,clamp_eq ⟨hac.trans hx.1,hx.2⟩]
    ring
  have eflow : (∫ x in alpha..cut, smallQ x*density x) =
      ∫ x in alpha..cut, smallF x := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le hac] at hx
    dsimp only
    rw [density_eq ⟨hx.1,hx.2.trans hcb⟩]
    unfold smallF
    ring
  have efhigh : (∫ x in cut..beta, largeQ x*density x) =
      ∫ x in cut..beta, largeF x := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le hcb] at hx
    dsimp only
    rw [density_eq ⟨hac.trans hx.1,hx.2⟩]
    unfold largeF
    ring
  rw [eflow] at hlow
  rw [efhigh] at hhigh
  unfold mass original
  change (36/5)*(∫ x in alpha..cut, outerMass x/(1-x))+
    8*(∫ x in cut..beta, outerMass x) = _
  rw [elo,ehi]
  linarith only [hlow,hhigh]

#check @mass_one_dimensional
#print axioms mass_one_dimensional
end WuSource.SrcFourEnclosure
