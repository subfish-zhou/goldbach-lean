import RetainedEndpointFeedback

namespace Wu2008DoubleSieve.Phase17
open Real Set MeasureTheory HighSixPhase9
noncomputable section

def X (δ : ℝ) : ℝ := wuImprovementLimit false δ (18/5)
def Y (δ : ℝ) : ℝ := wuImprovementLimit true δ (23/5)
def κX : ℝ := 20096/1136369
def κY : ℝ := 3136/2360151
def D : ℝ := (1-16/207)*(1-8/161)-(8/23)*(32/4347)

theorem determinant : D = (87413/99981 : ℝ) ∧ 0 < D ∧
    (0 : ℝ) < 1-16/207 ∧ (0 : ℝ) < 1-8/161 := by norm_num [D]
theorem kappa_identities :
    κX = ((128/8073)*(1-8/161)+(8/23)*(64/56511))/D ∧
    κY = ((64/56511)*(1-16/207)+(32/4347)*(128/8073))/D := by
  norm_num [κX,κY,D]
theorem kappa_strict : (128/8073 : ℝ) < κX ∧ (64/56511 : ℝ) < κY := by
  norm_num [κX,κY]
theorem κX_pos : 0 < κX := by norm_num [κX]
theorem κY_pos : 0 < κY := by norm_num [κY]
theorem X_nonneg {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100) : 0 ≤ X δ :=
  wuImprovementLimit_nonneg false hδ (by linarith) (by norm_num) (by norm_num)
theorem Y_nonneg {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100) : 0 ≤ Y δ :=
  wuImprovementLimit_nonneg true hδ (by linarith) (by norm_num) (by norm_num)

/-- One genuine FTC for the complete polynomial, with all coefficients retained. -/
theorem full_reverse_integral (a b c0 c1 c2 c3 : ℝ) :
    (∫ u in a..b, c0+c1*(b-u)+c2*(b-u)^2+c3*(b-u)^3) =
      c0*(b-a)+(c1/2)*(b-a)^2+(c2/3)*(b-a)^3+(c3/4)*(b-a)^4 := by
  have hd : ∀ u : ℝ, HasDerivAt
      (fun x : ℝ => -c0*(b-x)-(c1/2)*(b-x)^2-(c2/3)*(b-x)^3-(c3/4)*(b-x)^4)
      (c0+c1*(b-u)+c2*(b-u)^2+c3*(b-u)^3) u := by
    intro u
    have h := (hasDerivAt_const u b).sub (hasDerivAt_id u)
    convert (((h.const_mul (-c0)).sub ((h.pow 2).const_mul (c1/2))).sub
      ((h.pow 3).const_mul (c2/3))).sub ((h.pow 4).const_mul (c3/4)) using 1 <;>
      first | rfl | (norm_num; ring)
  have hi : IntervalIntegrable
      (fun u : ℝ => c0+c1*(b-u)+c2*(b-u)^2+c3*(b-u)^3) volume a b := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hf := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd u) hi
  calc
    _ = (-c0*(b-b)-(c1/2)*(b-b)^2-(c2/3)*(b-b)^3-(c3/4)*(b-b)^4)-
        (-c0*(b-a)-(c1/2)*(b-a)^2-(c2/3)*(b-a)^3-(c3/4)*(b-a)^4) := hf
    _ = _ := by ring

/-- The original integral comparison is rebuilt with its positive terminal retained. -/
theorem h_raw_affine {δ u : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100)
    (hu : u ∈ Icc (2 : ℝ) (18/5)) :
    X δ+amplitude δ*(5/13)*(18/5-u) ≤ wuImprovementLimit false δ u := by
  have hc := wuImprovementLimit_lower_cross (s := u) (t := (18/5 : ℝ))
    hδ (by linarith) hu.1 hu.2 (by norm_num)
  norm_num only at hc
  have hm : (∫ v in (u-1)..(13/5 : ℝ), (amplitude δ)*(5/13)) ≤
      ∫ v in (u-1)..(13/5 : ℝ), wuImprovementLimit true δ v/v := by
    apply intervalIntegral.integral_mono_on (by linarith [hu.2]) intervalIntegrable_const
      (wuImprovementLimit_div_intervalIntegrable true hδ (by linarith)
        (by linarith [hu.1]) (by linarith [hu.2]) (by norm_num))
    intro v hv
    have hs : amplitude δ ≤ wuImprovementLimit true δ v :=
      wuImprovementLimit_upper_antitone hδ (by linarith)
        ⟨by linarith [hu.1,hv.1],by linarith [hv.2]⟩
        ⟨by norm_num,by norm_num⟩ hv.2
    apply (le_div_iff₀ (by linarith [hu.1,hv.1])).2
    have hh := mul_le_mul_of_nonneg_left hv.2 (amplitude_nonneg hδ hδhi)
    nlinarith only [hs,hh]
  rw [intervalIntegral.integral_const,smul_eq_mul] at hm
  change X δ + _ ≤ _ at hc
  linarith only [hc,hm]

/-- Original cross and one complete polynomial comparison. -/
theorem H_raw_quadratic {δ s : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100)
    (hs : s ∈ Icc (3 : ℝ) (23/5)) :
    Y δ+X δ*(5/18)*(23/5-s)+amplitude δ*(25/468)*(23/5-s)^2 ≤ wuImprovementLimit true δ s := by
  have hc := wuImprovementLimit_upper_cross (s := s) (t := (23/5 : ℝ))
    hδ (by linarith) (by linarith [hs.1]) hs.2 (by norm_num)
  norm_num only at hc
  have hm : (∫ u in (s-1)..(18/5 : ℝ), (X δ*(5/18))+(amplitude δ*(5/13)*(5/18))*(18/5-u)^1+(0)*(18/5-u)^2+(0)*(18/5-u)^3) ≤
      ∫ u in (s-1)..(18/5 : ℝ), wuImprovementLimit false δ u/u := by
    apply intervalIntegral.integral_mono_on (by linarith [hs.2])
      (show IntervalIntegrable (fun u : ℝ => (X δ*(5/18))+(amplitude δ*(5/13)*(5/18))*(18/5-u)^1+(0)*(18/5-u)^2+(0)*(18/5-u)^3) volume (s-1) (18/5) from
        (by apply Continuous.intervalIntegrable; fun_prop))
      (wuImprovementLimit_div_intervalIntegrable false hδ (by linarith)
        (by linarith [hs.1]) (by linarith [hs.2]) (by norm_num))
    intro u hu
    have hl := h_raw_affine hδ hδhi ⟨by linarith [hs.1,hu.1],hu.2⟩
    have hA := amplitude_nonneg hδ hδhi
    have hX := X_nonneg hδ hδhi
    have hY := Y_nonneg hδ hδhi
    have hz : 0 ≤ 18/5-u := by linarith [hu.2]
    have hp : 0 ≤ X δ+amplitude δ*(5/13)*(18/5-u) := by positivity
    have hh := mul_le_mul_of_nonneg_left hu.2 hp
    apply (le_div_iff₀ (by linarith [hs.1,hu.1])).2
    nlinarith only [hl,hh]
  simp only [pow_one] at hm
  rw [full_reverse_integral] at hm
  change Y δ + _ ≤ _ at hc
  nlinarith only [hc,hm]

/-- Original cross and one complete polynomial comparison. -/
theorem h_raw_cubic {δ s : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100)
    (hs : s ∈ Icc (4 : ℝ) (28/5)) :
    (5/23)*(Y δ*(28/5-s)+((5/18)/2)*X δ*(28/5-s)^2+((25/468)/3)*amplitude δ*(28/5-s)^3) ≤ wuImprovementLimit false δ s := by
  have hc := wuImprovementLimit_lower_cross (s := s) (t := (28/5 : ℝ))
    hδ (by linarith) (by linarith [hs.1]) hs.2 (by norm_num)
  norm_num only at hc
  have hn := wuImprovementLimit_nonneg false hδ (by linarith : δ < 1/2)
    (s := (28/5 : ℝ)) (by norm_num) (by norm_num)
  have hm : (∫ u in (s-1)..(23/5 : ℝ), (Y δ*(5/23))+(X δ*(5/18)*(5/23))*(23/5-u)^1+(amplitude δ*(25/468)*(5/23))*(23/5-u)^2+(0)*(23/5-u)^3) ≤
      ∫ u in (s-1)..(23/5 : ℝ), wuImprovementLimit true δ u/u := by
    apply intervalIntegral.integral_mono_on (by linarith [hs.2])
      (show IntervalIntegrable (fun u : ℝ => (Y δ*(5/23))+(X δ*(5/18)*(5/23))*(23/5-u)^1+(amplitude δ*(25/468)*(5/23))*(23/5-u)^2+(0)*(23/5-u)^3) volume (s-1) (23/5) from
        (by apply Continuous.intervalIntegrable; fun_prop))
      (wuImprovementLimit_div_intervalIntegrable true hδ (by linarith)
        (by linarith [hs.1]) (by linarith [hs.2]) (by norm_num))
    intro u hu
    have hl := H_raw_quadratic hδ hδhi ⟨by linarith [hs.1,hu.1],hu.2⟩
    have hA := amplitude_nonneg hδ hδhi
    have hX := X_nonneg hδ hδhi
    have hY := Y_nonneg hδ hδhi
    have hz : 0 ≤ 23/5-u := by linarith [hu.2]
    have hp : 0 ≤ Y δ+X δ*(5/18)*(23/5-u)+amplitude δ*(25/468)*(23/5-u)^2 := by positivity
    have hh := mul_le_mul_of_nonneg_left hu.2 hp
    apply (le_div_iff₀ (by linarith [hs.1,hu.1])).2
    nlinarith only [hl,hh]
  simp only [pow_one] at hm
  rw [full_reverse_integral] at hm
  nlinarith only [hc,hn,hm]

/-- Original cross and one complete polynomial comparison. -/
theorem H_raw_quartic {δ s : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100)
    (hs : s ∈ Icc (5 : ℝ) (33/5)) :
    (5/28)*(5/23)*(Y δ*(33/5-s)^2/2+((5/18)/6)*X δ*(33/5-s)^3+((25/468)/12)*amplitude δ*(33/5-s)^4) ≤ wuImprovementLimit true δ s := by
  have hc := wuImprovementLimit_upper_cross (s := s) (t := (33/5 : ℝ))
    hδ (by linarith) (by linarith [hs.1]) hs.2 (by norm_num)
  norm_num only at hc
  have hn := wuImprovementLimit_nonneg true hδ (by linarith : δ < 1/2)
    (s := (33/5 : ℝ)) (by norm_num) (by norm_num)
  have hm : (∫ u in (s-1)..(28/5 : ℝ), (0)+((5/28)*(5/23)*Y δ)*(28/5-u)^1+((5/28)*(5/23)*((5/18)/2)*X δ)*(28/5-u)^2+((5/28)*(5/23)*((25/468)/3)*amplitude δ)*(28/5-u)^3) ≤
      ∫ u in (s-1)..(28/5 : ℝ), wuImprovementLimit false δ u/u := by
    apply intervalIntegral.integral_mono_on (by linarith [hs.2])
      (show IntervalIntegrable (fun u : ℝ => (0)+((5/28)*(5/23)*Y δ)*(28/5-u)^1+((5/28)*(5/23)*((5/18)/2)*X δ)*(28/5-u)^2+((5/28)*(5/23)*((25/468)/3)*amplitude δ)*(28/5-u)^3) volume (s-1) (28/5) from
        (by apply Continuous.intervalIntegrable; fun_prop))
      (wuImprovementLimit_div_intervalIntegrable false hδ (by linarith)
        (by linarith [hs.1]) (by linarith [hs.2]) (by norm_num))
    intro u hu
    have hl := h_raw_cubic hδ hδhi ⟨by linarith [hs.1,hu.1],hu.2⟩
    have hA := amplitude_nonneg hδ hδhi
    have hX := X_nonneg hδ hδhi
    have hY := Y_nonneg hδ hδhi
    have hz : 0 ≤ 28/5-u := by linarith [hu.2]
    have hp : 0 ≤ (5/23)*(Y δ*(28/5-u)+((5/18)/2)*X δ*(28/5-u)^2+((25/468)/3)*amplitude δ*(28/5-u)^3) := by positivity
    have hh := mul_le_mul_of_nonneg_left hu.2 hp
    apply (le_div_iff₀ (by linarith [hs.1,hu.1])).2
    nlinarith only [hl,hh]
  simp only [pow_one] at hm
  rw [full_reverse_integral] at hm
  nlinarith only [hc,hn,hm]

/-- The lower cross, not a global antitone assumption. -/
theorem X_ge_four {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100) :
    wuImprovementLimit false δ 4 ≤ X δ := by
  have hc := wuImprovementLimit_lower_cross (s := (18/5 : ℝ)) (t := 4)
    hδ (by linarith) (by norm_num) (by norm_num) (by norm_num)
  norm_num only at hc
  have hi : 0 ≤ ∫ v in (13/5 : ℝ)..3, wuImprovementLimit true δ v/v := by
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro v hv
    exact div_nonneg (wuImprovementLimit_nonneg true hδ (by linarith)
      (by linarith [hv.1]) (by linarith [hv.2])) (by linarith [hv.1])
  change _ ≤ X δ at hc
  linarith only [hc,hi]

theorem Y_ge_five {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100) :
    wuImprovementLimit true δ 5 ≤ Y δ :=
  wuImprovementLimit_upper_antitone hδ (by linarith)
    ⟨by norm_num,by norm_num⟩ ⟨by norm_num,by norm_num⟩ (by norm_num)

/-- Both inequalities concern the same actual endpoints and amplitude. -/
theorem actual_coupled_system {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100) :
    (128/8073)*amplitude δ+(16/207)*X δ+(8/23)*Y δ ≤ X δ ∧
    (64/56511)*amplitude δ+(32/4347)*X δ+(8/161)*Y δ ≤ Y δ := by
  have hx := (h_raw_cubic hδ hδhi (s := 4) ⟨by norm_num,by norm_num⟩).trans
    (X_ge_four hδ hδhi)
  have hy := (H_raw_quartic hδ hδhi (s := 5) ⟨by norm_num,by norm_num⟩).trans
    (Y_ge_five hδ hδhi)
  constructor <;> nlinarith only [hx,hy]

/-- Fixed positive elimination; no division by the possibly zero amplitude. -/
theorem coupled_elimination (A x y : ℝ)
    (hx : (128/8073)*A+(16/207)*x+(8/23)*y ≤ x)
    (hy : (64/56511)*A+(32/4347)*x+(8/161)*y ≤ y) :
    κX*A ≤ x ∧ κY*A ≤ y := by
  norm_num [κX,κY]
  constructor <;> linarith only [hx,hy]

theorem actual_endpoints_closed {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100) :
    κX*amplitude δ ≤ X δ ∧ κY*amplitude δ ≤ Y δ :=
  coupled_elimination _ _ _ (actual_coupled_system hδ hδhi).1
    (actual_coupled_system hδ hδhi).2

theorem hCoupled {δ u : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100)
    (hu : u ∈ Icc (2 : ℝ) (18/5)) :
    amplitude δ*(κX+(5/13)*(18/5-u)) ≤ wuImprovementLimit false δ u := by
  have hr := h_raw_affine hδ hδhi hu
  have he := (actual_endpoints_closed hδ hδhi).1
  nlinarith only [hr,he]

theorem HCoupled {δ s : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100)
    (hs : s ∈ Icc (3 : ℝ) (23/5)) :
    amplitude δ*(κY+(25/468)*(23/5-s)^2+κX*(5/18)*(23/5-s)) ≤
      wuImprovementLimit true δ s := by
  have hr := H_raw_quadratic hδ hδhi hs
  have he := actual_endpoints_closed hδ hδhi
  have hm := mul_le_mul_of_nonneg_right he.1
    (show 0 ≤ (5/18 : ℝ)*(23/5-s) by nlinarith only [hs.2])
  nlinarith only [hr,he.2,hm]

end
end Wu2008DoubleSieve.Phase17
