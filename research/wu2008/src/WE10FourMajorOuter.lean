import WE10FourMajorInner

noncomputable section
open Real Set MeasureTheory Wu2008DoubleSieve
open FourRoughClosedMass ClassicalLogFourBounds

namespace WuTarget.E10FourMajor

def middleTerm (i : Fin 5) (x y : ℝ) : ℝ :=
  (4/7)*recipCoeff i/x*
    (crossCap*(FourLogAffine.ell y)^(i.val+1)/y+
      (1+slope)*(FourLogAffine.ell y)^(i.val+2)/(2*y))

def coefA (i : Fin 5) : ℝ := (4/7)*recipCoeff i*crossCap/(i.val+2 : ℝ)
def coefB (i : Fin 5) : ℝ := (4/7)*recipCoeff i*(1+slope)/(2*(i.val+3 : ℝ))
def profileTerm (i : Fin 5) (x : ℝ) : ℝ :=
  coefA i*W13.tail (i.val+2) x+coefB i*W13.tail (i.val+3) x
def profile (x : ℝ) : ℝ := ∑ i : Fin 5, profileTerm i x

theorem coefficients_pos (i : Fin 5) : 0 < coefA i ∧ 0 < coefB i := by
  have hc := recipCoeff_pos i
  have hcross := crossCap_pos
  have hs := slope_pos
  unfold coefA coefB
  constructor <;> positivity

theorem middle_sum_identity (x y : ℝ) :
    (∑ i : Fin 5, middleTerm i x y) =
      (4/7)/(x*y)*reciprocalCap y*
        (crossCap*FourLogAffine.ell y+(1+slope)*FourLogAffine.ell y^2/2) := by
  unfold reciprocalCap
  rw [Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  unfold middleTerm
  simp only [pow_add,pow_one]
  ring

theorem middle_le_sum {x y : ℝ} (hx : alpha ≤ x) (hy : y ∈ Icc alpha beta) :
    regularMiddle10 x y+regularMiddle11 x y ≤ ∑ i : Fin 5, middleTerm i x y := by
  rw [middle_sum_identity]
  have ha := fixed_geometry_major.1
  have hx0 := ha.trans_le hx
  have hy0 := ha.trans_le hy.1
  have hell := FourLogAffine.ell_nonneg hy.1 hy.2
  have hs := slope_pos
  have hc := crossCap_pos
  have hp := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (reciprocal_upper hy)
      (show 0 ≤ (4/7)/(x*y) by positivity))
    (show 0 ≤ crossCap*FourLogAffine.ell y+
      (1+slope)*FourLogAffine.ell y^2/2 by positivity)
  have hi := middle_pair_upper hx hy
  apply hi.trans
  convert hp using 1
  ring

theorem middleTerm_eq (i : Fin 5) (x y : ℝ) :
    middleTerm i x y =
      ((4/7)*recipCoeff i*crossCap/x)*(log beta-log y)^(i.val+1)/y+
      ((4/7)*recipCoeff i*(1+slope)/(2*x))*(log beta-log y)^(i.val+2)/y := by
  unfold middleTerm FourLogAffine.ell
  ring

theorem middleTerm_integrable (i : Fin 5) {x : ℝ} (hx : 0 < x) (hxb : x ≤ beta) :
    IntervalIntegrable (middleTerm i x) volume x beta := by
  have he := funext (middleTerm_eq i x)
  rw [he]
  exact (FourLogAffine.tail_integrable hx hxb (i.val+1)).add
    (FourLogAffine.tail_integrable hx hxb (i.val+2))

theorem middleTerm_integral (i : Fin 5) {x : ℝ} (hx : 0 < x) (hxb : x ≤ beta) :
    (∫ y in x..beta, middleTerm i x y) = profileTerm i x := by
  rw [funext (middleTerm_eq i x)]
  rw [FourLogAffine.integral_two_tails hx hxb (i.val+1) (i.val+2)]
  unfold profileTerm coefA coefB W13.tail
  simp only [Nat.cast_add,Nat.cast_one,Nat.cast_ofNat]
  rw [show i.val+1+1 = i.val+2 by omega,show i.val+2+1 = i.val+3 by omega]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

theorem outer_pair_upper {x : ℝ} (hx : x ∈ Icc alpha beta) :
    regularOuter10 x+regularOuter11 x ≤ profile x := by
  have hx0 := fixed_geometry_major.1.trans_le hx.1
  have hi10 := (regularMiddle10_continuous.comp
    (f := fun y : ℝ => (x,y)) (by fun_prop)).intervalIntegrable (μ := volume) x beta
  have hi11 := (regularMiddle11_continuous.comp
    (f := fun y : ℝ => (x,y)) (by fun_prop)).intervalIntegrable (μ := volume) x beta
  change IntervalIntegrable (fun y => regularMiddle10 x y) volume x beta at hi10
  change IntervalIntegrable (fun y => regularMiddle11 x y) volume x beta at hi11
  have his : IntervalIntegrable (fun y => ∑ i : Fin 5, middleTerm i x y) volume x beta :=
    IntervalIntegrable.sum Finset.univ (fun i _ => middleTerm_integrable i hx0 hx.2)
  have hi := intervalIntegral.integral_mono_on hx.2 (hi10.add hi11) his
    (fun y hy => middle_le_sum hx.1 ⟨hx.1.trans hy.1,hy.2⟩)
  rw [intervalIntegral.integral_add hi10 hi11,
    intervalIntegral.integral_finsetSum (fun i _ => middleTerm_integrable i hx0 hx.2)] at hi
  change regularOuter10 x+regularOuter11 x ≤ _ at hi
  simp_rw [middleTerm_integral _ hx0 hx.2] at hi
  exact hi

end WuTarget.E10FourMajor
