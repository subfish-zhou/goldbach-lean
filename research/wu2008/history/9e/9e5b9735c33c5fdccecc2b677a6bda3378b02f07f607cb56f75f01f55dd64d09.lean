import SrcFourLowerGeometry

noncomputable section
open Real Set MeasureTheory Wu2008DoubleSieve FourRoughClosedMass
open Wu08OriginalFourWeights

namespace WuSource.SrcFour

def lowerMiddleTerm (c : ℝ) (i : Fin 4) (x y : ℝ) : ℝ :=
  c*lowerCoeff i/(beta*x)*
    (crossFloor*(FourLogAffine.ell y)^(i.val+1)/y+
      (1+slopeFloor)*(FourLogAffine.ell y)^(i.val+2)/(2*y))
def lowerA (c : ℝ) (i : Fin 4) : ℝ :=
  c*lowerCoeff i*crossFloor/(beta*(i.val+2 : ℝ))
def lowerB (c : ℝ) (i : Fin 4) : ℝ :=
  c*lowerCoeff i*(1+slopeFloor)/(2*beta*(i.val+3 : ℝ))
def lowerProfileTerm (c : ℝ) (i : Fin 4) (x : ℝ) : ℝ :=
  lowerA c i*WuTarget.W13.tail (i.val+2) x+
    lowerB c i*WuTarget.W13.tail (i.val+3) x
def lowerProfile (c x : ℝ) : ℝ := ∑ i : Fin 4, lowerProfileTerm c i x
def weightFloor : ℝ := (36/5)/(1-alpha)
def lowerAmount (c : ℝ) : ℝ :=
  weightFloor*∑ i : Fin 4,
    (lowerA c i*FourLogAffine.l^(i.val+3)/(i.val+3 : ℝ)+
      lowerB c i*FourLogAffine.l^(i.val+4)/(i.val+4 : ℝ))

theorem lower_coefficients_nonneg {c : ℝ} (hc0 : 0 ≤ c) (i : Fin 4) :
    0 ≤ lowerA c i ∧ 0 ≤ lowerB c i := by
  have hb := geometry.2.2.2.1.trans (geometry.1.trans (geometry.2.1.trans geometry.2.2.1))
  have hi := lowerCoeff_pos i
  have hcross := lower_constants.1
  have hs := lower_constants.2.1
  unfold lowerA lowerB
  constructor <;> positivity

theorem middle_lower {c x y : ℝ} (hc0 : 0 ≤ c)
    (hc : ∀ u : ℝ, (3 : ℝ) ≤ u → c ≤ LiLiuPrereqBuchstab.buchstab u)
    (hx : alpha ≤ x) (hxy : x ≤ y) (hy : y ≤ beta) :
    c/(x*y^2)*
      (crossFloor*FourLogAffine.ell y+(1+slopeFloor)*FourLogAffine.ell y^2/2) ≤
      regularMiddle10 x y+regularMiddle11 x y := by
  have hi10 := (regularInner10_continuous.comp
    (f := fun z : ℝ => (x,y,z)) (by fun_prop)).intervalIntegrable (μ := volume) y beta
  have hi11 := (regularInner11_continuous.comp
    (f := fun z : ℝ => (x,y,z)) (by fun_prop)).intervalIntegrable (μ := volume) y beta
  change IntervalIntegrable (fun z => regularInner10 x y z) volume y beta at hi10
  change IntervalIntegrable (fun z => regularInner11 x y z) volume y beta at hi11
  have hi := integral_ge_two_tails
    (f := fun z => regularInner10 x y z+regularInner11 x y z)
    (C := c*crossFloor/(x*y^2)) (D := c*(1+slopeFloor)/(x*y^2))
    ((regularInner10_continuous.comp (f := fun z : ℝ => (x,y,z)) (by fun_prop)).add
      (regularInner11_continuous.comp (f := fun z : ℝ => (x,y,z)) (by fun_prop)))
    (geometry.2.2.2.1.trans_le (hx.trans hxy)) hy 0 1 (fun z hz => by
      have hs := add_le_add (inner10_lower hc hx hxy hz.1 hz.2)
        (inner11_lower hc0 hc hx hxy hz.1 hz.2)
      convert hs using 1 <;> first | rfl |
        (simp only [pow_zero,pow_one,FourLogAffine.ell]; ring))
  rw [intervalIntegral.integral_add hi10 hi11] at hi
  change _ ≤ regularMiddle10 x y+regularMiddle11 x y at hi
  convert hi using 1
  norm_num only [Nat.cast_zero,Nat.cast_one,zero_add,one_add_one_eq_two,pow_one,div_one]
  unfold FourLogAffine.ell
  ring

theorem lower_middle_sum (c x y : ℝ) :
    (∑ i : Fin 4, lowerMiddleTerm c i x y) =
      c/(x*y)*((∑ i : Fin 4, lowerCoeff i*(FourLogAffine.ell y)^i.val)/beta)*
        (crossFloor*FourLogAffine.ell y+(1+slopeFloor)*FourLogAffine.ell y^2/2) := by
  rw [Finset.sum_div,Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  unfold lowerMiddleTerm
  simp only [pow_add,pow_one]
  ring

theorem lower_sum_le_middle {c x y : ℝ} (hc0 : 0 ≤ c)
    (hc : ∀ u : ℝ, (3 : ℝ) ≤ u → c ≤ LiLiuPrereqBuchstab.buchstab u)
    (hx : alpha ≤ x) (hxy : x ≤ y) (hy : y ≤ beta) :
    (∑ i : Fin 4, lowerMiddleTerm c i x y) ≤
      regularMiddle10 x y+regularMiddle11 x y := by
  rw [lower_middle_sum]
  have hx0 := geometry.2.2.2.1.trans_le hx
  have hy0 := hx0.trans_le hxy
  have hell := FourLogAffine.ell_nonneg (hx.trans hxy) hy
  have hs := lower_constants.2.1
  have hcross := lower_constants.1
  have hp := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (reciprocal_lower ⟨hx.trans hxy,hy⟩)
      (show 0 ≤ c/(x*y) by positivity))
    (show 0 ≤ crossFloor*FourLogAffine.ell y+
      (1+slopeFloor)*FourLogAffine.ell y^2/2 by positivity)
  apply le_trans hp
  convert middle_lower hc0 hc hx hxy hy using 1
  ring

theorem lowerMiddleTerm_eq (c : ℝ) (i : Fin 4) (x y : ℝ) :
    lowerMiddleTerm c i x y =
      (c*lowerCoeff i*crossFloor/(beta*x))*(log beta-log y)^(i.val+1)/y+
      (c*lowerCoeff i*(1+slopeFloor)/(2*beta*x))*(log beta-log y)^(i.val+2)/y := by
  unfold lowerMiddleTerm FourLogAffine.ell
  ring

theorem lowerMiddleTerm_integrable (c : ℝ) (i : Fin 4) {x : ℝ}
    (hx : 0 < x) (hxb : x ≤ beta) :
    IntervalIntegrable (lowerMiddleTerm c i x) volume x beta := by
  rw [funext (lowerMiddleTerm_eq c i x)]
  exact (FourLogAffine.tail_integrable hx hxb (i.val+1)).add
    (FourLogAffine.tail_integrable hx hxb (i.val+2))

theorem lowerMiddleTerm_integral (c : ℝ) (i : Fin 4) {x : ℝ}
    (hx : 0 < x) (hxb : x ≤ beta) :
    (∫ y in x..beta, lowerMiddleTerm c i x y) = lowerProfileTerm c i x := by
  rw [funext (lowerMiddleTerm_eq c i x),
    FourLogAffine.integral_two_tails hx hxb (i.val+1) (i.val+2)]
  unfold lowerProfileTerm lowerA lowerB WuTarget.W13.tail
  simp only [Nat.cast_add,Nat.cast_one,Nat.cast_ofNat]
  rw [show i.val+1+1 = i.val+2 by omega,show i.val+2+1 = i.val+3 by omega]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

theorem lowerProfile_le_outer {c x : ℝ} (hc0 : 0 ≤ c)
    (hc : ∀ u : ℝ, (3 : ℝ) ≤ u → c ≤ LiLiuPrereqBuchstab.buchstab u)
    (hx : x ∈ Icc alpha beta) :
    lowerProfile c x ≤ regularOuter10 x+regularOuter11 x := by
  have hx0 := geometry.2.2.2.1.trans_le hx.1
  have hi10 := (regularMiddle10_continuous.comp
    (f := fun y : ℝ => (x,y)) (by fun_prop)).intervalIntegrable (μ := volume) x beta
  have hi11 := (regularMiddle11_continuous.comp
    (f := fun y : ℝ => (x,y)) (by fun_prop)).intervalIntegrable (μ := volume) x beta
  change IntervalIntegrable (fun y => regularMiddle10 x y) volume x beta at hi10
  change IntervalIntegrable (fun y => regularMiddle11 x y) volume x beta at hi11
  have his : IntervalIntegrable (fun y => ∑ i : Fin 4, lowerMiddleTerm c i x y)
      volume x beta :=
    IntervalIntegrable.sum Finset.univ (fun i _ => lowerMiddleTerm_integrable c i hx0 hx.2)
  have hi := intervalIntegral.integral_mono_on hx.2 his (hi10.add hi11)
    (fun y hy => lower_sum_le_middle hc0 hc hx.1 hy.1 hy.2)
  rw [intervalIntegral.integral_add hi10 hi11,
    intervalIntegral.integral_finsetSum (fun i _ => lowerMiddleTerm_integrable c i hx0 hx.2)] at hi
  simp_rw [lowerMiddleTerm_integral _ _ hx0 hx.2] at hi
  exact hi

theorem lowerProfileTerm_integrable (c : ℝ) (i : Fin 4) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (lowerProfileTerm c i) volume a b :=
  ((WuTarget.W13.tail_continuousOn (i.val+2) ha hab).intervalIntegrable.const_mul
    (lowerA c i)).add
  ((WuTarget.W13.tail_continuousOn (i.val+3) ha hab).intervalIntegrable.const_mul
    (lowerB c i))

theorem lowerProfile_integrable (c : ℝ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (lowerProfile c) volume a b :=
  IntervalIntegrable.sum Finset.univ (fun i _ => lowerProfileTerm_integrable c i ha hab)

theorem lowerProfile_integral (c : ℝ) :
    (∫ x in alpha..beta, lowerProfile c x) =
      ∑ i : Fin 4,
        (lowerA c i*(log beta-log alpha)^(i.val+3)/(i.val+3 : ℝ)+
          lowerB c i*(log beta-log alpha)^(i.val+4)/(i.val+4 : ℝ)) := by
  have ha := geometry.2.2.2.1
  have hab := geometry.1.le.trans (geometry.2.1.le.trans geometry.2.2.1.le)
  unfold lowerProfile
  rw [intervalIntegral.integral_finsetSum
    (fun i _ => lowerProfileTerm_integrable c i ha hab)]
  apply Finset.sum_congr rfl
  intro i _
  have he (x : ℝ) :
      lowerProfileTerm c i x =
        lowerA c i*(log beta-log x)^(i.val+2)/x+
          lowerB c i*(log beta-log x)^(i.val+3)/x := by
    unfold lowerProfileTerm WuTarget.W13.tail
    ring
  rw [funext he,FourLogAffine.integral_two_tails ha hab (i.val+2) (i.val+3)]
  norm_num only [Nat.cast_add,Nat.cast_ofNat]
  rw [show i.val+2+1 = i.val+3 by omega,show i.val+3+1 = i.val+4 by omega]
  ring

#check @lowerProfile_le_outer
#check @lowerProfile_integral
#print axioms lowerProfile_le_outer
#print axioms lowerProfile_integral
end WuSource.SrcFour
