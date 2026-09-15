import FreshFTCJoint

noncomputable section
open Real FirstCRationalPayment F1JointFTC F1ActualSecondFTC F1BFullFTC
namespace FreshLogBasis

/-- All nonlogarithmic parts, including the forced fourth pole. -/
def poleR (a c₂ c₃ c₄ : ℝ) : ℝ :=
  c₂*(1/(2-a)-1/(927/200-a))+
  (c₃/2)*(1/(2-a)^2-1/(927/200-a)^2)+
  (c₄/3)*(1/(2-a)^3-1/(927/200-a)^3)

theorem pole_difference (a c₁ c₂ c₃ c₄ t : ℝ)
    (ha : a < 2) (ht : t=(927/200-a)/(2-a)) :
    F1FreshFTC.pole4 a c₁ c₂ c₃ c₄ (927/200)-
      F1FreshFTC.pole4 a c₁ c₂ c₃ c₄ 2 = c₁*log t+poleR a c₂ c₃ c₄ := by
  have h0 : 2-a ≠ 0 := by linarith
  have h1 : 927/200-a ≠ 0 := by linarith
  rw [ht,log_div h1 h0]
  unfold F1FreshFTC.pole4 polePrimitive poleR
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

def aMinus (f g : ℝ) : ℝ := f/2+(g-8*f)/(2*root)
def aPlus (f g : ℝ) : ℝ := f/2-(g-8*f)/(2*root)
def tMinus (f g : ℝ) : ℝ := f/42+(g+12*f/21)/(2*root)
def tPlus (f g : ℝ) : ℝ := f/42-(g+12*f/21)/(2*root)
def bMinus (f g : ℝ) : ℝ := f/42+(g/(1127/200)-f/(1127/200)-9*f/21)/(2*root)
def bPlus (f g : ℝ) : ℝ := f/42-(g/(1127/200)-f/(1127/200)-9*f/21)/(2*root)
def dMinus (f g : ℝ) : ℝ := f/2+(g/(1127/200)-f/(1127/200)-9*f)/(2*root)
def dPlus (f g : ℝ) : ℝ := f/2-(g/(1127/200)-f/(1127/200)-9*f)/(2*root)

theorem quadratic_A (f g : ℝ) :
    quadraticPrimitive f g (927/200)-quadraticPrimitive f g 2 =
    f*log refOne+aMinus f g*log crossOneMinus-aPlus f g*log crossOnePlus := by
  simpa only [aMinus,aPlus,crossOneMinus,crossOnePlus,show (2:ℝ)+8=10 by norm_num] using
    quadratic_difference_normalized f g (927/200) 2 refOne
      (by norm_num) (by norm_num) (by norm_num [refOne])

theorem quadratic_T (f g : ℝ) :
    affinePrimitive f g (927/200)-affinePrimitive f g 2 =
    (f/21)*log refTwo+tMinus f g*log crossTwoMinus-tPlus f g*log crossTwoPlus := by
  have h := quadratic_difference_normalized (f/21) (g+20*f/21)
    (21*(927/200)-20) (21*2-20) refTwo
    (by norm_num) (by norm_num) (by norm_num [refTwo])
  unfold affinePrimitive tMinus tPlus crossTwoMinus crossTwoPlus
  convert h using 1
  norm_num
  ring

theorem quadratic_B (f g : ℝ) :
    quadPrimitiveOne f g (927/200)-quadPrimitiveOne f g 2 =
    (f/21)*log bRefOne+bMinus f g*log bCrossOneMinus-bPlus f g*log bCrossOnePlus := by
  have h := quadratic_difference_normalized (f/21)
    (g/(1127/200)-f/21-f/(1127/200)) 22 (21*3/(1127/200)+1) bRefOne
    (by norm_num) (by norm_num) (by norm_num [bRefOne])
  unfold quadPrimitiveOne bMinus bPlus bCrossOneMinus bCrossOnePlus
  convert h using 1 <;> norm_num
  ring

theorem quadratic_D (f g : ℝ) :
    quadPrimitiveTwo f g (927/200)-quadPrimitiveTwo f g 2 =
    f*log bRefTwo+dMinus f g*log bCrossTwoMinus-dPlus f g*log bCrossTwoPlus := by
  have h := quadratic_difference_normalized f
    (g/(1127/200)-f-f/(1127/200)) 2 (3/(1127/200)+1) bRefTwo
    (by norm_num) (by norm_num) (by norm_num [bRefTwo])
  unfold quadPrimitiveTwo dMinus dPlus bCrossTwoMinus bCrossTwoPlus
  convert h using 1 <;> norm_num
  ring
end FreshLogBasis
