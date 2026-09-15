import WE10FourMajorWeighted

noncomputable section
open Real Set MeasureTheory Wu2008DoubleSieve
open FourRoughClosedMass

namespace WuSource.SrcFour

def TenDomain (x y z t : ℝ) : Prop :=
  alpha ≤ x ∧ x ≤ y ∧ y ≤ z ∧ z ≤ t ∧ t ≤ beta

def ElevenDomain (x y z t : ℝ) : Prop :=
  alpha ≤ x ∧ x ≤ y ∧ y ≤ z ∧ z ≤ beta ∧ beta ≤ t ∧ t ≤ lam-z

def threshold (x y z : ℝ) : ℝ := 1-x-(22/5)*y-z
def outerCut : ℝ := 1-lam-(22/5)*beta

theorem geometry :
    alpha < (1/10 : ℝ) ∧ (1/10 : ℝ) < outerCut ∧ outerCut < beta ∧
    0 < alpha ∧ beta < 1 ∧ 2*beta ≤ lam := by
  norm_num [outerCut, alpha, beta, lam, truncatedSixthLowerAlpha,
    truncatedSixthLowerBeta, truncatedSixthLowerLambda]

theorem fine_iff {x y z t : ℝ} (hy : 0 < y) :
    (17/5 : ℝ) ≤ parameter x y z t ↔ t ≤ threshold x y z := by
  rw [parameter, le_div_iff₀ hy]
  unfold threshold
  constructor <;> intro h <;> linarith only [h]

theorem complement_iff {x y z t : ℝ} (hy : 0 < y) :
    parameter x y z t < (17/5 : ℝ) ↔ threshold x y z < t := by
  rw [← not_le, fine_iff hy, not_le]

theorem ten_fine {x y z t : ℝ} (h : TenDomain x y z t) :
    (17/5 : ℝ) ≤ parameter x y z t := by
  obtain ⟨hx,hxy,hyz,hzt,ht⟩ := h
  apply (fine_iff (geometry.2.2.2.1.trans_le (hx.trans hxy))).mpr
  have hb : (37/5 : ℝ)*beta ≤ 1 := by
    norm_num [beta,truncatedSixthLowerBeta]
  unfold threshold
  linarith only [hxy,hyz,hzt,ht,hb]

theorem ten_complement_empty :
    ¬ ∃ x y z t : ℝ, TenDomain x y z t ∧ parameter x y z t < (17/5 : ℝ) := by
  rintro ⟨x,y,z,t,hd,hlt⟩
  exact (not_lt_of_ge (ten_fine hd)) hlt

theorem eleven_complement_location {x y z t : ℝ}
    (h : ElevenDomain x y z t) (hc : parameter x y z t < (17/5 : ℝ)) :
    outerCut < x ∧ (5/22)*(1-lam-x) < y ∧ threshold x y z < t := by
  obtain ⟨hx,hxy,hyz,hz,_,ht⟩ := h
  have hs := (complement_iff (geometry.2.2.2.1.trans_le (hx.trans hxy))).mp hc
  unfold threshold at hs
  refine ⟨?_,?_,hs⟩
  · unfold outerCut
    linarith only [hs,ht,hyz,hz]
  · linarith only [hs,ht]

theorem eleven_fine_of_outer {x y z t : ℝ}
    (h : ElevenDomain x y z t) (hx : x ≤ outerCut) :
    (17/5 : ℝ) ≤ parameter x y z t := by
  by_contra hc
  exact (not_lt_of_ge hx) (eleven_complement_location h (lt_of_not_ge hc)).1

theorem eleven_complement_nonempty :
    ElevenDomain beta beta beta (lam-beta) ∧
      parameter beta beta beta (lam-beta) < (17/5 : ℝ) := by
  constructor
  · unfold ElevenDomain
    norm_num [alpha,beta,lam,truncatedSixthLowerAlpha,
      truncatedSixthLowerBeta,truncatedSixthLowerLambda]
  · norm_num [parameter,alpha,beta,lam,truncatedSixthLowerAlpha,
      truncatedSixthLowerBeta,truncatedSixthLowerLambda]

theorem kernel_source_ten {x y z t : ℝ} (h : TenDomain x y z t) :
    regularKernel x y z t = kernel x y z t := by
  obtain ⟨hx,hxy,hyz,hzt,ht⟩ := h
  simp only [regularKernel,clip,max_eq_right hx,max_eq_right (hx.trans hxy),
    max_eq_right (hx.trans (hxy.trans hyz)),
    max_eq_right (hx.trans (hxy.trans (hyz.trans hzt))),
    max_eq_right (ten_parameter hx hxy hyz hzt ht),kernel]

theorem kernel_source_eleven {x y z t : ℝ} (h : ElevenDomain x y z t) :
    regularKernel x y z t = kernel x y z t := by
  obtain ⟨hx,hxy,hyz,hz,hbt,ht⟩ := h
  have hat := hx.trans (hxy.trans (hyz.trans (hz.trans hbt)))
  simp only [regularKernel,clip,max_eq_right hx,max_eq_right (hx.trans hxy),
    max_eq_right (hx.trans (hxy.trans hyz)),max_eq_right hat,
    max_eq_right (eleven_parameter hx hxy hyz hz ht),kernel]

theorem fine_kernel {c x y z t : ℝ}
    (hc : ∀ u : ℝ, (17/5 : ℝ) ≤ u → LiLiuPrereqBuchstab.buchstab u ≤ c)
    (hx : alpha ≤ x) (hy : alpha ≤ y) (hz : alpha ≤ z) (ht : alpha ≤ t)
    (hf : (17/5 : ℝ) ≤ parameter x y z t) :
    regularKernel x y z t ≤ c/(x*y^2*z*t) := by
  have ha := geometry.2.2.2.1
  have hx0 := ha.trans_le hx
  have hy0 := ha.trans_le hy
  have hz0 := ha.trans_le hz
  have ht0 := ha.trans_le ht
  simp only [regularKernel,clip,max_eq_right hx,max_eq_right hy,max_eq_right hz,
    max_eq_right ht,max_eq_right (show (2 : ℝ) ≤ parameter x y z t by linarith)]
  exact div_le_div_of_nonneg_right (hc _ hf) (by positivity)

#check @ten_complement_empty
#check @eleven_complement_location
#check @eleven_complement_nonempty
#check @kernel_source_ten
#check @kernel_source_eleven
#check @fine_kernel
#print axioms ten_complement_empty
#print axioms eleven_complement_location
#print axioms kernel_source_ten
#print axioms kernel_source_eleven
#print axioms fine_kernel
end WuSource.SrcFour
