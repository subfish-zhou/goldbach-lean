import SigmaRationalOuterSplit

noncomputable section
namespace SigmaRationalOuterFTC
open Real TerminalE SigmaVariableOuterPayment SigmaVariableFull

/-- The three remaining original ratio numerators and denominators. -/
def negN (t : ℝ) : ℝ := (t+3)*(t+2)
def negD (t : ℝ) : ℝ := 6*(t+1)
def radN (t : ℝ) : ℝ := (t+9-2*radical)*(5+radical)
def radD (t : ℝ) : ℝ := (t+9+2*radical)*(5-radical)
def outerQ (t : ℝ) : ℝ := -t^2+6*t+6

/-- Both original rational endpoints, after cancellation and division by the outer t. -/
def jointNum (t : ℝ) : ℝ :=
  32/35-(184/105)*t-(1144/945)*t^2-(5261/540)*t^3+(176/63)*t^4+
  (1759/270)*t^5+(2122/945)*t^6+(299/1260)*t^7

def jointDen (t : ℝ) : ℝ := t^4*(t+1)*(t+3)^3

theorem joint_weight_identity {t : ℝ} (ht : 1≤t) :
    (jointRational (-(t+1)) ((t+1)/2)-jointRational (-(t+1)) 1)/t=
      jointNum t/jointDen t := by
  have ht0 : t≠0 := by linarith
  have ht1 : t+1≠0 := by linarith
  have ht3 : t+3≠0 := by linarith
  unfold jointRational zeroTwo negTwo negThree negFour jointNum jointDen
    a b d TerminalE.e f
  rw [show -(t+1)+1 = -t by ring]
  field_simp [ht0,ht1,ht3]
  ring

theorem radD_pos {t : ℝ} (ht : 1≤t) : 0<radD t := by
  unfold radD
  apply mul_pos
  · linarith only [radical_pos,ht]
  · linarith only [radical_lt_four]

theorem outerQ_pos {t : ℝ} (ht : t ∈ Set.Icc 1 3) : 0<outerQ t := by
  have h := SigmaVariableFull.pole_quadratic ht
  unfold q at h
  unfold outerQ
  nlinarith only [h]

/-- Only exact polynomial substitutions of the four already paid terms. -/
def homogeneousWeight (t : ℝ) : ℝ :=
  (-(2145*t^2+4418*t+2280)/(210*(t+1)^2))*
    (splitUpperNum (t+2) 3/splitUpperDen (t+2) 3)/t+
  (64*(10*t^4+18*t^3-t^2-6*t+3)/(945*t^4))*
    (splitLowerNum (negN t) (negD t)/splitLowerDen (negN t) (negD t))/t+
  (250*(-5*t^2+21*t+26)/(189*outerQ t))*
    (splitLowerNum (quadN t) (quadD t)/splitLowerDen (quadN t) (quadD t))/t+
  (250*(-11*t^2+97*t+108)/(189*radical*outerQ t))*
    (splitLowerNum (radN t) (radD t)/splitLowerDen (radN t) (radD t))/t+
  jointNum t/jointDen t

/-- This connects the algebraic certificate to the actual paidWeight, not a substitute kernel. -/
theorem paidWeight_homogeneous {t : ℝ} (ht : t ∈ Set.Icc 1 3) :
    paidWeight t=homogeneousWeight t := by
  have hnD : 0<negD t := by unfold negD; linarith [ht.1]
  have hqD : 0<quadD t := by
    have ht1 : 0<t+1 := by linarith [ht.1]
    unfold quadD
    positivity
  have hn : negD t≤negN t := (one_le_div hnD).mp (negRatio_ge ht.1)
  have hq : quadD t≤quadN t := (one_le_div hqD).mp (quadRatio_ge ht.1)
  have hr : radD t≤radN t := (one_le_div (radD_pos ht.1)).mp (radRatio_ge ht.1)
  have h0 := splitUpper_homogeneous (by norm_num : (0:ℝ)<3)
    (by linarith [ht.1] : (3:ℝ)≤t+2)
  have h1 := splitLower_homogeneous hnD hn
  have h2 := splitLower_homogeneous hqD hq
  have h3 := splitLower_homogeneous (radD_pos ht.1) hr
  change RemainingHf.splitUpper (zeroRatio t)=_ at h0
  change RemainingHf.splitLower (negRatio t)=_ at h1
  change RemainingHf.splitLower (quadRatio t)=_ at h2
  change RemainingHf.splitLower (radRatio t)=_ at h3
  unfold paidWeight paidMass
  rw [h0,h1,h2,h3,zero_coefficient_formula ht.1,neg_coefficient_formula ht.1,
    quad_coefficient_formula ht,rad_coefficient_formula ht]
  have hj := joint_weight_identity ht.1
  unfold homogeneousWeight outerQ
  linear_combination hj

end SigmaRationalOuterFTC
