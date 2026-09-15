import TerminalEPrimitive

noncomputable section
namespace TerminalE
open Real Set MeasureTheory Wu04FactorEnvelopes
open scoped Interval

def leftArg (u : ℝ) : ℝ := (u+3)/4
def rightArg (u : ℝ) : ℝ := 2*(u+1)/(u+3)
def density (u : ℝ) : ℝ := RemainingHf.splitLower ((u+1)/2)/u

theorem split_identity (u : ℝ) :
    RemainingHf.splitLower ((u+1)/2)=RemainingHf.basicLower (leftArg u)+RemainingHf.basicLower (rightArg u) := by
  unfold RemainingHf.splitLower leftArg rightArg leftFactor rightFactor
  congr 1
  · congr 1
    ring
  · congr 1
    rw [show 1+(u+1)/2=(u+3)/2 by ring,div_div_eq_mul_div]
    ring

theorem argument_bounds {u : ℝ} (hu : 1 ≤ u) :
    1 ≤ leftArg u ∧ 0 < leftArg u-3/4 ∧
    1 ≤ rightArg u ∧ 0 < rightArg u-2/3 ∧ rightArg u-2<0 := by
  have hu3 : 0<u+3 := by linarith
  dsimp [leftArg,rightArg]
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · apply (le_div_iff₀ hu3).mpr
    linarith
  constructor
  · have hr : (2:ℝ)/3 < 2*(u+1)/(u+3) := by
      apply (lt_div_iff₀ hu3).mpr
      linarith
    linarith
  · have hr : 2*(u+1)/(u+3)<2 := by
      apply (div_lt_iff₀ hu3).mpr
      linarith
    linarith

def fullPrimitive (u : ℝ) : ℝ :=
  primitive (3/4) (leftArg u)+primitive (2/3) (rightArg u)-primitive 2 (rightArg u)

/-- The single authorized factorization is used without any integration cut. -/
theorem fullPrimitive_deriv {u : ℝ} (hu : 1 ≤ u) :
    HasDerivAt fullPrimitive (density u) u := by
  rcases argument_bounds hu with ⟨hl,hlp,hr,hrp,hr2⟩
  have hu0 : u ≠ 0 := by linarith
  have hu3 : u+3 ≠ 0 := by linarith
  have hleft : HasDerivAt leftArg (1/4) u := ((hasDerivAt_id u).add_const 3).div_const 4
  have hright : HasDerivAt rightArg (4/(u+3)^2) u := by
    convert ((((hasDerivAt_id u).add_const 1).const_mul 2).div
      ((hasDerivAt_id u).add_const 3) hu3) using 1 <;> first | rfl | (dsimp; ring)
  have h0 := (primitive_deriv (by norm_num : (0:ℝ)<3/4) hl hlp.ne').comp u hleft
  have h1 := (primitive_deriv (by norm_num : (0:ℝ)<2/3) hr hrp.ne').comp u hright
  have h2 := (primitive_deriv (by norm_num : (0:ℝ)<2) hr hr2.ne).comp u hright
  convert (h0.add h1).sub h2 using 1 <;> first | rfl | skip
  dsimp [density]
  rw [split_identity]
  dsimp [leftArg,rightArg] at *
  rw [show (u+3)/4-3/4=u/4 by ring,
    show 2*(u+1)/(u+3)-2/3=4*u/(3*(u+3)) by field_simp; ring,
    show 2*(u+1)/(u+3)-2= -4/(u+3) by field_simp; ring]
  field_simp [hu0,hu3]
  ring

theorem density_continuous {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    ContinuousOn density (uIcc a b) := by
  intro u hu
  rw [uIcc_of_le hab] at hu
  have h := fullPrimitive_deriv (ha.trans hu.1)
  rcases argument_bounds (ha.trans hu.1) with ⟨hl,hlp,hr,hrp,hr2⟩
  have hu0 : u ≠ 0 := by linarith [hu.1]
  have hcL := (primitive_deriv (by norm_num : (0:ℝ)<3/4) hl hlp.ne').continuousAt
  have hcR := (primitive_deriv (by norm_num : (0:ℝ)<2/3) hr hrp.ne').continuousAt
  have hbl : ContinuousAt RemainingHf.basicLower (leftArg u) := by
    have hx : 0 < leftArg u := by linarith
    unfold RemainingHf.basicLower F1FullRecoveryPayment.lowerGapPayment
      Wu2008DoubleSieve.SharpLogRecurrence.lowerLog Wu2008DoubleSieve.SharpLogRecurrence.upperLog
      F1LowerResidual.payment F1LowerResidual.denom
    fun_prop (disch := positivity)
  have hbr : ContinuousAt RemainingHf.basicLower (rightArg u) := by
    have hx : 0 < rightArg u := by linarith
    unfold RemainingHf.basicLower F1FullRecoveryPayment.lowerGapPayment
      Wu2008DoubleSieve.SharpLogRecurrence.lowerLog Wu2008DoubleSieve.SharpLogRecurrence.upperLog
      F1LowerResidual.payment F1LowerResidual.denom
    fun_prop (disch := positivity)
  have hleft : ContinuousAt leftArg u := by unfold leftArg; fun_prop
  have hright : ContinuousAt rightArg u := by
    have hu3 : u+3 ≠ 0 := by linarith [hu.1]
    unfold rightArg
    fun_prop (disch := assumption)
  have he : density = fun u => (RemainingHf.basicLower (leftArg u)+RemainingHf.basicLower (rightArg u))/u :=
    funext (fun u => by dsimp [density]; rw [split_identity])
  rw [he]
  exact (((hbl.comp hleft).add (hbr.comp hright)).div continuousAt_id hu0).continuousWithinAt

def cellMass (a b : ℝ) : ℝ := fullPrimitive b-fullPrimitive a

theorem density_integral {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    (∫ u in a..b,density u)=cellMass a b := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro u hu
    rw [uIcc_of_le hab] at hu
    exact fullPrimitive_deriv (ha.trans hu.1)
  · exact (density_continuous ha hab).intervalIntegrable

theorem cellMass_le {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    cellMass a b ≤ ∫ u in a..b, log ((u+1)/2)/u := by
  rw [← density_integral ha hab]
  apply intervalIntegral.integral_mono_on hab (density_continuous ha hab).intervalIntegrable
  · apply ContinuousOn.intervalIntegrable_of_Icc (h := hab)
    intro u hu
    have hu0 : 0<u := by linarith [hu.1]
    apply ContinuousAt.continuousWithinAt
    fun_prop (disch := positivity)
  · intro u hu
    have hu0 : 0≤u := by linarith [hu.1]
    exact div_le_div_of_nonneg_right
      (RemainingHf.splitLower_le (by linarith [hu.1] : 1≤(u+1)/2)) hu0

end TerminalE
