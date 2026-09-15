import D0FullPole
import SigmaInnerProfileIntegral

noncomputable section
namespace D0FullDensity
open Real Set MeasureTheory NodeExtension
open scoped Interval

def leftArg (v : ℝ) : ℝ := (v+3)/(2*(v-1))
def rightArg (v : ℝ) : ℝ := 8/(v+3)
def density (v : ℝ) : ℝ := RemainingHf.splitLower (4/(v-1))/v

theorem split_identity {v : ℝ} (hv : 3 ≤ v) :
    RemainingHf.splitLower (4/(v-1))=
      RemainingHf.basicLower (leftArg v)+RemainingHf.basicLower (rightArg v) := by
  have hv1 : v-1 ≠ 0 := by linarith
  have hv3 : v+3 ≠ 0 := by linarith
  unfold RemainingHf.splitLower Wu04FactorEnvelopes.leftFactor Wu04FactorEnvelopes.rightFactor
    leftArg rightArg
  congr 1
  · congr 1
    field_simp
    ring
  · congr 1
    rw [show 1+4/(v-1)=(v+3)/(v-1) by field_simp; ring]
    field_simp
    norm_num

theorem argument_bounds {v : ℝ} (hv : 3 ≤ v) (hv5 : v ≤ 5) :
    1 ≤ leftArg v ∧ 0 < leftArg v+3/2 ∧ 0 < leftArg v-1/2 ∧
    1 ≤ rightArg v ∧ rightArg v-8/3 < 0 := by
  have hv1 : 0 < v-1 := by linarith
  have hv3 : 0 < v+3 := by linarith
  have hl : 1 ≤ leftArg v := by
    unfold leftArg
    apply (le_div_iff₀ (by positivity : 0<2*(v-1))).mpr
    linarith
  have hr : 1 ≤ rightArg v := by
    unfold rightArg
    apply (le_div_iff₀ hv3).mpr
    linarith
  refine ⟨hl,by linarith,by linarith,hr,?_⟩
  have hr' : rightArg v < 8/3 := by
    unfold rightArg
    apply (div_lt_iff₀ hv3).mpr
    linarith
  linarith

def fullPrimitive (v : ℝ) : ℝ :=
  TerminalE.primitive (-3/2) (leftArg v)-TerminalE.primitive (1/2) (leftArg v)+
  TerminalE.primitive (8/3) (rightArg v)-zeroPrimitive (rightArg v)

theorem fullPrimitive_deriv {v : ℝ} (hv : 3 ≤ v) (hv5 : v ≤ 5) :
    HasDerivAt fullPrimitive (density v) v := by
  obtain ⟨hl,hlm,hlp,hr,hrp⟩ := argument_bounds hv hv5
  have hv0 : v ≠ 0 := by linarith
  have hv1 : v-1 ≠ 0 := by linarith
  have hv3 : v+3 ≠ 0 := by linarith
  have hleft : HasDerivAt leftArg (-2/(v-1)^2) v := by
    convert (((hasDerivAt_id v).add_const 3).div
      (((hasDerivAt_id v).sub_const 1).const_mul 2) (by positivity : 2*(v-1) ≠ 0)) using 1 <;>
      first | rfl | skip
    dsimp
    field_simp
    ring
  have hright : HasDerivAt rightArg (-8/(v+3)^2) v := by
    convert (((hasDerivAt_id v).add_const 3).inv hv3).const_mul 8 using 1 <;>
      first | rfl | (dsimp; ring)
  have h0 := (primitive_deriv (by norm_num : (-3/2:ℝ) ≠ 0)
    (by norm_num : (-3/2:ℝ)+1 ≠ 0) (by norm_num [TerminalE.q] : TerminalE.q (-3/2) ≠ 0)
    hl (by convert hlm.ne' using 1; ring)).comp v hleft
  have h1 := (TerminalE.primitive_deriv (by norm_num : (0:ℝ)<1/2) hl hlp.ne').comp v hleft
  have h2 := (TerminalE.primitive_deriv (by norm_num : (0:ℝ)<8/3) hr hrp.ne).comp v hright
  have h3 := (zeroPrimitive_deriv hr).comp v hright
  convert ((h0.sub h1).add h2).sub h3 using 1 <;> first | rfl | skip
  dsimp [density]
  rw [split_identity hv]
  have hL0 : leftArg v-(-3/2)=2*v/(v-1) := by unfold leftArg; field_simp; ring
  have hL1 : leftArg v-1/2=2/(v-1) := by unfold leftArg; field_simp; ring
  have hR : rightArg v-8/3= -8*v/(3*(v+3)) := by unfold rightArg; field_simp; ring
  rw [hL0,hL1,hR]
  dsimp [rightArg]
  field_simp [hv0,hv1,hv3]
  ring

theorem basic_continuousAt {x : ℝ} (hx : 0<x) : ContinuousAt RemainingHf.basicLower x := by
  unfold RemainingHf.basicLower F1FullRecoveryPayment.lowerGapPayment
    Wu2008DoubleSieve.SharpLogRecurrence.lowerLog Wu2008DoubleSieve.SharpLogRecurrence.upperLog
    F1LowerResidual.payment F1LowerResidual.denom
  fun_prop (disch := positivity)

theorem density_continuous : ContinuousOn density (uIcc (3:ℝ) 5) := by
  rw [uIcc_of_le (by norm_num : (3:ℝ)≤5)]
  intro v hv
  have hv0 : v ≠ 0 := by linarith [hv.1]
  have hv1 : v-1 ≠ 0 := by linarith [hv.1]
  have hv1p : 0<v-1 := by linarith [hv.1]
  have hx : 0 < 4/(v-1) := by positivity
  have hleft : 0 < Wu04FactorEnvelopes.leftFactor (4/(v-1)) := by
    unfold Wu04FactorEnvelopes.leftFactor
    positivity
  have hright : 0 < Wu04FactorEnvelopes.rightFactor (4/(v-1)) := by
    unfold Wu04FactorEnvelopes.rightFactor
    positivity
  unfold density RemainingHf.splitLower
  apply ContinuousAt.continuousWithinAt
  apply ContinuousAt.div _ continuousAt_id hv0
  apply ContinuousAt.add
  · apply ContinuousAt.comp (g := RemainingHf.basicLower) (f := fun v : ℝ => Wu04FactorEnvelopes.leftFactor (4/(v-1))) (basic_continuousAt hleft)
    unfold Wu04FactorEnvelopes.leftFactor
    fun_prop (disch := assumption)
  · apply ContinuousAt.comp (g := RemainingHf.basicLower) (f := fun v : ℝ => Wu04FactorEnvelopes.rightFactor (4/(v-1))) (basic_continuousAt hright)
    unfold Wu04FactorEnvelopes.rightFactor
    fun_prop (disch := positivity)

/-- Exact full-domain once-split mass, not the previous fixed-coefficient payment. -/
def fullMass : ℝ := fullPrimitive 5-fullPrimitive 3

theorem density_integral : (∫ v in (3:ℝ)..5,density v)=fullMass := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro v hv
    rw [uIcc_of_le (by norm_num : (3:ℝ)≤5)] at hv
    exact fullPrimitive_deriv hv.1 hv.2
  · exact density_continuous.intervalIntegrable

theorem fullMass_le_D0 : fullMass ≤ D0 := by
  rw [← density_integral]
  change (∫ v in (3:ℝ)..5,density v) ≤ ∫ v in (3:ℝ)..5, log (4/(v-1))/v
  have hi : IntervalIntegrable (fun v : ℝ => log (4/(v-1))/v) volume 3 5 := by
    apply ContinuousOn.intervalIntegrable_of_Icc (h := by norm_num)
    intro v hv
    have hv0 : 0<v := by linarith [hv.1]
    have hv1 : 0<v-1 := by linarith [hv.1]
    apply ContinuousAt.continuousWithinAt
    fun_prop (disch := positivity)
  apply intervalIntegral.integral_mono_on (by norm_num) density_continuous.intervalIntegrable hi
  intro v hv
  have hv1 : 0<v-1 := by linarith [hv.1]
  exact div_le_div_of_nonneg_right
    (RemainingHf.splitLower_le ((one_le_div hv1).mpr (by linarith [hv.2]))) (by linarith [hv.1])

end D0FullDensity
