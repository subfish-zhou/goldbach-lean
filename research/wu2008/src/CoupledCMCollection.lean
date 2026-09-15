import CoupledCMCollectedJ

namespace CoupledCMCollection
open Real Wu2008DoubleSieve NodeExtension ActualNineFeedback
open FiniteEndpointPayment CoupledIntegralRecovery CoupledFiniteAssembly
open CoupledCMCollectedJ CoupledHGateRecovery CoupledMiddleGateRecovery GatedDensityPayment
open scoped BigOperators
noncomputable section

def jRest (z : Fin 9 → ℝ) (s S : ℝ) : ℝ :=
  tail z (S-2)*log ((S-1)/(s-1))+
    ∑ k : Fin 9,z k*cell S (jStart s S)
      (left (jStart s S-1) (S-2) k) (right (jStart s S-1) (S-2) k)

theorem jRest_eq {z : Fin 9 → ℝ} {s S : ℝ} (hA : 2≤jStart s S)
    (hAS : jStart s S≤S-1) : jRest z s S=CoupledFiniteAssembly.jRest z s S := by
  unfold jRest CoupledFiniteAssembly.jRest
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  have hab : jStart s S-1≤S-2 := by linarith
  have ha := clip_bounds (x := upperLeft k) hab
  have hb := clip_bounds (x := upperNode k) hab
  change jStart s S-1≤left (jStart s S-1) (S-2) k ∧
    left (jStart s S-1) (S-2) k≤S-2 at ha
  change jStart s S-1≤right (jStart s S-1) (S-2) k ∧
    right (jStart s S-1) (S-2) k≤S-2 at hb
  rw [cell_exact (by linarith) (by linarith) (by linarith) (by linarith)
    (by linarith) (by linarith)]

def gate (p : SecondFunctionalParameters) : ℝ :=
  p.kappa2*((gateStart p+1)*log ((upperSwitch p+1)/(gateStart p+1))-
    gateStart p*log (upperSwitch p/gateStart p))

theorem gate_eq (i : Fin 4) : gate (coupledRow i)=gatePayment (coupledRow i) := by
  obtain ⟨ha,hab,_,_,_,_⟩ := original_gate_geometry i
  have hg : gateStart (coupledRow i)≠0 := by linarith
  have hu : upperSwitch (coupledRow i)≠0 := by linarith
  have hg1 : gateStart (coupledRow i)+1≠0 := by linarith
  have hu1 : upperSwitch (coupledRow i)+1≠0 := by linarith
  unfold gate gatePayment gatePrimitive
  rw [log_div hu1 hg1,log_div hu hg]
  ring

def middle (p : SecondFunctionalParameters) : ℝ :=
  log (middleRatio p)*log (lowerSwitch p/upperSwitch p)-oldMiddleBox p

theorem middle_eq (i : Fin 4) : middle (coupledRow i)=middleGain (coupledRow i) := by
  obtain ⟨ha,hab,_,_⟩ := original_middle_geometry i
  unfold middle middleGain middlePayment
  rw [log_div (by linarith : lowerSwitch (coupledRow i)≠0)
    (by linarith : upperSwitch (coupledRow i)≠0)]

def margin (i : Fin 4) : ℝ :=
  NineFeedbackStrength.publication (i.castAdd 5)-NineFeedbackStrength.originalH (i.castAdd 5)+
    aCoefficient (coupledRow i)*CubicCommonProfile.finiteLower NineFeedbackStrength.originalH+
    (4*eRest NineFeedbackStrength.originalH (coupledRow i).S+
      eRest NineFeedbackStrength.originalH (coupledRow i).kappa1+
      jRest NineFeedbackStrength.originalH (coupledRow i).s (coupledRow i).S+
      jRest NineFeedbackStrength.originalH (coupledRow i).kappa2 (coupledRow i).S+
      jRest NineFeedbackStrength.originalH (coupledRow i).kappa3 (coupledRow i).S+
      densityFinite (coupledRow i) NineFeedbackStrength.originalH+
      NineFeedbackStrength.originalH 0*gate (coupledRow i)+
      NineFeedbackStrength.originalH 0*middle (coupledRow i))/5

theorem margin_eq (i : Fin 4) : margin i=NineFeedbackStrength.publication (i.castAdd 5)+
    CubicMiddleJoint.lower (coupledRow i)-NineFeedbackStrength.originalH (i.castAdd 5) := by
  have hp := coupledRow_geometry i
  have hg := coupled_geometry_bounds hp
  have ha0 : 2≤jStart (coupledRow i).s (coupledRow i).S := hp.2.2.1
  have ha2 : 2≤jStart (coupledRow i).kappa2 (coupledRow i).S := hp.2.2.2.1
  have ha3 : 2≤jStart (coupledRow i).kappa3 (coupledRow i).S := hp.2.2.2.2
  have hs0 : jStart (coupledRow i).s (coupledRow i).S≤(coupledRow i).S-1 := by
    have h := (one_le_div (by linarith [hg.1] : 0<(coupledRow i).s)).mpr hg.2.1
    unfold jStart
    linarith
  have hs2 : jStart (coupledRow i).kappa2 (coupledRow i).S≤(coupledRow i).S-1 := by
    have h := (one_le_div (by linarith [hg.2.2.1] : 0<(coupledRow i).kappa2)).mpr hg.2.2.2.1
    unfold jStart
    linarith
  have hs3 : jStart (coupledRow i).kappa3 (coupledRow i).S≤(coupledRow i).S-1 := by
    have h := (one_le_div (by linarith [hg.2.2.2.2.1] : 0<(coupledRow i).kappa3)).mpr hg.2.2.2.2.2.1
    unfold jStart
    linarith
  unfold margin
  rw [jRest_eq ha0 hs0,jRest_eq ha2 hs2,jRest_eq ha3 hs3,gate_eq,middle_eq]
  unfold CubicMiddleJoint.lower remainder
  ring

/-- The complete signed expression is attached to the actual four hc margins. -/
theorem margin_le_original (i : Fin 4) : margin i≤
    NineFeedbackStrength.publication (i.castAdd 5)+
      coupledFeedback (coupledRow i) NineFeedbackStrength.originalH-
      NineFeedbackStrength.originalH (i.castAdd 5) := by
  rw [margin_eq]
  exact CubicMiddleJoint.original_hc_margin i

end
end CoupledCMCollection
