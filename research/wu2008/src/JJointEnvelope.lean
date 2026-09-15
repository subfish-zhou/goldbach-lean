import OldPackageWidth

noncomputable section
open Real Set MeasureTheory Wu2008DoubleSieve
open SharpLogRecurrence SharpJBalance JCubicActualMass
open scoped Interval
namespace JJointEnvelope

/-- The unchanged original U and L are combined before integration. -/
theorem scalar {q d U L : ℝ} (hq : 1 ≤ q) (hd : 0 < d)
    (hU : U=upperLog q/d) (hL : L=lowerLog q/d) :
    log q/d ≤ (3/5)*U+(2/5)*L := by
  have h := div_le_div_of_nonneg_right (JointLogTotalComparison.log_le_V hq) hd.le
  rw [hU,hL]
  unfold JointLogTotalComparison.V at h
  convert h using 1 <;> first | rfl | ring

def upper7 : ℝ := (7/6)*log ((1/3)/s)+(1/6)*(1/s-3)+(4/3)*log ((1-s)/(2/3))-
  (8/3)*(3/2-1/(1-s))-(1/6)*log ((1-2*s)/(1/3))
def upper8 : ℝ := (25/36)*log ((1/3)/a)+(4/9)*log ((1-a)/(2/3))-
  (8/9)*(3/2-1/(1-a))-(1/4)*log (2-3*a)
def upper9 : ℝ := ninthA*log (s/b)+ninthB*log ((1-b)/(1-s))+
  ninthC*(1/(1-s)-1/(1-b))+ninthD*log ((1-s-b)/(1-2*s))

theorem seventh : SeventhEighth.J7 ≤ (3/5)*upper7+(2/5)*fullMass 1 3 s (1/3) := by
  have hs0 : 0 < s := by norm_num [s,SeventhEighth.sigma,SeventhEighth.alpha]
  have hs : s ≤ (1/3:ℝ) := SeventhEighth.classical_parameters.2.2.le
  have hi := packet_integrable (A := 7/6) (E := 1/6) (B := 4/3) (C := -8/3)
    (D := -1/3) (d := 1) (e := 2) hs0 hs (by norm_num) (by norm_num) (by norm_num)
  have hl := full_integrable 1 3 hs0 hs (by norm_num)
  have hp (t : ℝ) (ht : t ∈ Icc s (1/3:ℝ)) :
      log ((1-2*t)/t)/(t*(1-t)) ≤
      (3/5)*packet (7/6) (1/6) (4/3) (-8/3) (-1/3) 1 2 t+(2/5)*fullDensity 1 3 t := by
    have ht0 := hs0.trans_le ht.1
    have ht1 : 0 < 1-t := by linarith [ht.2]
    have ht2 : 0 < 1-2*t := by linarith [ht.2]
    apply scalar ((le_div_iff₀ ht0).2 (by linarith [ht.2])) (mul_pos ht0 ht1)
    · dsimp [packet,upperLog]
      field_simp [(show 1-t*2 ≠ 0 by linarith),
        (show 1-t*2+t ≠ 0 by linarith),
        (show 1-t*3+t^2*2 ≠ 0 by nlinarith [mul_pos ht1 ht2])]
      ring
    · rw [fullDensity_eq 1 3 ht0.ne' ht1.ne']
      dsimp [lowerLog]; field_simp; ring
  have h := intervalIntegral.integral_mono_on hs SeventhEighth.J7_integrable
    ((hi.const_mul (3/5)).add (hl.const_mul (2/5))) hp
  rw [intervalIntegral.integral_add (hi.const_mul _) (hl.const_mul _),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,
    packet_integral hs0 hs (by norm_num) (by norm_num) (by norm_num),
    full_integral 1 3 hs0 hs (by norm_num)] at h
  change SeventhEighth.J7 ≤ _ at h
  dsimp [upper7]
  norm_num at h ⊢
  linarith only [h]

theorem eighth : SeventhEighth.J8 ≤ (3/5)*upper8+(2/5)*fullMass (1/3) 1 a (1/3) := by
  have ha : 0 < a := SeventhEighth.classical_parameters.1
  have hab : a ≤ (1/3:ℝ) := SeventhEighth.classical_parameters.2.1.le.trans
    SeventhEighth.classical_parameters.2.2.le
  have hi := packet_integrable (A := 25/36) (E := 0) (B := 4/9) (C := -8/9)
    (D := -3/4) (d := 2) (e := 3) ha hab (by norm_num) (by norm_num) (by norm_num)
  have hl := full_integrable (1/3) 1 ha hab (by norm_num)
  have hp (t : ℝ) (ht : t ∈ Icc a (1/3:ℝ)) :
      log (2-3*t)/(t*(1-t)) ≤
      (3/5)*packet (25/36) 0 (4/9) (-8/9) (-3/4) 2 3 t+(2/5)*fullDensity (1/3) 1 t := by
    have ht0 := ha.trans_le ht.1
    have ht1 : 0 < 1-t := by linarith [ht.2]
    have ht2 : 0 < 2-3*t := by linarith [ht.2]
    have ht3 : 3-3*t ≠ 0 := by linarith
    apply scalar (by linarith [ht.2]) (mul_pos ht0 ht1)
    · dsimp [packet,upperLog]
      field_simp [ht3,(show 2-t*3 ≠ 0 by linarith),
        (show 2-t*3+1 ≠ 0 by linarith),
        (show 6-t*15+t^2*9 ≠ 0 by nlinarith [mul_pos ht1 ht2])]
      ring
    · rw [fullDensity_eq (1/3) 1 ht0.ne' ht1.ne']
      dsimp [lowerLog]; field_simp [ht3]; ring
  have h := intervalIntegral.integral_mono_on hab SeventhEighth.J8_integrable
    ((hi.const_mul (3/5)).add (hl.const_mul (2/5))) hp
  rw [intervalIntegral.integral_add (hi.const_mul _) (hl.const_mul _),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,
    packet_integral ha hab (by norm_num) (by norm_num) (by norm_num),
    full_integral (1/3) 1 ha hab (by norm_num)] at h
  change SeventhEighth.J8 ≤ _ at h
  dsimp [upper8]
  norm_num at h ⊢
  linarith only [h]

theorem ninth : J9 ≤ (3/5)*upper9+(2/5)*fullMass (1-2*s) 1 b s := by
  have hb : 0 < b := by norm_num [b,ninthProfileK2]
  have hbs : b ≤ s := by norm_num [b,s,SeventhEighth.sigma,SeventhEighth.alpha,ninthProfileK2]
  have hs0 := hb.trans_le hbs
  have hs3 : s < 1/3 := SeventhEighth.classical_parameters.2.2
  have hs1 : s < 1 := by linarith
  have hi := packet_integrable (A := ninthA) (E := 0) (B := ninthB) (C := ninthC)
    (D := ninthD) (d := 1-s) (e := 1) hb hbs hs1 (by norm_num) (by linarith)
  have hl := full_integrable (1-2*s) 1 hb hbs hs1
  have hp (t : ℝ) (ht : t ∈ Icc b s) :
      log ((1-s-t)/s)/(t*(1-t)) ≤
      (3/5)*packet ninthA 0 ninthB ninthC ninthD (1-s) 1 t+(2/5)*fullDensity (1-2*s) 1 t := by
    have ht0 := hb.trans_le ht.1
    have ht1 : 0 < 1-t := by linarith [ht.2]
    have ht2 : 0 < 1-s-t := by linarith [ht.2]
    have hsne : 1-s ≠ 0 := by linarith
    apply scalar ((le_div_iff₀ hs0).2 (by linarith [ht.2])) (mul_pos ht0 ht1)
    · dsimp [packet,upperLog,ninthA,ninthB,ninthC,ninthD]; field_simp [hsne]; ring
    · rw [fullDensity_eq (1-2*s) 1 ht0.ne' ht1.ne']
      dsimp [lowerLog]; field_simp; ring
  have h := intervalIntegral.integral_mono_on hbs J9_integrable
    ((hi.const_mul (3/5)).add (hl.const_mul (2/5))) hp
  rw [intervalIntegral.integral_add (hi.const_mul _) (hl.const_mul _),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,
    packet_integral hb hbs hs1 (by norm_num) (by linarith),
    full_integral (1-2*s) 1 hb hbs hs1] at h
  change J9 ≤ _ at h
  dsimp [upper9]
  norm_num at h ⊢
  rw [show 1-s-s=1-2*s by ring] at h
  exact h

def upperMass : ℝ := 16*upper7+8*upper8+8*upper9

theorem complete_mixture : JFourRemainingMagnitude.actualJ ≤
    (3/5)*upperMass+(2/5)*JFourRemainingMagnitude.jLowerReal := by
  unfold JFourRemainingMagnitude.actualJ JFourRemainingMagnitude.jLowerReal upperMass
  linarith only [seventh,eighth,ninth]

/-- This replaces, rather than adds to, the previous J recovery. -/
def newJLower : ℝ := (UnroundedPayments.weightedJUpper-SignedTotalCorrelation.jTwo*
  (SignedTotalCorrelation.d2-SignedTotalCorrelation.e2)-
  ((3/5)*upperMass+(2/5)*JFourRemainingMagnitude.jLowerReal))

theorem j_loss_lower : newJLower ≤ AnalyticTotalThreshold.jLoss := by
  have h := complete_mixture
  unfold newJLower AnalyticTotalThreshold.jLoss JFourRemainingMagnitude.actualJ at *
  linarith only [h]

def upperPacket (f : ℝ → ℝ) : ℝ :=
  16*((7/6)*f ((1/3)/s)+(1/6)*(1/s-3)+(4/3)*f ((1-s)/(2/3))-
    (8/3)*(3/2-1/(1-s))-(1/6)*f ((1-2*s)/(1/3)))+
  8*((25/36)*(2*(f (4/3)+f (3/2))+f (((1/3)/a)/4))+
    (4/9)*f ((1-a)/(2/3))-(8/9)*(3/2-1/(1-a))-(1/4)*f (2-3*a))+
  8*(ninthA*(f (4/3)+f (3/2)+f ((s/b)/2))+ninthB*f ((1-b)/(1-s))+
    ninthC*(1/(1-s)-1/(1-b))+ninthD*f ((1-s-b)/(1-2*s)))

theorem upper_packet_identity : upperMass=upperPacket log := by
  unfold upperMass upper7 upper8 upper9 upperPacket
  rw [log_split_four (by norm_num [a,SeventhEighth.alpha] : (0:ℝ)<(1/3)/a),
    log_split_two (by norm_num [b,s,ninthProfileK2,SeventhEighth.sigma,SeventhEighth.alpha] : 0<s/b),
    GlobalSignedActualComparison.log_two]

def gainPacket (f : ℝ → ℝ) : ℝ :=
  (UnroundedPayments.weightedJUpper-SignedTotalCorrelation.jTwo*(upperLog 2-(f (4/3)+f (3/2)))-
    ((3/5)*upperPacket f+(2/5)*GlobalSignedActualComparison.jLower f)-
    JointJLossStrength.fixedRecovery)/4

theorem gain_packet_identity : (newJLower-JointJLossStrength.fixedRecovery)/4=gainPacket log := by
  unfold newJLower gainPacket
  rw [upper_packet_identity,GlobalSignedActualComparison.j_lower_identity]
  unfold SignedTotalCorrelation.d2 SignedTotalCorrelation.e2
  rw [GlobalSignedActualComparison.log_two]
  ring

end JJointEnvelope
