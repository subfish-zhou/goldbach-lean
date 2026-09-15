import AnalyticTotalThreshold

namespace Wu2008DoubleSieve.JointJLossStrength
open Real Set MeasureTheory SharpLogRecurrence SharpJBalance
open scoped Interval
noncomputable section

/-- An existing-envelope endpoint, not a new logarithmic approximation. -/
def gap : ℝ := upperLog ((1-2*s)/s)-log ((1-2*s)/s)
/-- The complete original ninth-domain kernel mass. -/
def mass : ℝ := log (s/b)+log ((1-b)/(1-s))
def recovery : ℝ := 8*gap*mass

theorem gap_monotone : MonotoneOn (fun x => upperLog x-log x) (Ici 1) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 1)
    (fun x hx => (upper_gap_derivative hx).continuousAt.continuousWithinAt)
    (fun x hx => (upper_gap_derivative (interior_subset hx)).hasDerivWithinAt)
  intro x hx
  exact div_nonneg (by positivity) (by positivity)

/-- Compare the two original envelope errors by their original derivatives.
No series is introduced: this is a global rational derivative comparison. -/
theorem envelope_error_comparison {x : ℝ} (hx : 1 ≤ x) :
    (2/5)*(upperLog x-lowerLog x) ≤ upperLog x-log x := by
  have hd (t : ℝ) (ht : 1 ≤ t) :
      HasDerivAt (fun t => (upperLog t-log t)-(2/3)*(log t-lowerLog t))
        ((t-1)^6/(6*t^2*(t+1)^4)) t := by
    have h := (upper_gap_derivative ht).sub ((lower_gap_derivative ht).const_mul (2/3))
    have ht0 : t ≠ 0 := by linarith
    have ht1 : t+1 ≠ 0 := by linarith
    convert h using 1 <;> first | rfl | (field_simp [ht0,ht1]; ring)
  have h := anchored_nonnegative hd (fun t ht => by positivity) hx
  have hzero : upperLog 1-log 1-(2/3)*(log 1-lowerLog 1) = 0 := by norm_num [upperLog,lowerLog]
  rw [hzero] at h
  linarith only [h]

def massPayment : ℝ := lowerLog 2+lowerLog ((s/b)/2)+lowerLog ((1-b)/(1-s))
def fixedRecovery : ℝ := 8*((2/5)*(upperLog ((1-2*s)/s)-lowerLog ((1-2*s)/s)))*massPayment

theorem fixedRecovery_le_recovery : fixedRecovery ≤ recovery := by
  have he := envelope_error_comparison (x := (1-2*s)/s)
    (by norm_num [s,SeventhEighth.sigma,SeventhEighth.alpha])
  have h2 := log_lower (by norm_num : (1 : ℝ) ≤ 2)
  have h1 := log_lower (t := (s/b)/2)
    (by norm_num [s,b,SeventhEighth.sigma,SeventhEighth.alpha,ninthProfileK2])
  have h3 := log_lower (t := (1-b)/(1-s))
    (by norm_num [s,b,SeventhEighth.sigma,SeventhEighth.alpha,ninthProfileK2])
  have hm : massPayment ≤ mass := by
    unfold massPayment mass
    rw [log_split_two (by norm_num [s,b,SeventhEighth.sigma,SeventhEighth.alpha,ninthProfileK2] : 0 < s/b)]
    linarith only [h1,h2,h3]
  have hp : 0 ≤ massPayment := by
    norm_num [massPayment,lowerLog,s,b,SeventhEighth.sigma,SeventhEighth.alpha,ninthProfileK2]
  have hg : 0 ≤ (2/5)*(upperLog ((1-2*s)/s)-lowerLog ((1-2*s)/s)) := by
    norm_num [upperLog,lowerLog,s,SeventhEighth.sigma,SeventhEighth.alpha]
  have hprod := mul_le_mul he hm hp (hg.trans he)
  change _ ≤ gap*mass at hprod
  unfold fixedRecovery recovery
  nlinarith only [hprod]

theorem gap_nonnegative : 0 ≤ gap := by
  exact sub_nonneg.mpr (log_upper (by
    norm_num [s,SeventhEighth.sigma,SeventhEighth.alpha]))

theorem ninth_integral_recovery : J9+gap*mass ≤
    ninthA*log (s/b)+ninthB*log ((1-b)/(1-s))+
    ninthC*(1/(1-s)-1/(1-b))+ninthD*log ((1-s-b)/(1-2*s)) := by
  have hb : 0 < b := by norm_num [b,ninthProfileK2]
  have hbs : b ≤ s := by norm_num [b,s,SeventhEighth.sigma,SeventhEighth.alpha,ninthProfileK2]
  have hs0 : 0 < s := hb.trans_le hbs
  have hs3 : s < 1/3 := by norm_num [s,SeventhEighth.sigma,SeventhEighth.alpha]
  have hs1 : s < 1 := by linarith
  have hi := packet_integrable (A := ninthA) (E := 0) (B := ninthB) (C := ninthC)
    (D := ninthD) (d := 1-s) (e := 1) hb hbs hs1 (by norm_num) (by linarith)
  have hk := packet_integrable (A := 1) (E := 0) (B := 1) (C := 0)
    (D := 0) (d := 1) (e := 1) hb hbs hs1 (by norm_num) (by linarith)
  have keq (t : ℝ) (ht : t ∈ Icc b s) :
      packet 1 0 1 0 0 1 1 t = 1/(t*(1-t)) := by
    have ht0 : t ≠ 0 := (hb.trans_le ht.1).ne'
    have ht1 : 1-t ≠ 0 := by linarith [ht.2]
    dsimp [packet]
    field_simp
    ring
  have hmono := intervalIntegral.integral_mono_on hbs
    (J9_integrable.add (hk.const_mul gap)) hi (fun t ht => by
      have ht0 := hb.trans_le ht.1
      have ht1 : 0 < 1-t := by linarith [ht.2]
      have ht2 : 0 < 1-s-t := by linarith [ht.2]
      have hmin : 1 ≤ (1-2*s)/s := (le_div_iff₀ hs0).2 (by linarith)
      have harg : (1-2*s)/s ≤ (1-s-t)/s :=
        (div_le_div_iff_of_pos_right hs0).2 (by linarith [ht.2])
      have hg := gap_monotone hmin (hmin.trans harg) harg
      change gap ≤ upperLog ((1-s-t)/s)-log ((1-s-t)/s) at hg
      change log ((1-s-t)/s)/(t*(1-t))+gap*packet 1 0 1 0 0 1 1 t ≤ _
      rw [keq t ht]
      have hd := div_le_div_of_nonneg_right hg (mul_pos ht0 ht1).le
      have he : packet ninthA 0 ninthB ninthC ninthD (1-s) 1 t =
          upperLog ((1-s-t)/s)/(t*(1-t)) := by
        dsimp [packet,upperLog,ninthA,ninthB,ninthC,ninthD]
        have hsne : 1-s ≠ 0 := by linarith
        field_simp [hsne]
        ring
      rw [he]
      rw [sub_div] at hd
      simp only [mul_one_div]
      linarith only [hd])
  have hj : IntervalIntegrable (fun t => log ((1-s-t)/s)/(t*(1-t))) volume b s := J9_integrable
  change (∫ t in b..s, log ((1-s-t)/s)/(t*(1-t))+gap*packet 1 0 1 0 0 1 1 t) ≤ _ at hmono
  rw [intervalIntegral.integral_add hj (hk.const_mul gap),
    intervalIntegral.integral_const_mul] at hmono
  rw [packet_integral hb hbs hs1 (by norm_num) (by linarith),
    packet_integral hb hbs hs1 (by norm_num) (by linarith)] at hmono
  change J9+_ ≤ _ at hmono
  norm_num at hmono
  rw [show 1-s-s=1-2*s by ring] at hmono
  simpa only [mass,one_div] using hmono

/-- Original ninth endpoint payments, with the integral recovery retained. -/
theorem ninth_residual_recovery :
    J9+gap*mass ≤ UnroundedPayments.j9Upper-ninthA*(SignedTotalCorrelation.d2-SignedTotalCorrelation.e2) := by
  unfold SignedTotalCorrelation.d2 SignedTotalCorrelation.e2
  have h9 := ninth_integral_recovery
  rw [log_split_two (by norm_num [b,s,SeventhEighth.sigma,SeventhEighth.alpha,ninthProfileK2] : 0 < s/b)] at h9
  have h91 := log_upper (t := (s/b)/2)
    (by norm_num [b,s,SeventhEighth.sigma,SeventhEighth.alpha,ninthProfileK2])
  have h92 := log_upper (t := (1-b)/(1-s))
    (by norm_num [b,s,SeventhEighth.sigma,SeventhEighth.alpha,ninthProfileK2])
  have h93 := log_lower (t := (1-s-b)/(1-2*s))
    (by norm_num [b,s,SeventhEighth.sigma,SeventhEighth.alpha,ninthProfileK2])
  norm_num [b,s,SeventhEighth.alpha,SeventhEighth.sigma,ninthProfileK2,
    ninthA,ninthB,ninthC,ninthD,upperLog,lowerLog,UnroundedPayments.j9Upper] at h9 h91 h92 h93 ⊢
  linarith

theorem weighted_j_recovery :
    16*SeventhEighth.J7+8*SeventhEighth.J8+8*J9+recovery ≤
    UnroundedPayments.weightedJUpper-SignedTotalCorrelation.jTwo*
      (SignedTotalCorrelation.d2-SignedTotalCorrelation.e2) := by
  have h7 := UnroundedPayments.J7_le_j7Upper
  have h8 := SignedTotalCorrelation.eighth_residual_upper
  have h9 := ninth_residual_recovery
  unfold UnroundedPayments.weightedJUpper SignedTotalCorrelation.jTwo recovery
  nlinarith only [h7,h8,h9]

theorem actual_jLoss_lower : recovery ≤ AnalyticTotalThreshold.jLoss := by
  have h := weighted_j_recovery
  unfold AnalyticTotalThreshold.jLoss
  linarith only [h]

/-- Consume the recovered integral error once in the original seven-loss identity. -/
theorem strengthened_coefficient_lower :
    AnalyticTotalThreshold.coefficient+recovery/4 ≤ JointHMotherPayment.unroundedCoefficient := by
  have h := actual_jLoss_lower
  have hn := AnalyticTotalThreshold.signed_losses_nonnegative
  have hm := AnalyticTotalThreshold.losses_nonnegative
  have he := AnalyticTotalThreshold.actual_gap_identity
  rw [AnalyticTotalThreshold.signed_loss_identity] at he
  linarith only [h,hn.1,hn.2.1,hn.2.2.2,hm.2.1,hm.2.2.1,hm.2.2.2,he]

theorem fixed_actual_jLoss_lower : fixedRecovery ≤ AnalyticTotalThreshold.jLoss :=
  fixedRecovery_le_recovery.trans actual_jLoss_lower

theorem fixed_coefficient_lower :
    AnalyticTotalThreshold.coefficient+fixedRecovery/4 ≤ JointHMotherPayment.unroundedCoefficient := by
  have h := strengthened_coefficient_lower
  have hf := fixedRecovery_le_recovery
  linarith only [h,hf]

theorem fixedRecovery_positive : 0 < fixedRecovery := by
  norm_num [fixedRecovery,massPayment,upperLog,lowerLog,s,b,SeventhEighth.sigma,SeventhEighth.alpha,ninthProfileK2]

end
end Wu2008DoubleSieve.JointJLossStrength
