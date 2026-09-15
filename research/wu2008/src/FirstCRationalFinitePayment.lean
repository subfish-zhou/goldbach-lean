import FirstCRationalCollected

noncomputable section
open Real Set MeasureTheory
open scoped Interval
open FirstIntegralRecovery Wu08OriginalFirstSteps Wu2008DoubleSieve SharpLogRecurrence
namespace FirstCRationalPayment

def residueA : ℝ := (104612377246377427527815209111679744/39718485152665208530677440192121)
def residueB : ℝ := (-42669554113724007422501216061341925731840/16356745075999619879454582003479248778787)
def residueC : ℝ := (-10171860499583562168530544984204899072/3870252578140107956192622055344363)
def residueD : ℝ := (-2400004246990329338908198130480633272576/167861172709101151140958712418055048929)
def rationalEndpointPart : ℝ := (-6155677056626368891786728296959751781121879838782533098252105992768/31882001125214926572581930244042659121940902285018356675015138523)

/-- Exact common-log collection before applying any inequality. -/
def signedMainLogs : ℝ :=
  (1+residueB)*(log 2+log (3/2)) + log (1127/600) +
  residueA*log (3884129/3606400) + (residueA+residueC)*log (4508/2927) -
  residueB*log (2400/2381) + residueD*log (4508/3981) + rationalEndpointPart

/-- The existing L/V bounds, each used once with the paying sign. -/
def finiteMainPayment : ℝ :=
  (1+residueB)*(JointLogTotalComparison.V 2+JointLogTotalComparison.V (3/2)) + lowerLog (1127/600) +
  residueA*lowerLog (3884129/3606400) + (residueA+residueC)*lowerLog (4508/2927) -
  residueB*lowerLog (2400/2381) + residueD*JointLogTotalComparison.V (4508/3981) + rationalEndpointPart

theorem residue_signs :
    0 ≤ residueA ∧ 0 ≤ residueA+residueC ∧ residueB ≤ 0 ∧ 1+residueB ≤ 0 ∧ residueD ≤ 0 := by
  norm_num [residueA,residueB,residueC,residueD]

theorem signedMainLogs_exact : log (1127/200)+collectedMass = signedMainLogs := by
  have hbase : log ((1127:ℝ)/200) = log 3+log (1127/600) := by
    rw [← log_mul (by norm_num : (3:ℝ) ≠ 0) (by norm_num : (1127:ℝ)/600 ≠ 0)]
    norm_num
  have hthree : log (3:ℝ) = log 2+log (3/2) := by
    rw [← log_mul (by norm_num : (2:ℝ) ≠ 0) (by norm_num : (3:ℝ)/2 ≠ 0)]
    norm_num
  have hcommon : log ((1327:ℝ)/800) = log (3884129/3606400)+log (4508/2927) := by
    rw [← log_mul (by norm_num : (3884129:ℝ)/3606400 ≠ 0) (by norm_num : (4508:ℝ)/2927 ≠ 0)]
    norm_num
  have hnear : log ((2381:ℝ)/800) = log 3-log (2400/2381) := by
    rw [← log_div (by norm_num : (3:ℝ) ≠ 0) (by norm_num : (2400:ℝ)/2381 ≠ 0)]
    norm_num
  unfold collectedMass signedMainLogs residueA residueB residueC residueD rationalEndpointPart
  rw [hbase,hcommon,hnear,hthree]
  ring

theorem finiteMainPayment_le_signedMainLogs : finiteMainPayment ≤ signedMainLogs := by
  obtain ⟨ha,hac,hb,hb1,hd⟩ := residue_signs
  have h2 := mul_le_mul_of_nonpos_left
    (add_le_add (JointLogTotalComparison.log_le_V (by norm_num : (1:ℝ) ≤ 2))
      (JointLogTotalComparison.log_le_V (by norm_num : (1:ℝ) ≤ 3/2))) hb1
  have hbase := log_lower (by norm_num : (1:ℝ) ≤ 1127/600)
  have hcommon := mul_le_mul_of_nonneg_left (log_lower (by norm_num : (1:ℝ) ≤ 3884129/3606400)) ha
  have haclog := mul_le_mul_of_nonneg_left (log_lower (by norm_num : (1:ℝ) ≤ 4508/2927)) hac
  have hnear := mul_le_mul_of_nonpos_left (log_lower (by norm_num : (1:ℝ) ≤ 2400/2381)) hb
  have hdlog := mul_le_mul_of_nonpos_left
    (JointLogTotalComparison.log_le_V (by norm_num : (1:ℝ) ≤ 4508/3981)) hd
  unfold finiteMainPayment signedMainLogs
  linarith only [h2,hbase,hcommon,haclog,hnear,hdlog]

/-- All true logarithmic recovery is retained, not silently discarded. -/
def logRecovery : ℝ := signedMainLogs-finiteMainPayment

theorem logRecovery_nonneg : 0 ≤ logRecovery := sub_nonneg.mpr finiteMainPayment_le_signedMainLogs

/-- Exact unpaid rational debit for this single prescribed L/V payment. -/
def finitePaymentDebit : ℝ := (14900897:ℝ)/8000000-finiteMainPayment

theorem finitePaymentDebit_positive : 0 < finitePaymentDebit := by
  norm_num [finitePaymentDebit,finiteMainPayment,residueA,residueB,residueC,residueD,
    rationalEndpointPart,JointLogTotalComparison.V,lowerLog,upperLog]

theorem publicationResidual_exact_recoveries :
    publicationResidual = finitePaymentDebit-logRecovery-E (1327/200) := by
  unfold publicationResidual finitePaymentDebit logRecovery
  rw [← signedMainLogs_exact]
  ring

theorem endpointFirst_exact_recoveries :
    endpointFirst = 8*(finiteMainPayment+logRecovery+E (1327/200)) := by
  rw [endpointFirst,endpointMass_eq_collectedMass]
  unfold logRecovery
  rw [← signedMainLogs_exact]
  ring

/-- Sufficient remaining recovery inequality, with exact original E only once. -/
theorem publication_count_of_true_recoveries
    (h : finitePaymentDebit ≤ logRecovery+E (1327/200))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ((14900897:ℝ)/1000000-ε)*wuSingularSeries N*N/log N^(2 : ℕ) ≤
        (sieveCount N 1 N ((N : ℝ)^truncatedSixthLowerAlpha) : ℝ) := by
  apply new_mass_suffices_for_publication_count ?_ hε
  apply publication_payment_iff_residual_nonpos.mpr
  rw [publicationResidual_exact_recoveries]
  linarith only [h]

end FirstCRationalPayment
