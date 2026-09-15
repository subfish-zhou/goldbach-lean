import FirstCRationalFinitePayment

noncomputable section
open Real Set MeasureTheory
open scoped Interval
open FirstIntegralRecovery Wu08OriginalFirstSteps Wu2008DoubleSieve SharpLogRecurrence
namespace FirstCRationalPayment

def rationalMainPayment : ℝ := 168550228562328259987578768984992313348337565915940000820905250383373767972846042064009569129695002683854532602032778844188767519/90608131520353048849823162561380324282955244313917519210629937376594424419855630973643792941758742621267045769589303862429448750

def rationalPublicationDebit : ℝ := 1392485318886483717242609329156706544171539043200490948700799118474868217428140396959456221531200942539198152538974721802596350823/579892041730259512638868240392834075410913563609072122948031599210204316287076038231320274827255952776109092925371544719548472000000

theorem finiteMainPayment_exact : finiteMainPayment = rationalMainPayment := by
  norm_num [finiteMainPayment,rationalMainPayment,residueA,residueB,residueC,residueD,
    rationalEndpointPart,JointLogTotalComparison.V,lowerLog,upperLog]

theorem finitePaymentDebit_exact : finitePaymentDebit = rationalPublicationDebit := by
  rw [finitePaymentDebit,finiteMainPayment_exact]
  norm_num [rationalPublicationDebit,rationalMainPayment]

theorem rationalPublicationDebit_positive : 0 < rationalPublicationDebit := by
  rw [← finitePaymentDebit_exact]
  exact finitePaymentDebit_positive

/-- Exact rational lower certificate with the original E retained once. -/
def rationalFirstCoefficient : ℝ := 8*(rationalMainPayment+E (1327/200))

theorem rationalFirstCoefficient_le_endpointFirst : rationalFirstCoefficient ≤ endpointFirst := by
  rw [endpointFirst_exact_recoveries,finiteMainPayment_exact]
  unfold rationalFirstCoefficient
  linarith only [logRecovery_nonneg]

/-- Actual sieve counting consumes the evaluated certificate, not an abstract surrogate. -/
theorem rationalFirstCoefficient_actual_count {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (rationalFirstCoefficient-ε)*wuSingularSeries N*N/log N^(2 : ℕ) ≤
        (sieveCount N 1 N ((N : ℝ)^truncatedSixthLowerAlpha) : ℝ) := by
  have hδ : 0 < endpointFirst-rationalFirstCoefficient+ε := by
    linarith only [rationalFirstCoefficient_le_endpointFirst,hε]
  obtain ⟨T,hT,h⟩ := endpointFirst_actual_count hδ
  refine ⟨T,hT,?_⟩
  intro N hN hEven
  have heq : endpointFirst-(endpointFirst-rationalFirstCoefficient+ε) =
      rationalFirstCoefficient-ε := by ring
  simpa only [heq] using h N hN hEven

/-- Fully explicit first unpaid amount. Its sign is not proved. -/
theorem exact_publication_gap :
    (14900897:ℝ)/1000000-endpointFirst =
      8*(rationalPublicationDebit-logRecovery-E (1327/200)) := by
  rw [← publicationResidual_eq_gap,publicationResidual_exact_recoveries,finitePaymentDebit_exact]

end FirstCRationalPayment
