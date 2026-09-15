import FirstCRationalEndpoints

noncomputable section
open Real Set MeasureTheory
open scoped Interval
open FirstIntegralRecovery Wu08OriginalFirstSteps Wu2008DoubleSieve
namespace FirstCRationalPayment

/-- Four logarithms of original endpoint ratios plus an exact rational remainder. -/
def collectedMass : ℝ :=
  (104612377246377427527815209111679744/39718485152665208530677440192121)*log (1327/800) +
  (-42669554113724007422501216061341925731840/16356745075999619879454582003479248778787)*log (2381/800) +
  (-10171860499583562168530544984204899072/3870252578140107956192622055344363)*log (4508/2927) +
  (-2400004246990329338908198130480633272576/167861172709101151140958712418055048929)*log (4508/3981) +
  (-6155677056626368891786728296959751781121879838782533098252105992768/31882001125214926572581930244042659121940902285018356675015138523)

theorem endpointMass_eq_collectedMass : endpointMass = collectedMass := by
  have h0 : log (1327/800) = log (1327/200) - log (4/1) := by
    rw [← Real.log_div (by norm_num : ((1327/200) : ℝ) ≠ 0) (by norm_num : ((4/1) : ℝ) ≠ 0)]
    norm_num
  have h1 : log (2381/800) = log (2381/600) - log (4/3) := by
    rw [← Real.log_div (by norm_num : ((2381/600) : ℝ) ≠ 0) (by norm_num : ((4/3) : ℝ) ≠ 0)]
    norm_num
  have h2 : log (4508/2927) = log (1127/150) - log (2927/600) := by
    rw [← Real.log_div (by norm_num : ((1127/150) : ℝ) ≠ 0) (by norm_num : ((2927/600) : ℝ) ≠ 0)]
    norm_num
  have h3 : log (4508/3981) = log (1127/50) - log (3981/200) := by
    rw [← Real.log_div (by norm_num : ((1127/50) : ℝ) ≠ 0) (by norm_num : ((3981/200) : ℝ) ≠ 0)]
    norm_num
  unfold endpointMass fixedPrimitive primitive0 primitive1 primitive2 primitive3 primitive4 polePrimitive collectedMass
  rw [h0,h1,h2,h3]
  norm_num
  ring

theorem cLowerMass_eq_collectedMass : cLowerMass (1327/200) = collectedMass :=
  cLowerMass_eq_endpointMass.trans endpointMass_eq_collectedMass

/-- The first unpaid scalar after complete exact FTC. No sign is claimed. -/
def publicationResidual : ℝ :=
  (14900897:ℝ)/8000000 - log (1127/200) - collectedMass - E (1327/200)

theorem publicationResidual_eq_gap :
    8*publicationResidual = (14900897:ℝ)/1000000-endpointFirst := by
  rw [publicationResidual,endpointFirst,endpointMass_eq_collectedMass]
  ring

theorem publication_payment_iff_residual_nonpos :
    (14900897:ℝ)/8000000-log (1127/200) ≤ cLowerMass (1327/200)+E (1327/200) ↔
      publicationResidual ≤ 0 := by
  rw [cLowerMass_eq_collectedMass,publicationResidual]
  constructor <;> intro h <;> linarith only [h]

end FirstCRationalPayment
