import Wu18938Campaign.M3.Confirmed.LogIntegral
import Wu18938Campaign.M3.Confirmed.ActualAssembly

noncomputable section

namespace Wu18938Campaign.M3.Confirmed.SeventhNinth

open Real Set MeasureTheory Wu2008DoubleSieve LogMoments Wu08TerminalAlignment

def seventhCap : ℝ :=
  endpointBound 8 1 (coordinate 1 3 SeventhEighth.sigma) 0
    (coordinate 1 3 SeventhEighth.sigma)
    (logUpper 24 (1/(1-coordinate 1 3 SeventhEighth.sigma)))

theorem seventh_integral_upper : SeventhEighth.J7 ≤ seventhCap := by
  have h := transformed_integral_upper 8
    (d := 1) (e := 3) (l := SeventhEighth.sigma) (r := 1/3)
    (by norm_num [SeventhEighth.sigma, SeventhEighth.alpha])
    (by norm_num [SeventhEighth.sigma, SeventhEighth.alpha])
    (by norm_num) (by norm_num) (by norm_num [coordinate])
    (by norm_num [coordinate, SeventhEighth.sigma, SeventhEighth.alpha])
  have he : (∫ t in SeventhEighth.sigma..(1/3:ℝ), transformedKernel 1 3 t) =
      SeventhEighth.J7 := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le SeventhEighth.classical_parameters.2.2.le] at ht
    have ht0 : 0 < t := (SeventhEighth.classical_parameters.1.trans
      SeventhEighth.classical_parameters.2.1).trans_le ht.1
    have ht1 : 1-t ≠ 0 := by linarith [ht.2]
    unfold transformedKernel coordinate
    congr 2
    have hd : (1:ℝ)-(1-3*t)/(1-t) = 2*t/(1-t) := by
      field_simp
      ring
    rw [hd]
    field_simp [ht0.ne',ht1]
    ring
  rw [he, show coordinate 1 3 (1/3) = 0 by norm_num [coordinate]] at h
  apply h.trans
  apply endpoint_bound 8 (by norm_num)
    (by norm_num [coordinate, SeventhEighth.sigma, SeventhEighth.alpha])
    (by norm_num [coordinate, SeventhEighth.sigma, SeventhEighth.alpha])
    (by norm_num) (by norm_num [coordinate, SeventhEighth.sigma, SeventhEighth.alpha])
  simpa only [sub_zero] using log_upper
    (by norm_num [coordinate, SeventhEighth.sigma, SeventhEighth.alpha] :
      (1:ℝ) ≤ 1/(1-coordinate 1 3 SeventhEighth.sigma)) 24

theorem seventh_main_upper : seventhMain ≤ (585179/1000000:ℝ) := by
  have h := seventh_integral_upper
  have hc : 8*seventhCap ≤ (585179/1000000:ℝ) := by
    norm_num [seventhCap, endpointBound, momentBound, logUpper,
      coordinate, SeventhEighth.sigma, SeventhEighth.alpha, Finset.sum_range_succ]
  unfold seventhMain
  linarith only [h,hc]

def ninthD : ℝ := 1-2*SeventhEighth.sigma
def ninthLeft : ℝ := coordinate ninthD 1 SeventhEighth.sigma
def ninthRight : ℝ := coordinate ninthD 1 ninthProfileK2
def ninthCap : ℝ :=
  endpointBound 10 ninthD ninthRight ninthLeft ninthRight
    (logUpper 24 ((ninthD-ninthLeft)/(ninthD-ninthRight)))

theorem ninth_integral_upper : J9 ≤ ninthCap := by
  have h := transformed_integral_upper 10
    (d := ninthD) (e := 1) (l := ninthProfileK2) (r := SeventhEighth.sigma)
    (by norm_num [ninthProfileK2])
    (by norm_num [ninthProfileK2, SeventhEighth.sigma, SeventhEighth.alpha])
    (by norm_num [SeventhEighth.sigma, SeventhEighth.alpha])
    (by norm_num [ninthD, SeventhEighth.sigma, SeventhEighth.alpha])
    (by norm_num [coordinate, ninthD, SeventhEighth.sigma, SeventhEighth.alpha])
    (by norm_num [coordinate, ninthD, ninthProfileK2, SeventhEighth.sigma, SeventhEighth.alpha])
  have he : (∫ t in ninthProfileK2..SeventhEighth.sigma, transformedKernel ninthD 1 t) =
      J9 := by
    apply intervalIntegral.integral_congr
    intro t ht
    have hbs : ninthProfileK2 ≤ SeventhEighth.sigma := by
      norm_num [ninthProfileK2, SeventhEighth.sigma, SeventhEighth.alpha]
    rw [uIcc_of_le hbs] at ht
    have ht1 : 1-t ≠ 0 := by
      have hr : SeventhEighth.sigma < 1 := by norm_num [SeventhEighth.sigma, SeventhEighth.alpha]
      linarith [ht.2]
    have hs : SeventhEighth.sigma ≠ 0 := by norm_num [SeventhEighth.sigma, SeventhEighth.alpha]
    change transformedKernel ninthD 1 t =
      log ((1-SeventhEighth.sigma-t)/SeventhEighth.sigma)/(t*(1-t))
    unfold transformedKernel coordinate ninthD
    congr 2
    field_simp [hs,ht1]
    ring
  rw [he] at h
  apply h.trans
  apply endpoint_bound 10
    (by norm_num [ninthD, SeventhEighth.sigma, SeventhEighth.alpha])
    (by norm_num [ninthRight, coordinate, ninthD, ninthProfileK2, SeventhEighth.sigma, SeventhEighth.alpha])
    (by norm_num [ninthRight, coordinate, ninthD, ninthProfileK2, SeventhEighth.sigma, SeventhEighth.alpha])
    (by norm_num [ninthLeft, coordinate, ninthD, SeventhEighth.sigma, SeventhEighth.alpha])
    (by norm_num [ninthRight, coordinate, ninthD, ninthProfileK2, SeventhEighth.sigma, SeventhEighth.alpha])
  exact log_upper (by
    norm_num [ninthLeft, ninthRight, coordinate, ninthD, ninthProfileK2,
      SeventhEighth.sigma, SeventhEighth.alpha]) 24

theorem ninth_main_upper : ninthMain ≤ (5372410/1000000:ℝ) := by
  have h := ninth_integral_upper
  have hc : 8*ninthCap ≤ (5372410/1000000:ℝ) := by
    norm_num [ninthCap, endpointBound, momentBound, logUpper, ninthD, ninthLeft, ninthRight,
      coordinate, ninthProfileK2, SeventhEighth.sigma, SeventhEighth.alpha, Finset.sum_range_succ]
  unfold ninthMain
  linarith only [h,hc]

end Wu18938Campaign.M3.Confirmed.SeventhNinth
