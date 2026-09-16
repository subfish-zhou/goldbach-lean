import Wu18938Campaign.M1.Confirmed.ProfileKernelIdentity
import FeedbackSystem

noncomputable section

namespace Wu18938Campaign.M1.Confirmed.FiniteProfile

open Wu2008DoubleSieve Rebox Real MeasureTheory NodeExtension MotherPair
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne
open scoped Classical Interval

def lowerGainJ (H : ℝ → ℝ) (s t : ℝ) : ℝ :=
  ∫ u in (1 - 1 / s)..(1 - 1 / t), gProfile H (t * u) / (u * (1 - u))

theorem gProfile_continuous {H : ℝ → ℝ} (hH : Antitone H) :
    ContinuousOn (gProfile H) (Set.Icc 2 4) := by
  have hi := profile_div_integrable hH.intervalIntegrable
  have hc := intervalIntegral.continuousOn_primitive_interval_left
    ((intervalIntegrable_iff' (by finiteness)).mp hi)
  have hcomp : ContinuousOn (fun u => ∫ t in (u - 1)..3, H t / t) (Set.Icc 2 4) := by
    apply hc.comp (continuousOn_id.sub continuousOn_const)
    intro u hu
    rw [Set.uIcc_of_le (by norm_num : (1 : ℝ) ≤ 3)]
    change 1 ≤ u - 1 ∧ u - 1 ≤ 3
    exact ⟨by linarith [hu.1],by linarith [hu.2]⟩
  exact continuousOn_const.add hcomp

theorem lowerGainJ_integrable {H : ℝ → ℝ} (hH : Antitone H)
    {s t : ℝ} (hs : 2 ≤ s) (hst : s ≤ t) (ht : 3 ≤ t) (ht5 : t ≤ 5)
    (hr : 2 ≤ t - t / s) :
    IntervalIntegrable (fun u => gProfile H (t * u) / (u * (1 - u)))
      volume (1 - 1 / s) (1 - 1 / t) := by
  have hg := ActualNineFeedback.J_geometry hs ht ht5 hst hr
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le hg.1]
  apply ContinuousOn.div
  · exact (gProfile_continuous hH).comp (continuousOn_const.mul continuousOn_id)
      (fun u hu => (hg.2 u hu).2.2)
  · exact continuousOn_id.mul (continuousOn_const.sub continuousOn_id)
  · intro u hu
    exact ne_of_gt (mul_pos (hg.2 u hu).1 (by linarith [(hg.2 u hu).2.1]))

theorem lower_profile_J_split {H : ℝ → ℝ} (hH : Antitone H)
    {s t : ℝ} (hs : 2 < s) (hst : s ≤ t) (ht : 3 ≤ t) (ht5 : t ≤ 5)
    (hr : 2 ≤ t - t / s) :
    profileJ (lowerExtension H (aProfile H)) s t =
      fourthRowClassicalJ s t + lowerGainJ H s t := by
  have hg := ActualNineFeedback.J_geometry hs.le ht ht5 hst hr
  have hl : IntervalIntegrable (fun u => log (t * u - 1) / (u * (1 - u)))
      volume (1 - 1 / s) (1 - 1 / t) := fourthRowClassical_J_integrable hst hs
  have hh := lowerGainJ_integrable hH hs.le hst ht ht5 hr
  unfold profileJ lowerGainJ fourthRowClassicalJ
  rw [← intervalIntegral.integral_add hl hh]
  apply intervalIntegral.integral_congr
  intro u hu
  rw [Set.uIcc_of_le hg.1] at hu
  have hv := (hg.2 u hu).2.2
  dsimp only
  rw [lowerExtension_eq hH hv.1 hv.2]
  have ha : wuLowerCoefficient (t * u) = log (t * u - 1) :=
    jr1965f_normalized_firstInterval hv.1 hv.2
  rw [ha]
  unfold gProfile
  ring

theorem upper_profile_E {H : ℝ → ℝ} (hH : Antitone H)
    {v : ℝ} (hv : 3 ≤ v) (hv5 : v ≤ 5) :
    upperExtension H (aProfile H) v = wuUpperCoefficient v - eProfile H v :=
  upperExtension_eq hH hv hv5

def feedbackDensityMoment (p : SecondFunctionalParameters) (H : ℝ → ℝ) : ℝ :=
  ∫ v in (1 : ℝ)..3, H v * SecondFunctionalCoupledFeedback.density p v

theorem classical_pair_identity (p : SecondFunctionalParameters) (j : Term) :
    Pair.classicalIntegral p j = MotherPair.classicalIntegral p j := by
  cases j <;> rfl

theorem classical_pair_sum (p : SecondFunctionalParameters) :
    (∑ j : Term, Pair.classicalIntegral p j) = SecondFunctionalCoupledFeedback.classical p := by
  simp_rw [classical_pair_identity]
  rw [show (Finset.univ : Finset Term) =
      {Term.gammaFive,Term.gammaSix,Term.gammaSeven,Term.gammaEight} by ext j; cases j <;> simp]
  simp only [Finset.sum_insert (by decide : Term.gammaFive ∉
      {Term.gammaSix,Term.gammaSeven,Term.gammaEight}),
    Finset.sum_insert (by decide : Term.gammaSix ∉ {Term.gammaSeven,Term.gammaEight}),
    Finset.sum_insert (by decide : Term.gammaSeven ∉ {Term.gammaEight}),Finset.sum_singleton]
  unfold SecondFunctionalCoupledFeedback.classical
  ring

theorem first_gain_source_identity {H : ℝ → ℝ} (hH : Antitone H)
    {δ s t : ℝ} (hs : 2 < s) (hs3 : s ≤ 3) (ht : 3 ≤ t) (ht5 : t ≤ 5)
    (hr : 2 ≤ t - t / s) :
    firstGain δ s t H =
      firstFunctionalGainPsi δ s t + eProfile H t + lowerGainJ H s t / 2 := by
  have ha : wuUpperCoefficient s = 1 :=
    jr1965F_normalized_initial (by linarith) hs3
  unfold firstGain firstCoefficient firstFunctionalGainPsi
  rw [upper_profile_E hH ht ht5,lower_profile_J_split hH hs (hs3.trans ht) ht ht5 hr,ha]
  unfold fourthRowClassicalJ
  ring

theorem second_gain_source_identity {H : ℝ → ℝ} (hH : Antitone H) (hHb : ∀ v, |H v| ≤ 1)
    (p : SecondFunctionalParameters) (hp : ActualNineFeedback.CoupledGeometry p) (δ : ℝ)
    (hδ : δ < 1 / 2) :
    secondGain p δ H = ActualNineFeedback.coupledBase p -
      ActualNineFeedback.deltaLoss δ * ActualNineFeedback.coupledLoss p +
      (4 * eProfile H p.S + eProfile H p.kappa1 +
        lowerGainJ H p.s p.S + lowerGainJ H p.kappa2 p.S + lowerGainJ H p.kappa3 p.S +
        feedbackDensityMoment p H) / 5 := by
  have hg := ActualNineFeedback.coupled_geometry_bounds hp
  have hJ0 := lower_profile_J_split hH hp.1.two_lt_s hg.2.1 hp.1.three_le_S hp.1.S_le_five hp.2.2.1
  have hJ2 := lower_profile_J_split hH
    (hp.1.two_lt_s.trans_le (hp.1.mother.s_le_kappa3.trans hp.1.mother.kappa3_lt_kappa2.le))
    hg.2.2.2.1 hp.1.three_le_S hp.1.S_le_five hp.2.2.2.1
  have hJ3 := lower_profile_J_split hH (hp.1.two_lt_s.trans_le hp.1.mother.s_le_kappa3)
    hg.2.2.2.2.2.1 hp.1.three_le_S hp.1.S_le_five hp.2.2.2.2
  have hG := ProfileGrid.four_profile_density hp.1 hH.measurable hHb
  have ha : wuUpperCoefficient p.s = 1 :=
    jr1965F_normalized_initial
      (by linarith [hp.1.two_lt_s]) hp.1.s_le_three
  unfold secondGain secondProfileCoefficient
  rw [upper_profile_E hH hp.1.three_le_S hp.1.S_le_five,
    upper_profile_E hH hp.2.1 hg.2.2.2.2.2.2,hJ0,hJ2,hJ3,
    Finset.sum_sub_distrib,classical_pair_sum,hG]
  unfold ActualNineFeedback.coupledBase ActualNineFeedback.coupledCostMass
    ActualNineFeedback.deltaLoss ActualNineFeedback.coupledLoss feedbackDensityMoment
  unfold ActualNineFeedback.coupledCostMass
  rw [ha]
  have hd : 1 - 2 * δ ≠ 0 := by linarith
  field_simp
  ring

end Wu18938Campaign.M1.Confirmed.FiniteProfile
