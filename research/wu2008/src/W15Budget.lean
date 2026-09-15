import W15HighB
import PsiG18Strength

namespace WuTarget.W15
open Real QuarterTrim Wu2008DoubleSieve
noncomputable section

def psiFloor : ℝ :=
  (3629895479136046171/1363514967405501300000) *
    ((HighSix.right-HighSix.left)/(HighSix.left*(1/2-HighSix.left)))

def independentFloor : ℝ := 4*psiFloor + 4*(285/1000000) + highFloor

theorem rawPsi_lower : psiFloor ≤ Phase20.rawPsi := by
  have h := mul_le_mul HighSixPhase5.psi_lower PsiG18Strength.prime_integral_bounds.1
    (by norm_num [HighSix.left,HighSix.right]) HighSixPhase5.psi_positive.le
  simpa only [psiFloor, Phase20.rawPsi, HighSix.s, HighSix.S] using h

theorem g18_lower : (285/1000000 : ℝ) < Phase18.g18 :=
  PsiG18Strength.g18_bounds.1

theorem psiFloor_exact :
    psiFloor = (4816871300813533268917/14304635523051114138300000 : ℝ) := by
  norm_num [psiFloor, HighSix.left, HighSix.right]

theorem highFloor_exact : highFloor = (4403217/699329000000 : ℝ) := by
  norm_num [highFloor, highDensityFloor, alpha]

theorem highGain_rational : (4403217/699329000000 : ℝ) ≤ HighConsumer.highGain := by
  rw [← highFloor_exact]
  exact highGain_lower

theorem independentFloor_exact :
    independentFloor =
      (14671443843245999147312340283/5884497915117536823072471000000 : ℝ) := by
  norm_num [independentFloor, psiFloor_exact, highFloor_exact]

theorem independentFloor_rounded : (2493/1000000 : ℝ) < independentFloor := by
  rw [independentFloor_exact]
  norm_num

theorem independent_lower :
    independentFloor < 4*Phase20.rawPsi + 4*Phase18.g18 + HighConsumer.highGain := by
  unfold independentFloor
  linarith only [rawPsi_lower, g18_lower, highGain_lower]

theorem independent_rational :
    (2493/1000000 : ℝ) < 4*Phase20.rawPsi + 4*Phase18.g18 + HighConsumer.highGain :=
  independentFloor_rounded.trans independent_lower

theorem independent_fixed_delta_lower {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100) :
    independentFloor - 4*Phase18.B18*δ <
      4*Phase20.rawPsi + SingleUpperHIntegral.gainH34 δ + HighConsumer.highGain := by
  have h := Phase18.gain18_linear_error hδ hδhi
  linarith only [independent_lower, h]

theorem high_profile_fixed_delta {δ x y : ℝ} (hδ : 0 ≤ δ)
    (hr : truncatedSixthLowerRegion δ x y) (hh : (x,y) ∈ Wu08G6High.highDomain) :
    log (u x y-1) + 546/(1327*20000) - δ/alpha ≤
      log (truncatedSixthLowerS δ x y-1) +
        PositiveH.lowerCorrection (truncatedSixthLowerS δ x y) := by
  linarith only [high_correction_lower hh, HighConsumer.original_profile_delta_debit hδ hr]

end
end WuTarget.W15
