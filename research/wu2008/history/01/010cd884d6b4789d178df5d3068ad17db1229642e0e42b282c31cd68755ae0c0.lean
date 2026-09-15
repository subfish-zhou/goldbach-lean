import W06SigmaV2
import CoupledEndpointLog

noncomputable section
namespace WuTarget.W06
open Real Set MeasureTheory Wu2008DoubleSieve NodeExtension ActualNineFeedback
open CoupledIntegralRecovery
open scoped Interval BigOperators

def eCoefficient (S : ℝ) : ℝ := log (4/(S-1))
def jCoefficient (s S : ℝ) : ℝ := log ((S-1)/(s-1))

def eRemainder (z : Fin 9 → ℝ) (S : ℝ) : ℝ :=
  ∫ t in (S-2)..3, nineProfile z t/t * log ((t+1)/(S-1))

def jRemainder (z : Fin 9 → ℝ) (s S : ℝ) : ℝ :=
  (∫ t in (S-2)..3, nineProfile z t/t) * jCoefficient s S +
    ∫ t in (jStart s S)..(S-1),
      nineProfile z (t-1)/(t-1) * odds S (jStart s S) t

theorem eCoefficient_nonneg {S : ℝ} (hS : 3 ≤ S) (hS5 : S ≤ 5) :
    0 ≤ eCoefficient S :=
  log_nonneg ((one_le_div (by linarith : 0 < S-1)).mpr (by linarith))

theorem eCoefficient_pos {S : ℝ} (hS : 3 ≤ S) (hS5 : S < 5) :
    0 < eCoefficient S :=
  log_pos ((one_lt_div (by linarith : 0 < S-1)).mpr (by linarith))

theorem jCoefficient_nonneg {s S : ℝ} (hs : 2 ≤ s) (hsS : s ≤ S) :
    0 ≤ jCoefficient s S :=
  log_nonneg ((one_le_div (by linarith : 0 < s-1)).mpr (by linarith))

theorem jCoefficient_pos {s S : ℝ} (hs : 2 ≤ s) (hsS : s < S) :
    0 < jCoefficient s S :=
  log_pos ((one_lt_div (by linarith : 0 < s-1)).mpr (by linarith))

theorem eRemainder_nonneg {z : Fin 9 → ℝ} (hz : ∀ k, 0 ≤ z k)
    {S : ℝ} (hS : 3 ≤ S) (hS5 : S ≤ 5) : 0 ≤ eRemainder z S := by
  apply intervalIntegral.integral_nonneg (by linarith : S-2 ≤ 3)
  intro t ht
  apply mul_nonneg (div_nonneg (nineProfile_nonneg hz t) (by linarith [ht.1]))
  exact log_nonneg ((one_le_div (by linarith : 0 < S-1)).mpr (by linarith [ht.1]))

theorem jRemainder_nonneg {z : Fin 9 → ℝ} (hz : ∀ k, 0 ≤ z k)
    {s S : ℝ} (hs : 2 ≤ s) (hS : 3 ≤ S) (hS5 : S ≤ 5)
    (hsS : s ≤ S) (hr : 2 ≤ S-S/s) : 0 ≤ jRemainder z s S := by
  have hstart : 2 ≤ jStart s S := hr
  have hend : jStart s S ≤ S-1 := by
    have h := (one_le_div (by linarith : 0 < s)).mpr hsS
    unfold jStart
    linarith only [h]
  apply add_nonneg
  · apply mul_nonneg _ (jCoefficient_nonneg hs hsS)
    apply intervalIntegral.integral_nonneg (by linarith : S-2 ≤ 3)
    intro t ht
    exact div_nonneg (nineProfile_nonneg hz t) (by linarith [ht.1])
  · apply intervalIntegral.integral_nonneg hend
    intro t ht
    exact mul_nonneg (div_nonneg (nineProfile_nonneg hz (t-1))
      (by linarith [ht.1]))
      (odds_nonneg (by linarith : 0 < jStart s S) ht.1 (by linarith [ht.2]))

theorem eProfile_split (z : Fin 9 → ℝ) (S : ℝ) :
    eProfile (nineProfile z) S =
      eCoefficient S * aProfile (nineProfile z) + eRemainder z S := by
  unfold eProfile eCoefficient eRemainder
  ring

theorem profileJ_split (z : Fin 9 → ℝ) {s S : ℝ}
    (hs : 2 ≤ s) (hS : 3 ≤ S) (hS5 : S ≤ 5)
    (hsS : s ≤ S) (hr : 2 ≤ S-S/s) :
    profileJ z s S = jCoefficient s S * aProfile (nineProfile z) +
      jRemainder z s S := by
  rw [profileJ_original_log z hs hS hS5 hsS hr, gProfile,
    show S-1-1 = S-2 by ring]
  unfold jCoefficient jRemainder
  ring

theorem eProfile_sigma_lower {z : Fin 9 → ℝ} (hz : ∀ k, 0 ≤ z k)
    {S : ℝ} (hS : 3 ≤ S) (hS5 : S ≤ 5) :
    eCoefficient S * sigmaLower z + eRemainder z S ≤ eProfile (nineProfile z) S := by
  rw [eProfile_split]
  exact add_le_add_right
    (mul_le_mul_of_nonneg_left (sigmaLower_le_aProfile hz) (eCoefficient_nonneg hS hS5)) _

theorem profileJ_sigma_lower {z : Fin 9 → ℝ} (hz : ∀ k, 0 ≤ z k)
    {s S : ℝ} (hs : 2 ≤ s) (hS : 3 ≤ S) (hS5 : S ≤ 5)
    (hsS : s ≤ S) (hr : 2 ≤ S-S/s) :
    jCoefficient s S * sigmaLower z + jRemainder z s S ≤ profileJ z s S := by
  rw [profileJ_split z hs hS hS5 hsS hr]
  exact add_le_add_right
    (mul_le_mul_of_nonneg_left (sigmaLower_le_aProfile hz) (jCoefficient_nonneg hs hsS)) _

def firstCoefficient (s S : ℝ) : ℝ := eCoefficient S + jCoefficient s S/2

def coupledCoefficient (p : SecondFunctionalParameters) : ℝ :=
  (4*eCoefficient p.S + eCoefficient p.kappa1 + jCoefficient p.s p.S +
    jCoefficient p.kappa2 p.S + jCoefficient p.kappa3 p.S)/5

def firstRemainder (z : Fin 9 → ℝ) (s S : ℝ) : ℝ :=
  eRemainder z S + jRemainder z s S/2

def coupledRemainder (p : SecondFunctionalParameters) (z : Fin 9 → ℝ) : ℝ :=
  (4*eRemainder z p.S + eRemainder z p.kappa1 + jRemainder z p.s p.S +
    jRemainder z p.kappa2 p.S + jRemainder z p.kappa3 p.S + densityMoment p z)/5

theorem firstCoefficient_nonneg {s S : ℝ}
    (hs : 2 ≤ s) (hS : 3 ≤ S) (hS5 : S ≤ 5) (hsS : s ≤ S) :
    0 ≤ firstCoefficient s S :=
  add_nonneg (eCoefficient_nonneg hS hS5)
    (div_nonneg (jCoefficient_nonneg hs hsS) (by norm_num))

theorem coupledCoefficient_nonneg {p : SecondFunctionalParameters} (hp : CoupledGeometry p) :
    0 ≤ coupledCoefficient p := by
  have hg := coupled_geometry_bounds hp
  have h0 := eCoefficient_nonneg hp.1.three_le_S hp.1.S_le_five
  have h1 := eCoefficient_nonneg hp.2.1 hg.2.2.2.2.2.2
  have hj0 := jCoefficient_nonneg hg.1 hg.2.1
  have hj2 := jCoefficient_nonneg hg.2.2.1 hg.2.2.2.1
  have hj3 := jCoefficient_nonneg hg.2.2.2.2.1 hg.2.2.2.2.2.1
  unfold coupledCoefficient
  positivity

theorem firstFeedback_split (z : Fin 9 → ℝ) {s S : ℝ}
    (hs : 2 ≤ s) (hS : 3 ≤ S) (hS5 : S ≤ 5)
    (hsS : s ≤ S) (hr : 2 ≤ S-S/s) :
    firstFeedback z s S = firstCoefficient s S * aProfile (nineProfile z) +
      firstRemainder z s S := by
  unfold firstFeedback
  rw [eProfile_split, profileJ_split z hs hS hS5 hsS hr]
  unfold firstCoefficient firstRemainder
  ring

theorem coupledFeedback_split {p : SecondFunctionalParameters} (hp : CoupledGeometry p)
    (z : Fin 9 → ℝ) :
    coupledFeedback p z = coupledCoefficient p * aProfile (nineProfile z) +
      coupledRemainder p z := by
  have hg := coupled_geometry_bounds hp
  unfold coupledFeedback
  rw [eProfile_split, eProfile_split,
    profileJ_split z hg.1 hp.1.three_le_S hp.1.S_le_five hg.2.1 hp.2.2.1,
    profileJ_split z hg.2.2.1 hp.1.three_le_S hp.1.S_le_five hg.2.2.2.1 hp.2.2.2.1,
    profileJ_split z hg.2.2.2.2.1 hp.1.three_le_S hp.1.S_le_five
      hg.2.2.2.2.2.1 hp.2.2.2.2]
  unfold coupledCoefficient coupledRemainder
  ring

theorem firstRemainder_nonneg {z : Fin 9 → ℝ} (hz : ∀ k, 0 ≤ z k)
    {s S : ℝ} (hs : 2 ≤ s) (hS : 3 ≤ S) (hS5 : S ≤ 5)
    (hsS : s ≤ S) (hr : 2 ≤ S-S/s) : 0 ≤ firstRemainder z s S :=
  add_nonneg (eRemainder_nonneg hz hS hS5)
    (div_nonneg (jRemainder_nonneg hz hs hS hS5 hsS hr) (by norm_num))

theorem coupledRemainder_nonneg {p : SecondFunctionalParameters} (hp : CoupledGeometry p)
    {z : Fin 9 → ℝ} (hz : ∀ k, 0 ≤ z k) : 0 ≤ coupledRemainder p z := by
  have hg := coupled_geometry_bounds hp
  have h0 := eRemainder_nonneg hz hp.1.three_le_S hp.1.S_le_five
  have h1 := eRemainder_nonneg hz hp.2.1 hg.2.2.2.2.2.2
  have hj0 := jRemainder_nonneg hz hg.1 hp.1.three_le_S hp.1.S_le_five hg.2.1 hp.2.2.1
  have hj2 := jRemainder_nonneg hz hg.2.2.1 hp.1.three_le_S hp.1.S_le_five
    hg.2.2.2.1 hp.2.2.2.1
  have hj3 := jRemainder_nonneg hz hg.2.2.2.2.1 hp.1.three_le_S hp.1.S_le_five
    hg.2.2.2.2.2.1 hp.2.2.2.2
  have hd := densityMoment_nonneg p hp.1 hz
  unfold coupledRemainder
  positivity

theorem firstFeedback_sigma_lower {z : Fin 9 → ℝ} (hz : ∀ k, 0 ≤ z k)
    {s S : ℝ} (hs : 2 ≤ s) (hS : 3 ≤ S) (hS5 : S ≤ 5)
    (hsS : s ≤ S) (hr : 2 ≤ S-S/s) :
    firstCoefficient s S * sigmaLower z + firstRemainder z s S ≤ firstFeedback z s S := by
  rw [firstFeedback_split z hs hS hS5 hsS hr]
  exact add_le_add_right (mul_le_mul_of_nonneg_left (sigmaLower_le_aProfile hz)
    (firstCoefficient_nonneg hs hS hS5 hsS)) _

theorem coupledFeedback_sigma_lower {p : SecondFunctionalParameters} (hp : CoupledGeometry p)
    {z : Fin 9 → ℝ} (hz : ∀ k, 0 ≤ z k) :
    coupledCoefficient p * sigmaLower z + coupledRemainder p z ≤ coupledFeedback p z := by
  rw [coupledFeedback_split hp z]
  exact add_le_add_right (mul_le_mul_of_nonneg_left (sigmaLower_le_aProfile hz)
    (coupledCoefficient_nonneg hp)) _

end WuTarget.W06
