import CoupledJFlat

namespace CoupledIntegralRecovery
open Real Set MeasureTheory NodeExtension ActualNineFeedback Wu2008DoubleSieve
open scoped Interval
noncomputable section

/-- Only the already admitted fixed lower envelope, at the unchanged endpoints. -/
def oddsLower (S a x : ℝ) : ℝ :=
  Wu04FactorEnvelopes.lower (x/a)+Wu04FactorEnvelopes.lower ((S-a)/(S-x))

theorem oddsLower_le {S a x : ℝ} (ha : 0<a) (hax : a ≤ x) (hx : x<S) :
    oddsLower S a x ≤ odds S a x := by
  apply add_le_add
  · exact Wu04FactorEnvelopes.lower_le_log ((one_le_div ha).mpr hax)
  · exact Wu04FactorEnvelopes.lower_le_log
      ((one_le_div (by linarith : 0<S-x)).mpr (by linarith))

theorem oddsLower_continuous {S a b : ℝ} (ha : 0<a) (hab : a ≤ b) (hb : b<S) :
    ContinuousOn (oddsLower S a) (uIcc a b) := by
  rw [uIcc_of_le hab]
  intro x hx
  apply ContinuousAt.continuousWithinAt
  unfold oddsLower
  apply ContinuousAt.add
  · exact (Wu04FactorEnvelopes.lower_continuous (x := x/a) (div_pos (by linarith [hx.1]) ha)).comp (f := fun y : ℝ => y/a)
      (continuousAt_id.div_const a)
  · exact (Wu04FactorEnvelopes.lower_continuous (x := (S-a)/(S-x))
      (div_pos (by linarith) (by linarith [hx.2]))).comp (f := fun y : ℝ => (S-a)/(S-y))
      (continuousAt_const.div (continuousAt_const.sub continuousAt_id) (by linarith [hx.2]))

/-- The full J lower integral retains the entire original nine-profile and terminal tail. -/
def jLower (z : Fin 9 → ℝ) (s S : ℝ) : ℝ :=
  gProfile (nineProfile z) (S-1)*oddsLower S (jStart s S) (S-1) +
    ∫ t in (jStart s S)..(S-1),
      nineProfile z (t-1)/(t-1)*oddsLower S (jStart s S) t

theorem jLower_le (z : Fin 9 → ℝ) (hz : ∀ k, 0 ≤ z k) {s S : ℝ}
    (hs : 2 ≤ s) (hS : 3 ≤ S) (hS5 : S ≤ 5) (hsS : s ≤ S) (hr : 2 ≤ S-S/s) :
    jLower z s S ≤ profileJ z s S := by
  have hstart : 2 ≤ jStart s S := hr
  have hend : jStart s S ≤ S-1 := by
    have hdiv : 1 ≤ S/s := (one_le_div (by linarith : 0<s)).mpr hsS
    unfold jStart
    linarith
  have ha : 0<jStart s S := by linarith
  have hb : S-1<S := by linarith
  have hp := shifted_profile_integrable z hstart hend (by linarith)
  have hl := oddsLower_continuous ha hend hb
  have ho : ContinuousOn (odds S (jStart s S)) (uIcc (jStart s S) (S-1)) := by
    rw [uIcc_of_le hend]
    intro t ht
    apply ContinuousAt.continuousWithinAt
    unfold odds
    apply ContinuousAt.add
    · exact ((continuousAt_id.div_const _).log
        (ne_of_gt (div_pos (by linarith [ht.1] : 0<t) ha)))
    · apply ContinuousAt.log
      · exact continuousAt_const.div (continuousAt_const.sub continuousAt_id) (by linarith [ht.2])
      · exact ne_of_gt (div_pos (by linarith) (by linarith [ht.2]))
  have hmono := intervalIntegral.integral_mono_on hend (hp.mul_continuousOn hl)
    (hp.mul_continuousOn ho) (fun t ht =>
      mul_le_mul_of_nonneg_left (oddsLower_le ha ht.1 (ht.2.trans_lt hb))
        (div_nonneg (nineProfile_nonneg hz (t-1)) (by linarith [ht.1])))
  have hg : 0 ≤ gProfile (nineProfile z) (S-1) :=
    (profiles_nonneg (fun t _ => nineProfile_nonneg hz t)).2.1 _ ⟨by linarith,by linarith⟩
  rw [profileJ_eq_flat z hs hS hS5 hsS hr]
  exact add_le_add (mul_le_mul_of_nonneg_left (oddsLower_le ha hend hb) hg) hmono

/-- The complete eProfile lower integral, with its genuine sigma-feedback coefficient retained. -/
def eLower (z : Fin 9 → ℝ) (v : ℝ) : ℝ :=
  aProfile (nineProfile z)*Wu04FactorEnvelopes.lower (4/(v-1)) +
    ∫ t in (v-2)..3, nineProfile z t/t * Wu04FactorEnvelopes.lower ((t+1)/(v-1))

theorem eLower_le (z : Fin 9 → ℝ) (hz : ∀ k, 0 ≤ z k) {v : ℝ}
    (hv : 3 ≤ v) (hv5 : v ≤ 5) : eLower z v ≤ eProfile (nineProfile z) v := by
  have hv0 : 0<v-1 := by linarith
  have hab : v-2 ≤ 3 := by linarith
  have hp := profile_subinterval (profile_div_integrable (nineProfile_integrable z))
    (by linarith : 1 ≤ v-2) hab
  have hl : ContinuousOn (fun t => Wu04FactorEnvelopes.lower ((t+1)/(v-1))) (uIcc (v-2) 3) := by
    rw [uIcc_of_le hab]
    intro t ht
    apply ContinuousAt.continuousWithinAt
    exact (Wu04FactorEnvelopes.lower_continuous (x := (t+1)/(v-1))
      (div_pos (by linarith [ht.1]) hv0)).comp (f := fun y : ℝ => (y+1)/(v-1))
      ((continuousAt_id.add_const 1).div_const _)
  have hm := intervalIntegral.integral_mono_on hab (hp.mul_continuousOn hl)
    (hp.mul_continuousOn (log_weight_continuous hv hv5)) (fun t ht =>
      mul_le_mul_of_nonneg_left
        (Wu04FactorEnvelopes.lower_le_log ((one_le_div hv0).mpr (by linarith [ht.1])))
        (div_nonneg (nineProfile_nonneg hz t) (by linarith [ht.1])))
  have ha : 0 ≤ aProfile (nineProfile z) :=
    (profiles_nonneg (fun t _ => nineProfile_nonneg hz t)).1
  exact add_le_add
    (mul_le_mul_of_nonneg_left
      (Wu04FactorEnvelopes.lower_le_log ((one_le_div hv0).mpr (by linarith))) ha) hm

/-- The unchanged six-term numerator, after genuine integral lower bounds, not matrix entries. -/
def coupledLower (p : SecondFunctionalParameters) (z : Fin 9 → ℝ) : ℝ :=
  (4*eLower z p.S+eLower z p.kappa1+jLower z p.s p.S+
    jLower z p.kappa2 p.S+jLower z p.kappa3 p.S+densityMoment p z)/5

theorem coupledLower_le (p : SecondFunctionalParameters) (hp : CoupledGeometry p)
    (z : Fin 9 → ℝ) (hz : ∀ k, 0 ≤ z k) : coupledLower p z ≤ coupledFeedback p z := by
  have hg := coupled_geometry_bounds hp
  have e0 := eLower_le z hz hp.1.three_le_S hp.1.S_le_five
  have e1 := eLower_le z hz hp.2.1 hg.2.2.2.2.2.2
  have j0 := jLower_le z hz hg.1 hp.1.three_le_S hp.1.S_le_five hg.2.1 hp.2.2.1
  have j2 := jLower_le z hz hg.2.2.1 hp.1.three_le_S hp.1.S_le_five hg.2.2.2.1 hp.2.2.2.1
  have j3 := jLower_le z hz hg.2.2.2.2.1 hp.1.three_le_S hp.1.S_le_five hg.2.2.2.2.2.1 hp.2.2.2.2
  unfold coupledLower coupledFeedback
  linarith only [e0,e1,j0,j2,j3]

theorem originalH_nonneg (k : Fin 9) : 0 ≤ NineFeedbackStrength.originalH k := by
  have h : ∀ k : Fin 9, 0 ≤ NineFeedbackStrength.originalH k := by
    simp only [NineFeedbackStrength.originalH, Fin.forall_fin_succ, Fin.forall_fin_zero,
      and_true, Matrix.cons_val_zero, Matrix.cons_val_succ]
    norm_num
  exact h k

/-- Unconditional weighted lower bound for all four original H rows, with no new numerical inputs. -/
theorem original_four_weighted_lower (i : Fin 4) :
    coupledLower (coupledRow i) NineFeedbackStrength.originalH ≤
      coupledFeedback (coupledRow i) NineFeedbackStrength.originalH :=
  coupledLower_le _ (coupledRow_geometry i) _ originalH_nonneg

end
end CoupledIntegralRecovery
