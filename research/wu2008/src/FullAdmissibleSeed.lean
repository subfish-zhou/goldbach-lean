import JointHMotherPayment
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalSmallDelta

namespace Wu2008DoubleSieve.FullAdmissibleSeed
open Real Set MeasureTheory
open scoped Classical
noncomputable section

/-- Complete available affine seed, including its zero extension above 7/2. -/
def seed (s : ℝ) : ℝ := max 0 ((7/2-s)/750)

/-- The moving seed uses the actual mask and the actual three-factor denominator. -/
def movingKernel (δ : ℝ) (v : ℝ × ℝ) : ℝ :=
  if truncatedSixthLowerAdmissibleRegion δ v.1 v.2 then
    seed (truncatedSixthLowerS δ v.1 v.2) /
      (v.1*v.2*(truncatedSixthLowerC δ-v.1-v.2)) else 0

/-- A uniform payment kernel. Only the existing seed endpoint d controls the mask;
no extra integration cuts or prime windows are introduced. -/
def uniformKernel (d : ℝ) (v : ℝ × ℝ) : ℝ :=
  if truncatedSixthLowerAdmissibleRegion d v.1 v.2 then
    seed (truncatedSixthLowerS 0 v.1 v.2) /
      (v.1*v.2*(truncatedSixthLowerC 0-v.1-v.2)) else 0

def Gamma (d : ℝ) : ℝ := 4 * ∫ v : ℝ × ℝ, uniformKernel d v

def Gamma6 : ℝ := Gamma (1/1000)

theorem seed_nonneg (s : ℝ) : 0 ≤ seed s := le_max_left _ _

theorem seed_antitone : Antitone seed := by
  intro s t h
  exact max_le_max le_rfl (by linarith)

theorem seed_lower {δ s : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/1000)
    (hs : 2 ≤ s) (hsHi : s ≤ 5) :
    seed s ≤ wuImprovementLimit false δ s := by
  apply max_le
  · exact wuImprovementLimit_nonneg false hδ (by linarith) (by linarith) (by linarith)
  · by_cases h : s < 7/2
    · exact (SecondFunctionalSmallDelta.h_strict hδ hδhi hs h).le
    · have hn := wuImprovementLimit_nonneg false hδ (by linarith)
        (show 1 ≤ s by linarith) (show s ≤ 10 by linarith)
      linarith

theorem region_mono {δ d x y : ℝ} (h : δ ≤ d)
    (hv : truncatedSixthLowerAdmissibleRegion d x y) :
    truncatedSixthLowerAdmissibleRegion δ x y := by
  rcases hv with ⟨⟨ha,hb,hc,he,hf⟩,hg⟩
  refine ⟨⟨ha,hb,hc,he,?_⟩,?_⟩ <;>
    unfold truncatedSixthLowerC at * <;> linarith

theorem denominator_pos {δ x y : ℝ} (hδ : 0 ≤ δ)
    (hv : truncatedSixthLowerAdmissibleRegion δ x y) :
    0 < x*y*(truncatedSixthLowerC δ-x-y) := by
  have hb := truncatedSixthLower_region_bounds hδ hv.1
  have ha := truncatedSixthLower_parameters.1
  exact mul_pos (mul_pos hb.1 hb.2.1) (by linarith [hb.2.2.1])

theorem moving_nonneg {δ : ℝ} (hδ : 0 ≤ δ) (v : ℝ × ℝ) :
    0 ≤ movingKernel δ v := by
  unfold movingKernel
  split_ifs with hv
  · exact div_nonneg (seed_nonneg _) (denominator_pos hδ hv).le
  · exact le_rfl

theorem moving_lower {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/1000)
    (v : ℝ × ℝ) : movingKernel δ v ≤ truncatedSixthMassHKernel δ v := by
  unfold movingKernel truncatedSixthMassHKernel
  split_ifs with hv
  · have hb := truncatedSixthLower_region_bounds hδ.le hv.1
    exact div_le_div_of_nonneg_right (seed_lower hδ hδhi hb.2.2.2.1 hb.2.2.2.2)
      (denominator_pos hδ.le hv).le
  · exact le_rfl

theorem uniform_nonneg {d : ℝ} (hd : 0 ≤ d) (v : ℝ × ℝ) :
    0 ≤ uniformKernel d v := by
  unfold uniformKernel
  split_ifs with hv
  · exact div_nonneg (seed_nonneg _) (denominator_pos le_rfl (region_mono hd hv)).le
  · exact le_rfl

theorem uniform_le_moving {δ d : ℝ} (hδ : 0 ≤ δ) (hδd : δ ≤ d)
    (v : ℝ × ℝ) : uniformKernel d v ≤ movingKernel δ v := by
  by_cases hv : truncatedSixthLowerAdmissibleRegion d v.1 v.2
  · have hvδ := region_mono hδd hv
    have hv0 := region_mono hδ hvδ
    rw [uniformKernel, if_pos hv, movingKernel, if_pos hvδ]
    have hb := truncatedSixthLower_region_bounds hδ hvδ.1
    have hs : truncatedSixthLowerS δ v.1 v.2 ≤ truncatedSixthLowerS 0 v.1 v.2 := by
      unfold truncatedSixthLowerS truncatedSixthLowerC
      exact div_le_div_of_nonneg_right (by linarith) truncatedSixthLower_parameters.1.le
    have hz : v.1*v.2*(truncatedSixthLowerC δ-v.1-v.2) ≤
        v.1*v.2*(truncatedSixthLowerC 0-v.1-v.2) := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hb.1.le hb.2.1.le)
      unfold truncatedSixthLowerC
      linarith
    exact div_le_div₀ (seed_nonneg _) (seed_antitone hs) (denominator_pos hδ hvδ) hz
  · rw [uniformKernel, if_neg hv]
    exact moving_nonneg hδ v

theorem moving_measurable (δ : ℝ) : Measurable (movingKernel δ) := by
  have hs : Measurable (fun v : ℝ × ℝ => seed (truncatedSixthLowerS δ v.1 v.2)) := by
    unfold seed truncatedSixthLowerS
    fun_prop
  have hd : Measurable (fun v : ℝ × ℝ => v.1*v.2*(truncatedSixthLowerC δ-v.1-v.2)) := by fun_prop
  exact (hs.div hd).ite (truncatedSixthMass_regions_measurable δ).2 measurable_const

theorem uniform_measurable (d : ℝ) : Measurable (uniformKernel d) := by
  have hs : Measurable (fun v : ℝ × ℝ => seed (truncatedSixthLowerS 0 v.1 v.2)) := by
    unfold seed truncatedSixthLowerS
    fun_prop
  have hd : Measurable (fun v : ℝ × ℝ => v.1*v.2*(truncatedSixthLowerC 0-v.1-v.2)) := by fun_prop
  exact (hs.div hd).ite (truncatedSixthMass_regions_measurable d).2 measurable_const

theorem moving_integrable {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/1000) :
    Integrable (movingKernel δ) := by
  apply ((truncatedSixthMass_kernels_integrable hδ (by linarith)).2).mono'
    (moving_measurable δ).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun v => by
    rw [Real.norm_eq_abs, abs_of_nonneg (moving_nonneg hδ.le v)]
    exact moving_lower hδ hδhi v)

theorem uniform_integrable {d : ℝ} (hd : 0 < d) (hdhi : d ≤ 1/1000) :
    Integrable (uniformKernel d) := by
  apply (moving_integrable hd hdhi).mono' (uniform_measurable d).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun v => by
    rw [Real.norm_eq_abs, abs_of_nonneg (uniform_nonneg hd.le v)]
    exact uniform_le_moving hd.le le_rfl v)

/-- Full moving affine-seed payment, with no discarded subrectangle complement. -/
theorem full_moving_payment {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/1000) :
    4 * (∫ v : ℝ × ℝ, movingKernel δ v) ≤ truncatedSixthLowerHadmdelta δ := by
  rw [(truncatedSixthMass_literal_integrals hδ (by linarith)).2]
  exact mul_le_mul_of_nonneg_left (integral_mono (moving_integrable hδ hδhi)
    (truncatedSixthMass_kernels_integrable hδ (by linarith)).2 (moving_lower hδ hδhi)) (by norm_num)

/-- Uniform in every positive delta below d; only the explicit seed kernel is frozen. -/
theorem uniform_payment {δ d : ℝ} (hδ : 0 < δ) (hδd : δ ≤ d) (hdhi : d ≤ 1/1000) :
    Gamma d ≤ truncatedSixthLowerHadmdelta δ := by
  have hd : 0 < d := hδ.trans_le hδd
  have hδhi := hδd.trans hdhi
  exact (mul_le_mul_of_nonneg_left (integral_mono (uniform_integrable hd hdhi)
    (moving_integrable hδ hδhi) (uniform_le_moving hδ.le hδd))
    (by norm_num : (0 : ℝ) ≤ 4)).trans (full_moving_payment hδ hδhi)

theorem gamma6_payment {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/1000) :
    Gamma6 ≤ truncatedSixthLowerHadmdelta δ := uniform_payment hδ hδhi le_rfl

/-- The original kept-count producer, retaining all small-delta quantifiers. -/
theorem uniform_actual_lower {ε d : ℝ} (hε : 0 < ε) (hd : 0 < d) (hdhi : d ≤ 1/1000) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ d ∧
      ∀ δ : ℝ, 0 < δ → δ < δ0 →
        ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
          (truncatedSixthLowerF6lin + Gamma d - ε)*wuSingularSeries N*N/log N^(2 : ℕ) ≤
          (truncatedSixthMass N ((N : ℝ)^truncatedSixthLowerAlpha)
            ((N : ℝ)^truncatedSixthLowerBeta) ((N : ℝ)^truncatedSixthLowerSigma)
            ((N : ℝ)^truncatedSixthLowerLambda) : ℝ) := by
  obtain ⟨a,ha,_,hc⟩ := truncatedSixthZeroDelta_actual_lower hε
  refine ⟨min a d,lt_min ha hd,min_le_right _ _,?_⟩
  intro δ hδ hδsmall
  obtain ⟨T,hT,ht⟩ := hc δ hδ (hδsmall.trans_le (min_le_left _ _))
  refine ⟨T,hT,?_⟩
  intro N hN he
  have hg := uniform_payment hδ (hδsmall.le.trans (min_le_right _ _)) hdhi
  have hm := mul_le_mul_of_nonneg_right
    (show truncatedSixthLowerF6lin+Gamma d-ε ≤ truncatedSixthLowerF6lin+truncatedSixthLowerHadmdelta δ-ε by linarith)
    (truncatedSixthClosure_scale_nonneg (hT.trans hN))
  have hm' : (truncatedSixthLowerF6lin+Gamma d-ε)*wuSingularSeries N*N/log N^(2 : ℕ) ≤
      (truncatedSixthLowerF6lin+truncatedSixthLowerHadmdelta δ-ε)*wuSingularSeries N*N/log N^(2 : ℕ) := by
    simpa only [truncatedSixthMassScale, mul_div_assoc, mul_assoc] using hm
  exact hm'.trans (ht N hN he)

theorem actual_count_lower {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (truncatedSixthLowerF6lin+Gamma6-ε)*wuSingularSeries N*N/log N^(2 : ℕ) ≤
      (truncatedSixthMass N ((N : ℝ)^truncatedSixthLowerAlpha)
        ((N : ℝ)^truncatedSixthLowerBeta) ((N : ℝ)^truncatedSixthLowerSigma)
        ((N : ℝ)^truncatedSixthLowerLambda) : ℝ) := by
  obtain ⟨d,hd,_,hc⟩ := uniform_actual_lower (d := 1/1000) hε (by norm_num) le_rfl
  exact hc (d/2) (half_pos hd) (half_lt_self hd)

end
end Wu2008DoubleSieve.FullAdmissibleSeed
