import Wu18938Campaign.M5.KernelCorner
import MathlibNt.Wu2008DoubleSieve.ImprovementMonotonicity

noncomputable section

namespace Wu18938Campaign.M5.OriginalAnalytic

open Real Set MeasureTheory Wu2008DoubleSieve
open Wu18938Campaign.M5.StrictCorner Wu18938Campaign.M5.KernelCorner
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne

def coefficient (δ s : ℝ) : ℝ :=
  wuLowerCoefficient (max 1 (min 5 s)) +
    wuImprovementLimit false δ (max 1 (min 5 s))

theorem coefficient_eq {δ s : ℝ} (hs : s ∈ Icc (1 : ℝ) 5) :
    coefficient δ s = wuLowerCoefficient s + wuImprovementLimit false δ s := by
  simp only [coefficient, min_eq_right hs.2, max_eq_right hs.1]

theorem coefficient_measurable {δ : ℝ} (hδ : 0 < δ) (hδhi : δ < 1 / 2) :
    Measurable (coefficient δ) := by
  have hm : Monotone (coefficient δ) := by
    intro s t hst
    apply wu_effective_lower_limit_mono hδ hδhi (le_max_left _ _)
      (max_le_max le_rfl (min_le_min le_rfl hst))
    exact (max_le (by norm_num) (min_le_left _ _)).trans (by norm_num)
  exact hm.measurable

theorem coefficient_bound {δ : ℝ} (hδ : 0 < δ) (hδhi : δ < 1 / 2)
    (s : ℝ) (hs : s ∈ Icc (1 : ℝ) 5) : |coefficient δ s| ≤ 10 := by
  rw [coefficient_eq hs]
  have hb := wuImprovementLimit_bounds hδ hδhi hs.1 (hs.2.trans (by norm_num))
  have hs0 : 0 < s := lt_of_lt_of_le (by norm_num) hs.1
  have hf : 0 ≤ jr1965f s := jr1965f_nonneg hs0
  have ha : 0 ≤ wuLowerCoefficient s := by unfold wuLowerCoefficient; positivity
  have hA : wuUpperCoefficient s ≤ 10 := by
    unfold wuUpperCoefficient
    apply (div_le_iff₀ (by positivity : 0 < 2 * exp eulerMascheroniConstant)).mpr
    have hF := mul_le_mul_of_nonneg_left (jr1965F_le_delayConstant hs.1) hs0.le
    unfold jr1965DelayConstant at hF
    exact hF.trans (mul_le_mul_of_nonneg_right
      (hs.2.trans (by norm_num : (5 : ℝ) ≤ 10)) (by positivity))
  rw [abs_of_nonneg (add_nonneg ha hb.2.2.1)]
  linarith [hb.2.2.2]

theorem original_ah_uniform_limit {ε : ℝ} (hε : 0 < ε) :
    ∃ η0 : ℝ, 0 < η0 ∧ η0 ≤ 1 / 100 ∧
      ∀ η : ℝ, 0 < η → η < η0 →
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 100 →
        |originalMass (kernel δ (coefficient δ)) 0 -
          originalMass (kernel δ (coefficient δ)) η| < ε := by
  obtain ⟨η0, hη0, hη0hi, h⟩ := original_kernel_uniform_limit hε
  refine ⟨η0, hη0, hη0hi, ?_⟩
  intro η hη hηhi δ hδ hδhi
  exact h η hη hηhi δ hδ.le hδhi (coefficient δ)
    (coefficient_measurable hδ (by linarith))
    (coefficient_bound hδ (by linarith))

theorem mass_congr_on_envelope {f g : ℝ × ℝ → ℝ} {η : ℝ}
    (hη : 0 ≤ η) (hfg : EqOn f g originalEnvelope) :
    originalMass f η = originalMass g η := by
  have ha : mass f (100 / 1327) (25 / 206) (25 / 206)
      (1 / 2 - 2 * (25 / 206) - η) =
      mass g (100 / 1327) (25 / 206) (25 / 206)
        (1 / 2 - 2 * (25 / 206) - η) := by
    apply setIntegral_congr_fun (rectangle_measurable _ _ _ _)
    intro z hz
    exact hfg ⟨hz.1, hz.2.1, by linarith [hz.2.2]⟩
  have hb : mass f (100 / 1327) (3 * (100 / 1327) / 2)
      (1 / 2 - 2 * (25 / 206)) (1 / 2 - 3 * (100 / 1327) - η) =
      mass g (100 / 1327) (3 * (100 / 1327) / 2)
        (1 / 2 - 2 * (25 / 206)) (1 / 2 - 3 * (100 / 1327) - η) := by
    apply setIntegral_congr_fun (rectangle_measurable _ _ _ _)
    intro z hz
    exact hfg ⟨⟨hz.1.1, by linarith [hz.1.2]⟩,
      (by norm_num : (25 / 206 : ℝ) ≤ 1 / 2 - 2 * (25 / 206)).trans hz.2.1,
      by linarith [hz.2.2]⟩
  simp only [originalMass, ha, hb]

theorem mass_actual_coefficient {δ ρ η : ℝ}
    (hρ : 0 ≤ ρ) (hρhi : ρ ≤ 1 / 100) (hη : 0 ≤ η) :
    originalMass (kernel ρ (coefficient δ)) η =
      originalMass (kernel ρ (fun s => wuLowerCoefficient s +
        wuImprovementLimit false δ s)) η := by
  apply mass_congr_on_envelope hη
  intro z hz
  unfold kernel
  rw [coefficient_eq (envelope_parameter hρ hρhi hz)]

end Wu18938Campaign.M5.OriginalAnalytic
