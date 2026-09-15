import MathlibNt.Wu2008DoubleSieve.HighSixTailIntegral
import MathlibNt.Wu2008DoubleSieve.SingleUpperClassicalAssembly

namespace Wu2008DoubleSieve.HighSix
open Real Set
open SingleUpperQuadrature SingleUpperHighQuadrature
open SingleUpperCounts SingleUpperSplice SingleUpperClassicalLimit
open SingleUpperClassicalAssembly SingleUpperLowEndpoint

/-- Exact adjacent integral assembly; constant A is used only on the original j6 interval. -/
theorem high_integral_split_j6 {δ : ℝ} (hδ : 0 ≤ δ) (hδhi : δ ≤ 1/100) :
    (∫ t in ((1/2-δ)/2)..left, weight δ t/t) + primeIntegral δ +
      (∫ t in right..(1/3 : ℝ), weight δ t/t) =
      ∫ t in ((1/2-δ)/2)..(1/3 : ℝ), weight δ t/t := by
  have hc : (1/15 : ℝ) ≤ (1/2-δ)/2 := by linarith
  have hcl : (1/2-δ)/2 ≤ left := by norm_num [left]; linarith
  have hlr : left ≤ right := by norm_num [left,right]
  have hr3 : right ≤ (1/3 : ℝ) := by norm_num [right]
  have hi1 := density_integrable hδ hδhi hc hcl (hlr.trans hr3)
  have hi2 := density_integrable hδ hδhi (hc.trans hcl) hlr hr3
  have hi3 := density_integrable hδ hδhi ((hc.trans hcl).trans hlr) hr3 le_rfl
  have he : (∫ t in left..right, weight δ t/t) = primeIntegral δ := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hlr] at ht
    dsimp only
    rw [primeWeight_eq_single hδ hδhi ht]
    simp only [primeWeight,div_eq_mul_inv,mul_inv_rev,one_mul]
  rw [← he, intervalIntegral.integral_add_adjacent_intervals hi1 hi2,
    intervalIntegral.integral_add_adjacent_intervals (hi1.trans hi2) hi3]

/-- The complete original high U3 count. No sign is assumed for Psi or its complement. -/
theorem U3_high_psi_integral_upper {δ ε : ℝ} (hδ : 0 < δ)
    (hδhi : δ ≤ 1/100) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      highCount N δ (1/3) ≤
        (4*(∫ t in ((1/2-δ)/2)..(1/3 : ℝ), weight δ t/t) -
          4*firstFunctionalGainPsi δ s S*primeIntegral δ+ε)*truncatedSixthMassScale N := by
  obtain ⟨TA,hTA4,hA⟩ := U3_high_j6_inserted hδ hδhi (half_pos hε)
  obtain ⟨TB,_,hB⟩ := HighSixTail.actual_tail_classical_upper hδ hδhi (half_pos hε)
  refine ⟨max TA TB,hTA4.trans (le_max_left _ _),?_⟩
  intro N hN he
  have ha := hA N (by omega) he
  have hb := hB N (by omega) he
  have hs := high_integral_split_j6 hδ.le hδhi
  rw [← hs]
  nlinarith only [ha,hb]

/-- Paper PsiOne notation keeps the entire fixed-delta penalty in the full high count. -/
theorem U3_high_source_integral_upper {δ ε : ℝ} (hδ : 0 < δ)
    (hδhi : δ ≤ 1/100) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      highCount N δ (1/3) ≤
        (4*(∫ t in ((1/2-δ)/2)..(1/3 : ℝ), weight δ t/t) -
          4*firstFunctionalGainPsiOne s S*primeIntegral δ +
          4*(2*δ/(1-2*δ))*omega3XIntegralEnvelope s S*primeIntegral δ+ε)*
            truncatedSixthMassScale N := by
  obtain ⟨T,hT4,hT⟩ := U3_high_psi_integral_upper hδ hδhi hε
  refine ⟨T,hT4,?_⟩
  intro N hN he
  have h := hT N hN he
  rw [psi_source_penalty hδhi] at h
  convert h using 1
  ring

/-- Reassemble low and high actual U3 counts, not a gain added to an old upper bound. -/
theorem U3_psi_Gdelta_upper {δ ε : ℝ} (hδ : 0 < δ)
    (hδhi : δ ≤ 1/100) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (U N (1/3) : ℝ) ≤
        (Gdelta δ (1/3)-4*firstFunctionalGainPsi δ s S*primeIntegral δ+ε)*
          truncatedSixthMassScale N := by
  obtain ⟨TL,hTL4,hL⟩ := lowCount_classical_upper hδ hδhi (half_pos hε)
  obtain ⟨TH,_,hH⟩ := U3_high_psi_integral_upper hδ hδhi (half_pos hε)
  refine ⟨max TL TH,hTL4.trans (le_max_left _ _),?_⟩
  intro N hN he
  have hl := hL N (by omega) he (1/3)
  have hh := hH N (by omega) he
  have hs := classical_integral_split hδ.le hδhi
    (show (1/2-δ)/2 ≤ (1/3 : ℝ) by linarith) (le_refl (1/3 : ℝ))
  rw [count_split]
  change lowCount N δ (1/3) + highCount N δ (1/3) ≤ _
  rw [← hs]
  nlinarith only [hl,hh]

/-- The two physical negative terms, retaining their overlap with multiplicity two. -/
theorem U3_U4_psi_Gdelta_upper {δ ε : ℝ} (hδ : 0 < δ)
    (hδhi : δ ≤ 1/100) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (U N (1/3) : ℝ)+(U N truncatedSixthLowerSigma : ℝ) ≤
        (Gdelta δ (1/3)+Gdelta δ truncatedSixthLowerSigma -
          4*firstFunctionalGainPsi δ s S*primeIntegral δ+ε)*truncatedSixthMassScale N := by
  obtain ⟨T3,hT34,h3⟩ := U3_psi_Gdelta_upper hδ hδhi (half_pos hε)
  obtain ⟨T4,_,h4⟩ := actual_Gdelta_upper hδ hδhi (half_pos hε)
  refine ⟨max T3 T4,hT34.trans (le_max_left _ _),?_⟩
  intro N hN he
  have hU3 := h3 N (by omega) he
  have hb := original_endpoint_bounds hδ.le
  have hU4 := h4 N (by omega) he truncatedSixthLowerSigma hb.2.1 hb.2.2
  nlinarith only [hU3,hU4]

end Wu2008DoubleSieve.HighSix
