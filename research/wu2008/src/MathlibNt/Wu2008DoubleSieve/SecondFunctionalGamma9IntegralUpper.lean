import MathlibNt.Wu2008DoubleSieve.SecondFunctionalGamma9WeightedSource
import MathlibNt.Wu2008DoubleSieve.ElevenTermAssembly
import MathlibNt.Wu2008DoubleSieve.Omega3Relative
import MathlibNt.Wu2008DoubleSieve.OmegaSwitchedIntegral
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighNonunitKThetaNormalization

namespace Wu2008DoubleSieve
open Finset Real
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418
open scoped Classical

/-- Exact strict descending dictionary, transported from integer to real counts. -/
theorem secondFunctionalMother_gamma9_eq_wuOmega3Sum
    (p : SecondFunctionalParameters) (hp : p.MotherAdmissible)
    {i k N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1/2)
    (hb : wuSourceBox k δ N i Δ V) :
    secondFunctionalMotherGammaSum p N δ (convolutionWuWindows N Δ V) 9 =
      wuOmega3Sum N δ p.kappa3 p.kappa1 (convolutionWuWindows N Δ V) := by
  rw [secondFunctionalMother_gamma9_weighted_ordered_source p hp hN hδ hδhi hb]
  unfold wuOmega3Sum
  apply sum_congr rfl
  intro d _
  congr 1
  have h := congrArg (fun z : ℤ => (z : ℝ))
    (sum_s3_orderedTriples_descending N (wuLocalCutoff N δ d p.kappa1)
      (wuLocalCutoff N δ d p.kappa3)
      (fun t => (sourceSieveCount N (d*t.1*t.2.1*t.2.2) (d*t.1*N) t.2.1 : ℤ)))
  simpa only [Int.cast_sum, Int.cast_natCast, wuOmega3] using h

/-- This cap pays errors only; the leading term remains the actual integral supremum. -/
theorem omega3XIntegralEnvelope_uniform_cap {s t : ℝ}
    (hs : 2 ≤ s) (hst : s ≤ t) (ht : t ≤ 10) :
    0 ≤ omega3XIntegralEnvelope s t ∧ omega3XIntegralEnvelope s t ≤ 10000 := by
  have h := omega3XIntegralEnvelope_bounds hs hst ht
  have hs0 : 0 < s := by linarith
  have ht0 : 0 < t := hs0.trans_le hst
  have hw0 : 0 ≤ 1/s - 1/t := sub_nonneg.mpr (one_div_le_one_div_of_le hs0 hst)
  have hw1 : 1/s - 1/t ≤ 1 := by
    have := one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 2) hs
    have := one_div_pos.mpr ht0
    linarith
  have hp := pow_le_pow_left₀ hw0 hw1 3
  norm_num only [one_pow] at hp
  exact ⟨h.1, h.2.trans (by nlinarith only [hp])⟩

/-- One rho=tau works for the entire parameter range, before any cutoff is chosen. -/
theorem omega3_envelope_uniform_slack {δ ε : ℝ} (hδhi : δ < 1/2) (hε : 0 < ε) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ s t : ℝ, 2 ≤ s → s ≤ t → t ≤ 10 →
      (1+ρ)*((1+ρ)*(1+ρ*exp (-eulerMascheroniConstant))*(8/(1-2*δ)))/4 *
        omega3XIntegralEnvelope s t ≤
      (2/(1-2*δ))*omega3XIntegralEnvelope s t + ε/3 := by
  have hD : 0 < 1-2*δ := by linarith
  have he : 0 < (ε/(3*10001))*HighNonunit.sourceKCap := by
    exact mul_pos (by positivity) HighNonunit.sourceKCap_pos
  obtain ⟨ρ, hr, hc⟩ := HighNonunit.sourceK_positive_slack hD he
    (exp_pos (-eulerMascheroniConstant)).le
  have hc' : (1+ρ)*((1+ρ)*(1+ρ*exp (-eulerMascheroniConstant))*(8/(1-2*δ)))/4 ≤
      2/(1-2*δ) + ε/(3*10001) := by
    have hz := ne_of_gt HighNonunit.sourceKCap_pos
    have hcancel : ε/(3*10001)*HighNonunit.sourceKCap/HighNonunit.sourceKCap = ε/(3*10001) := by
      field_simp
    rw [hcancel] at hc
    convert hc using 1
    ring
  refine ⟨ρ, hr, ?_⟩
  intro s t hs hst ht
  have hI := omega3XIntegralEnvelope_uniform_cap hs hst ht
  have h1 := mul_le_mul_of_nonneg_right hc' hI.1
  have h2 := mul_le_mul_of_nonneg_left hI.2 (show 0 ≤ ε/(3*10001) by positivity)
  nlinarith only [h1, h2, hε]

/-- Actual Omega3 with one epsilon and the full fixed-delta density loss.
The cutoff is uniform in both endpoints and in all source boxes. -/
theorem wuOmega3Sum_uniform_integral_upper (k : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1/2) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → t ≤ 10 →
      wuOmega3Sum N δ s t (convolutionWuWindows N Δ V) ≤
        ((2/(1-2*δ))*omega3XIntegralEnvelope s t + ε) *
          boxTheta N ((N:ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) := by
  obtain ⟨ρ, hr, hc⟩ := omega3_envelope_uniform_slack hδhi hε
  have he : 0 < ε/3 := by positivity
  obtain ⟨T1, hT14, hT1⟩ := wu04_54 k hδ hδhi he
  obtain ⟨T2, _, hT2⟩ := omega3_switched_upper_envelope k hδ hδhi hr hr he
  refine ⟨max T1 T2, hT14.trans (le_max_left _ _), ?_⟩
  intro N hN heven i Δ V hb s t hs hst ht
  have hN4 : 4 ≤ N := hT14.trans ((le_max_left _ _).trans hN)
  have h1 := hT1 N ((le_max_left _ _).trans hN) N le_rfl heven i Δ V hb s t hs hst ht
  have h2 := hT2 N ((le_max_right _ _).trans hN) heven i Δ V hb s t hs hst ht
  have hli : 0 ≤ logarithmicIntegral N :=
    MathlibNt.SieveTheory.LiuWeight.liuLogarithmicIntegral_nonneg 0 le_rfl
      (by exact_mod_cast (show 2 ≤ N by omega))
  have hTheta : 0 ≤ boxTheta N ((N:ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) := by
    unfold boxTheta
    apply mul_nonneg (mul_nonneg (by norm_num) hli)
    exact sum_nonneg fun d hd => HighNonunit.sourceKTheta_weight_nonneg hN4 hδ hδhi hb hd
  have h3 := mul_le_mul_of_nonneg_right (hc s t hs hst ht) hTheta
  dsimp only at h1 h2
  nlinarith only [h1, h2, h3]

/-- The original Gamma9, not an assumed surrogate or a fixed-row estimate. -/
theorem secondFunctionalMother_gamma9_integral_upper (k : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1/2) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible → 2 ≤ p.s →
      secondFunctionalMotherGammaSum p N δ (convolutionWuWindows N Δ V) 9 ≤
        ((2/(1-2*δ))*omega3XIntegralEnvelope p.kappa3 p.kappa1 + ε) *
          boxTheta N ((N:ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) := by
  obtain ⟨T, hT4, hT⟩ := wuOmega3Sum_uniform_integral_upper k hδ hδhi hε
  refine ⟨T, hT4, ?_⟩
  intro N hN he i Δ V hb p hp hs
  rw [secondFunctionalMother_gamma9_eq_wuOmega3Sum p hp (by omega) hδ hδhi hb]
  exact hT N hN he i Δ V hb p.kappa3 p.kappa1 (hs.trans hp.s_le_kappa3)
    (hp.kappa3_lt_kappa2.trans hp.kappa2_lt_kappa1).le (hp.kappa1_le_S.trans hp.S_le_ten)

end Wu2008DoubleSieve
