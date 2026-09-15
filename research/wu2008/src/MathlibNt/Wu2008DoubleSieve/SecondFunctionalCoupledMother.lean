import MathlibNt.Wu2008DoubleSieve.SecondFunctionalCoupledKernel

namespace Wu2008DoubleSieve.SecondFunctionalCoupled
open Finset Real FourthRowPhiOmega2
open scoped Classical

/-- The genuine H/J coefficient, with one joint supremum and the fixed delta loss. -/
noncomputable def coefficient (p : SecondFunctionalParameters) (δ : ℝ) : ℝ :=
  4 * wuUpperCoefficient p.S + wuUpperCoefficient p.kappa1 -
    4 * wuImprovementLimit true δ p.S - wuImprovementLimit true δ p.kappa1 -
    J δ p.s p.S - J δ p.kappa2 p.S - J δ p.kappa3 p.S +
    (2/(1-2*δ))*omega3XIntegralEnvelope p.kappa3 p.kappa1 +
    MotherPair.fourIntegralUpper p δ + (2/(1-2*δ))*jointSup p

/-- Complete original mother: no finite Gamma or residual KTheta remains. -/
theorem mother (p : SecondFunctionalParameters) (hp : MotherPair.AnalyticParameters p)
    (k : ℕ) (hk : 1 ≤ k) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1/10) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
        5 * wuBoxPhi N δ (convolutionWuWindows N Δ V) p.s ≤
          (coefficient p δ + ε) *
            boxTheta N ((N:ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) := by
  obtain ⟨T, hT, hm⟩ := secondFunctional_pair_gain_kTheta_mother p hp k hk hδ hδhi hε
  refine ⟨T, hT, ?_⟩
  intro N hN he i Δ V hb
  have hbase := hm N hN he i Δ V hb
  have hscalar := (theta_scalarization (hT.trans hN) hδ (by linarith) hb
    p hp.mother hp.two_lt_s.le).2
  have hD : 0 ≤ 2/(1-2*δ) := div_nonneg (by norm_num) (by linarith)
  have hpay := mul_le_mul_of_nonneg_left hscalar hD
  unfold coefficient
  nlinarith only [hbase, hpay]

/-- The feedback candidate is a genuine improvement, not an assumed estimate. -/
noncomputable def feedback (p : SecondFunctionalParameters) (δ : ℝ) : ℝ :=
  wuUpperCoefficient p.s - coefficient p δ / 5

/-- Threshold membership is proved directly from the complete original mother. -/
theorem feedback_sub_mem (p : SecondFunctionalParameters) (hp : MotherPair.AnalyticParameters p)
    (k : ℕ) (hk : 1 ≤ k) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1/10) (hε : 0 < ε) :
    feedback p δ - ε ∈ wuEventualImprovements true k δ p.s := by
  obtain ⟨T, _, hm⟩ := mother p hp k hk hδ hδhi (show 0 < 5*ε by positivity)
  refine ⟨T, ?_⟩
  intro N hN _ he i Δ V hb
  have h := hm N hN he i Δ V hb
  change wuBoxPhi N δ (convolutionWuWindows N Δ V) p.s ≤
    (wuUpperCoefficient p.s - (feedback p δ - ε)) *
      boxTheta N ((N:ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V)
  unfold feedback
  linarith only [h]

/-- First take the actual fixed-depth supremum, then remove the positive slack. -/
theorem feedback_le_fixed_depth (p : SecondFunctionalParameters)
    (hp : MotherPair.AnalyticParameters p) (k : ℕ) (hk : 1 ≤ k) {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1/10) :
    feedback p δ ≤ wuImprovementAtInfinity true k δ p.s := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have h := le_csSup (wuEventualImprovements_bddAbove true k hδ (by linarith)
    hp.mother.one_le_s (hp.s_le_three.trans (by norm_num)))
    (feedback_sub_mem p hp k hk hδ hδhi hε)
  change feedback p δ - ε ≤ wuImprovementAtInfinity true k δ p.s at h
  linarith only [h]

/-- The depth infimum is taken only after the fixed-depth eventual supremum. -/
theorem feedback_le_limit (p : SecondFunctionalParameters)
    (hp : MotherPair.AnalyticParameters p) {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1/10) :
    feedback p δ ≤ wuImprovementLimit true δ p.s := by
  exact le_ciInf (fun k => feedback_le_fixed_depth p hp (k+1) (by omega) hδ hδhi)

/-- Expanded final feedback retains all original H/J integrals and Gamma9 envelope. -/
theorem actual_limit (p : SecondFunctionalParameters)
    (hp : MotherPair.AnalyticParameters p) {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1/10) :
    wuUpperCoefficient p.s -
      (4 * wuUpperCoefficient p.S + wuUpperCoefficient p.kappa1 -
        4 * wuImprovementLimit true δ p.S - wuImprovementLimit true δ p.kappa1 -
        J δ p.s p.S - J δ p.kappa2 p.S - J δ p.kappa3 p.S +
        (2/(1-2*δ))*omega3XIntegralEnvelope p.kappa3 p.kappa1 +
        MotherPair.fourIntegralUpper p δ + (2/(1-2*δ))*jointSup p)/5 ≤
      wuImprovementLimit true δ p.s :=
  feedback_le_limit p hp hδ hδhi

end Wu2008DoubleSieve.SecondFunctionalCoupled
