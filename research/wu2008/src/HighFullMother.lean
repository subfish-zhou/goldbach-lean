import HighFullActual
import HighO3Envelope

namespace HighFull
open Finset Real Filter Wu2008DoubleSieve HighTheta HighBoxRecovery
open scoped Classical Topology
noncomputable section

/-- Literal signed finite mother, preserving the actual negative Omega2 and
all positive Omega3/repeated labels before any analytic upper substitution. -/
theorem signed_counts {i N : ℕ} {δ s t : ℝ} (W : Fin i → Finset ℕ)
    (hQ : ∀ d ∈ boxConvolutionSupport W, 1 < (N : ℝ)^(1/2-δ)/d)
    (hs : 2 ≤ s) (hst : s ≤ t) :
    wuBoxPhi N δ W s ≤ wuBoxPhi N δ W t-wuOmega2Sum N δ s t W/2+
      (wuOmega3Sum N δ s t W+wuOmegaRepeatedSum N δ s t W)/2 := by
  have hw := wu_omega_weighted_box (N := N) (δ := δ) (s := s) (t := t) W
    (fun d hd => rpow_le_rpow_of_exponent_le (hQ d hd).le
      (one_div_le_one_div_of_le (by linarith) hst))
  rw [HighCross.omega1_eq_twice_phi] at hw
  linarith

/-- Actual upper with the already-paid original Omega3 integral envelope.
The negative Omega2 is the full literal count, not a presumed log lower bound.
K retains fixed delta, rho and true-Li tau; no limit coefficient is substituted. -/
theorem original_inserted_mother {δ ρ τ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 50*highEta) (hρ : 0 < ρ) (hτ : 0 < τ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N → ∀ Δ : ℝ,
      1+log (N : ℝ)^(-4 : ℝ) ≤ Δ → Δ < 1+2*log (N : ℝ)^(-4 : ℝ) →
      ∀ V : Fin 2 → ℝ, (∀ j, (N : ℝ)^(100/1327 : ℝ) ≤ V j) → OriginalRectangles N V →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → t ≤ 10 →
      let claim := fun {i : ℕ} (W : Fin i → Finset ℕ) =>
        wuBoxPhi N δ W s ≤
          (wuUpperCoefficient t+(1+τ)*HighO3.densityFactor δ ρ/8*omega3XIntegralEnvelope s t+ε)*
            boxTheta N ((N : ℝ)^(1/2-δ)) W-wuOmega2Sum N δ s t W/2+
            C*N/log (N : ℝ)^(18 : ℝ)
      claim (convolutionWuWindows N Δ V) ∧
        ∀ U : ℝ, ActualInsertion N δ Δ U V → claim (convolutionWuWindows N Δ (Fin.cons U V)) := by
  obtain ⟨C,hC,T0,hT04,hu⟩ := original_inserted_upper hδ hδhi (show 0 < ε/2 by positivity)
  obtain ⟨T1,_,ho⟩ := HighO3.original_and_inserted_omega3_envelope hδ hδhi hρ hτ hε
  obtain ⟨T2,hsmall⟩ := eventually_atTop.mp delta_eventually_small
  refine ⟨C,hC,max T0 (max T1 T2),hT04.trans (le_max_left _ _),?_⟩
  intro N hN he Δ hlo hhi V hV hr s t hs hst ht
  have hN0 := (le_max_left T0 _).trans hN
  have hN1 := (le_max_left T1 T2).trans ((le_max_right T0 _).trans hN)
  have hN2 := (le_max_right T1 T2).trans ((le_max_right T0 _).trans hN)
  have hN4 := hT04.trans hN0
  have hup := hu N hN0 he Δ hlo hhi V hV hr t (by linarith) ht
  have hop := ho N hN1 he Δ hlo hhi V hV hr s t hs hst ht
  obtain ⟨hΔ,hΔhi⟩ := hsmall N hN2 Δ hlo hhi
  have consume : ∀ {i : ℕ} (W : Fin i → Finset ℕ),
      (∀ j p, p ∈ W j → p.Prime) →
      (∀ d ∈ boxConvolutionSupport W, (d : ℝ) ≤ (N : ℝ)^(1/2-δ-10*highEta)) →
      wuBoxPhi N δ W t ≤
        (wuUpperCoefficient t+ε/2)*boxTheta N ((N : ℝ)^(1/2-δ)) W+C*N/log (N : ℝ)^(18 : ℝ) →
      wuOmega3Sum N δ s t W+wuOmegaRepeatedSum N δ s t W ≤
        ((1+τ)*HighO3.densityFactor δ ρ/4*omega3XIntegralEnvelope s t+ε)*
          boxTheta N ((N : ℝ)^(1/2-δ)) W →
      wuBoxPhi N δ W s ≤
        (wuUpperCoefficient t+(1+τ)*HighO3.densityFactor δ ρ/8*omega3XIntegralEnvelope s t+ε)*
          boxTheta N ((N : ℝ)^(1/2-δ)) W-wuOmega2Sum N δ s t W/2+
          C*N/log (N : ℝ)^(18 : ℝ) := by
    intro i W hW hsize hupper hO
    have hg := HighCross.support_admission W (show 2 ≤ N by omega)
      (show 0 < highEta by norm_num [highEta]) hW hsize
    have hfinite := signed_counts W hg.2 hs hst
    nlinarith only [hfinite,hupper,hO]
  have hg := original_box_geometry (show 2 ≤ N by omega) hδhi hΔ hΔhi hV hr
  refine ⟨consume _ (fun j p hp => (hg.1 j p hp).1) hg.2 hup.1.2 hop.1,?_⟩
  intro U hi
  have hig := inserted_box_geometry (show 2 ≤ N by omega) hδhi hΔ hΔhi hV hr hi
  exact consume _ (fun j p hp => (hig.1 j p hp).1) hig.2 (hup.2 U hi).2 (hop.2 U hi)

end
end HighFull
