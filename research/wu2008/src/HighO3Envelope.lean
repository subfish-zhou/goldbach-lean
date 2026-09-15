import HighO3Actual

namespace HighO3
open Finset Real Wu2008DoubleSieve HighBoxRecovery HighTheta Filter
open scoped Classical Topology
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418
noncomputable section

/-- Fixed delta, rho and true-Li slack. The coefficient is NOT the limit 2I.
No independent phi supremum is coupled to Omega2 or joint input. -/
theorem original_and_inserted_envelope {δ ρ τ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 50*highEta) (hρ : 0 < ρ) (hτ : 0 < τ) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N → ∀ Δ : ℝ,
      1+log (N : ℝ)^(-4 : ℝ) ≤ Δ → Δ < 1+2*log (N : ℝ)^(-4 : ℝ) →
      ∀ V : Fin 2 → ℝ, (∀ j, (N : ℝ)^(100/1327 : ℝ) ≤ V j) → OriginalRectangles N V →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → t ≤ 10 →
      (let W := convolutionWuWindows N Δ V
       omega3SwitchedSiftedCountLE N δ s t (sqrt ((N : ℝ)^(1/2-δ))) W+
         HighCross.switchingLoss N δ s t W ≤
       ((1+τ)*densityFactor δ ρ/4*omega3XIntegralEnvelope s t+ε)*
         boxTheta N ((N : ℝ)^(1/2-δ)) W) ∧
      ∀ U : ℝ, ActualInsertion N δ Δ U V →
      let W := convolutionWuWindows N Δ (Fin.cons U V)
      omega3SwitchedSiftedCountLE N δ s t (sqrt ((N : ℝ)^(1/2-δ))) W+
        HighCross.switchingLoss N δ s t W ≤
      ((1+τ)*densityFactor δ ρ/4*omega3XIntegralEnvelope s t+ε)*
        boxTheta N ((N : ℝ)^(1/2-δ)) W := by
  have hη : 0 < highEta := by norm_num [highEta]
  have hδhalf : δ < 1/2 := lt_of_le_of_lt hδhi (by norm_num [highEta])
  have hK : 0 < densityFactor δ ρ := omega3X_fixed_density_factor_pos hδhalf hρ
  obtain ⟨T1,hT14,hI⟩ := original_and_inserted_integral hδ hδhi hρ hε
  obtain ⟨T2,_,hLi⟩ := omega3X_trueLi_sharp_lower hτ
  obtain ⟨T3,hsmall⟩ := eventually_atTop.mp delta_eventually_small
  refine ⟨max T1 (max T2 T3),hT14.trans (le_max_left _ _),?_⟩
  intro N hN he Δ hlo hhi V hV hrect s t hs hst ht
  have hN1 := (le_max_left T1 _).trans hN
  have hN2 := (le_max_left T2 T3).trans ((le_max_right T1 _).trans hN)
  have hN3 := (le_max_right T2 T3).trans ((le_max_right T1 _).trans hN)
  have hN4 := hT14.trans hN1
  have hi := hI N hN1 he Δ hlo hhi V hV hrect s t hs hst ht
  obtain ⟨hΔ,hΔhi⟩ := hsmall N hN3 Δ hlo hhi
  have hconsume : ∀ {i : ℕ} (W : Fin i → Finset ℕ),
      (∀ j p, p ∈ W j → p.Prime) →
      (∀ d ∈ boxConvolutionSupport W, (d : ℝ) ≤ (N : ℝ)^(1/2-δ-10*highEta)) →
      omega3SwitchedSiftedCountLE N δ s t (sqrt ((N : ℝ)^(1/2-δ))) W+
        HighCross.switchingLoss N δ s t W ≤
      omega3XIntegralMain N δ s t W*(densityFactor δ ρ*wuSingularSeries N/log N)+
        ε*boxTheta N ((N : ℝ)^(1/2-δ)) W →
      omega3SwitchedSiftedCountLE N δ s t (sqrt ((N : ℝ)^(1/2-δ))) W+
        HighCross.switchingLoss N δ s t W ≤
      ((1+τ)*densityFactor δ ρ/4*omega3XIntegralEnvelope s t+ε)*
        boxTheta N ((N : ℝ)^(1/2-δ)) W := by
    intro i W hW hsize hcount
    have hb := integral_envelope_scaled W hN4 hδ hδhalf hη
      (fun d hd => ⟨boxConvolutionSupport_pos (fun j p hp => (hW j p hp).pos) hd,hsize d hd⟩)
      hs hst ht hK.le (hLi N hN2)
    calc
      _ ≤ omega3XIntegralMain N δ s t W*(densityFactor δ ρ*wuSingularSeries N/log N)+
          ε*boxTheta N ((N : ℝ)^(1/2-δ)) W := hcount
      _ ≤ ((1+τ)*densityFactor δ ρ/4*omega3XIntegralEnvelope s t)*
          boxTheta N ((N : ℝ)^(1/2-δ)) W+ε*boxTheta N ((N : ℝ)^(1/2-δ)) W := add_le_add hb le_rfl
      _ = _ := by ring
  have hg := original_box_geometry (show 2 ≤ N by omega) hδhi hΔ hΔhi hV hrect
  refine ⟨hconsume _ (fun j p hp => (hg.1 j p hp).1) hg.2 hi.1,?_⟩
  intro U hw
  have hig := inserted_box_geometry (show 2 ≤ N by omega) hδhi hΔ hΔhi hV hrect hw
  exact hconsume _ (fun j p hp => (hig.1 j p hp).1) hig.2 (hi.2 U hw)

/-- The original unswitched Omega3 plus repeated-prime lane is actually paid
by the same original/insertion integral envelope, not a target assumption. -/
theorem original_and_inserted_omega3_envelope {δ ρ τ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 50*highEta) (hρ : 0 < ρ) (hτ : 0 < τ) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N → ∀ Δ : ℝ,
      1+log (N : ℝ)^(-4 : ℝ) ≤ Δ → Δ < 1+2*log (N : ℝ)^(-4 : ℝ) →
      ∀ V : Fin 2 → ℝ, (∀ j, (N : ℝ)^(100/1327 : ℝ) ≤ V j) → OriginalRectangles N V →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → t ≤ 10 →
      (let W := convolutionWuWindows N Δ V
       wuOmega3Sum N δ s t W+wuOmegaRepeatedSum N δ s t W ≤
       ((1+τ)*densityFactor δ ρ/4*omega3XIntegralEnvelope s t+ε)*
         boxTheta N ((N : ℝ)^(1/2-δ)) W) ∧
      ∀ U : ℝ, ActualInsertion N δ Δ U V →
      let W := convolutionWuWindows N Δ (Fin.cons U V)
      wuOmega3Sum N δ s t W+wuOmegaRepeatedSum N δ s t W ≤
      ((1+τ)*densityFactor δ ρ/4*omega3XIntegralEnvelope s t+ε)*
        boxTheta N ((N : ℝ)^(1/2-δ)) W := by
  obtain ⟨T,hT4,hT⟩ := original_and_inserted_envelope hδ hδhi hρ hτ hε
  refine ⟨T,hT4,?_⟩
  intro N hN he Δ hlo hhi V hV hrect s t hs hst ht
  have hb := hT N hN he Δ hlo hhi V hV hrect s t hs hst ht
  refine ⟨(omega3_add_repeated_le_closed _ (hT4.trans hN) he
    (fun _ _ hp => (mem_convolutionWuWindows.mp hp).1)).trans hb.1,?_⟩
  intro U hw
  exact (omega3_add_repeated_le_closed _ (hT4.trans hN) he
    (fun _ _ hp => (mem_convolutionWuWindows.mp hp).1)).trans (hb.2 U hw)

end
end HighO3
