import InsertedO2Final
import HighFullMother

namespace InsertedO2
open Finset Real Filter Wu2008DoubleSieve HighTheta HighBoxRecovery
open scoped Classical Topology Interval
noncomputable section

/-- The once-inserted actual box has the same original log integral mother.
The frozen full upper and original Ω3 envelope are consumed, not reproved.
Fixed positive δ,ρ,τ and the genuine remaining C*N/log^18 term are retained. -/
theorem inserted_log_integral_mother {δ ρ τ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 50*highEta)
    (hρ : 0 < ρ) (hτ : 0 < τ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N → ∀ Δ : ℝ,
      1+log (N : ℝ)^(-4 : ℝ) ≤ Δ → Δ < 1+2*log (N : ℝ)^(-4 : ℝ) →
      ∀ V : Fin 2 → ℝ, (∀ j, (N : ℝ)^(100/1327 : ℝ) ≤ V j) → OriginalRectangles N V →
      ∀ U : ℝ, ActualInsertion N δ Δ U V →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → 3 ≤ t → t ≤ 5 → 2 ≤ t-t/s →
      wuBoxPhi N δ (convolutionWuWindows N Δ (Fin.cons U V)) s ≤
        (wuUpperCoefficient t-
          (∫ u in (1-1/s)..(1-1/t), log (t*u-1)/(u*(1-u)))/2+
          (1+τ)*HighO3.densityFactor δ ρ/8*omega3XIntegralEnvelope s t+ε)*
          boxTheta N ((N : ℝ)^(1/2-δ)) (convolutionWuWindows N Δ (Fin.cons U V))+
        C*N/log (N : ℝ)^(18 : ℝ) := by
  obtain ⟨C,hC,T0,hT04,hupper⟩ := HighFull.original_inserted_mother
    hδ hδhi hρ hτ (half_pos hε)
  obtain ⟨T1,_,hlower⟩ := inserted_log_integral_lower hδ hδhi hε
  refine ⟨C,hC,max T0 T1,hT04.trans (le_max_left _ _),?_⟩
  intro N hN he Δ hlo hhi V hV hr U hU s t hs hst ht ht5 hc
  have hu := (hupper N ((le_max_left _ _).trans hN) he Δ hlo hhi V hV hr
    s t hs hst (by linarith)).2 U hU
  have hl := hlower N ((le_max_right _ _).trans hN) he Δ hlo hhi V hV hr
    U hU s t hs hst ht ht5 hc
  nlinarith only [hu,hl]

end
end InsertedO2
