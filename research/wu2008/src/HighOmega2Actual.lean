import HighOmega2Local

namespace HighOmega2
open Finset Real Wu2008DoubleSieve HighTheta HighBoxRecovery Filter
open scoped Classical Topology
noncomputable section

/-- Literal normalized main masses on original and every occupied insertion.
This uses the actual parent geometry and no source-domain identification. -/
theorem original_inserted_main {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 50*highEta) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N → ∀ Δ : ℝ,
      1+log (N : ℝ)^(-4 : ℝ) ≤ Δ → Δ < 1+2*log (N : ℝ)^(-4 : ℝ) →
      ∀ V : Fin 2 → ℝ, (∀ j, (N : ℝ)^(100/1327 : ℝ) ≤ V j) → OriginalRectangles N V →
      let claim := fun {i : ℕ} (W : Fin i → Finset ℕ) =>
        (∀ s : ℝ, 2 ≤ s → s ≤ 4 →
          (log (s-1)-4*ε)*boxTheta N ((N : ℝ)^(1/2-δ)) W ≤
            convolutionRosserMain N W false (wuVariableRosserLevel N δ)
              (fun d => wuLocalCutoff N δ d s)) ∧
        (∀ s : ℝ, 3/2 ≤ s → s ≤ 3 →
          convolutionRosserMain N W true (wuVariableRosserLevel N δ)
            (fun d => wuLocalCutoff N δ d s) ≤
              (1+ε)^2*boxTheta N ((N : ℝ)^(1/2-δ)) W)
      claim (convolutionWuWindows N Δ V) ∧
        ∀ U : ℝ, ActualInsertion N δ Δ U V → claim (convolutionWuWindows N Δ (Fin.cons U V)) := by
  obtain ⟨T0,_,hm⟩ := main_normalization hδ.le (show 0 < highEta by norm_num [highEta]) hε hε1
  obtain ⟨T1,hsmall⟩ := eventually_atTop.mp delta_eventually_small
  refine ⟨max 4 (max T0 T1),le_max_left _ _,?_⟩
  intro N hN he Δ hlo hhi V hV hr
  have hN4 : 4 ≤ N := (le_max_left _ _).trans hN
  have hN0 := (le_max_left T0 T1).trans ((le_max_right 4 _).trans hN)
  have hN1 := (le_max_right T0 T1).trans ((le_max_right 4 _).trans hN)
  obtain ⟨hΔ,hΔhi⟩ := hsmall N hN1 Δ hlo hhi
  have hg := original_box_geometry (show 2 ≤ N by omega) hδhi hΔ hΔhi hV hr
  refine ⟨hm N hN0 he 2 _ (fun j p hp => (hg.1 j p hp).1) hg.2,?_⟩
  intro U hu
  have hg' := inserted_box_geometry (show 2 ≤ N by omega) hδhi hΔ hΔhi hV hr hu
  exact hm N hN0 he 3 _ (fun j p hp => (hg'.1 j p hp).1) hg'.2

/-- A genuine count lower after classic log normalization, with the original
AP and closed-endpoint debit retained. This is not a positive h bound. -/
theorem original_inserted_lower {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 50*highEta) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N → ∀ Δ : ℝ,
      1+log (N : ℝ)^(-4 : ℝ) ≤ Δ → Δ < 1+2*log (N : ℝ)^(-4 : ℝ) →
      ∀ V : Fin 2 → ℝ, (∀ j, (N : ℝ)^(100/1327 : ℝ) ≤ V j) → OriginalRectangles N V →
      ∀ s : ℝ, 2 ≤ s → s ≤ 4 →
      let claim := fun {i : ℕ} (W : Fin i → Finset ℕ) =>
        (log (s-1)-4*ε)*boxTheta N ((N : ℝ)^(1/2-δ)) W - C*N/log (N : ℝ)^(18 : ℝ) ≤ wuBoxPhi N δ W s ∧
        (log (s-1)-5*ε)*boxTheta N ((N : ℝ)^(1/2-δ)) W - C*N/log (N : ℝ)^(18 : ℝ) ≤ wuBoxPhiLE N δ W s
      claim (convolutionWuWindows N Δ V) ∧
        ∀ U : ℝ, ActualInsertion N δ Δ U V → claim (convolutionWuWindows N Δ (Fin.cons U V)) := by
  obtain ⟨T0,hT04,hm⟩ := original_inserted_main hδ hδhi hε hε1
  obtain ⟨C,hC,T1,_,hl⟩ := original_and_inserted_lower_source hδ hδhi hε
  refine ⟨C,hC,max T0 T1,hT04.trans (le_max_left _ _),?_⟩
  intro N hN he Δ hlo hhi V hV hr s hs hs4
  have hm' := hm N ((le_max_left _ _).trans hN) he Δ hlo hhi V hV hr
  have hl' := hl N ((le_max_right _ _).trans hN) he Δ hlo hhi V hV hr s (by linarith) (by linarith)
  have consume : ∀ {i : ℕ} (W : Fin i → Finset ℕ),
      (log (s-1)-4*ε)*boxTheta N ((N : ℝ)^(1/2-δ)) W ≤
        convolutionRosserMain N W false (wuVariableRosserLevel N δ) (fun d => wuLocalCutoff N δ d s) →
      LowerSourcePaid N δ ε C s W →
      (log (s-1)-4*ε)*boxTheta N ((N : ℝ)^(1/2-δ)) W - C*N/log (N : ℝ)^(18 : ℝ) ≤ wuBoxPhi N δ W s ∧
      (log (s-1)-5*ε)*boxTheta N ((N : ℝ)^(1/2-δ)) W - C*N/log (N : ℝ)^(18 : ℝ) ≤ wuBoxPhiLE N δ W s := by
    intro i W hx hy
    dsimp [LowerSourcePaid] at hy
    constructor <;> nlinarith [hy.1,hy.2]
  exact ⟨consume _ (hm'.1.1 s hs hs4) hl'.1,
    fun U hu => consume _ ((hm'.2 U hu).1 s hs hs4) (hl'.2 U hu)⟩

end
end HighOmega2
