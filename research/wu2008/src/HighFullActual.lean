import HighFullLocal

namespace HighFull
open Finset Real Filter Wu2008DoubleSieve HighTheta HighBoxRecovery
open scoped Classical Topology
noncomputable section

/-- Actual original and occupied one-insertion upper counts through ten.
The full AP convolution is paid once; C and T precede s and all moving boxes. -/
theorem original_inserted_upper {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 50*highEta) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N → ∀ Δ : ℝ,
      1+log (N : ℝ)^(-4 : ℝ) ≤ Δ → Δ < 1+2*log (N : ℝ)^(-4 : ℝ) →
      ∀ V : Fin 2 → ℝ, (∀ j, (N : ℝ)^(100/1327 : ℝ) ≤ V j) → OriginalRectangles N V →
      ∀ s : ℝ, 3/2 ≤ s → s ≤ 10 →
      let claim := fun {i : ℕ} (W : Fin i → Finset ℕ) =>
        HighCross.rosserUpper N δ s W ≤
          (wuUpperCoefficient s+ε)*boxTheta N ((N : ℝ)^(1/2-δ)) W+C*N/log (N : ℝ)^(18 : ℝ) ∧
        wuBoxPhi N δ W s ≤
          (wuUpperCoefficient s+ε)*boxTheta N ((N : ℝ)^(1/2-δ)) W+C*N/log (N : ℝ)^(18 : ℝ)
      claim (convolutionWuWindows N Δ V) ∧
        ∀ U : ℝ, ActualInsertion N δ Δ U V → claim (convolutionWuWindows N Δ (Fin.cons U V)) := by
  have hη : 0 < highEta := by norm_num [highEta]
  obtain ⟨T0,_,hm⟩ := main_upper hδ.le hη hε
  obtain ⟨C,hC,T1,hBV⟩ := convolution_bombieri_vinogradov 3 hη hδ (show (0 : ℝ)<18 by norm_num)
  obtain ⟨T2,hsmall⟩ := eventually_atTop.mp delta_eventually_small
  refine ⟨C,hC,max 4 (max T0 (max T1 T2)),le_max_left _ _,?_⟩
  intro N hN he Δ hlo hhi V hV hr s hs hs10
  have hN4 : 4 ≤ N := (le_max_left _ _).trans hN
  have hN0 := (le_max_left T0 _).trans ((le_max_right 4 _).trans hN)
  have hN12 := (le_max_right T0 _).trans ((le_max_right 4 _).trans hN)
  have hN1 := (le_max_left T1 T2).trans hN12
  have hN2 := (le_max_right T1 T2).trans hN12
  obtain ⟨hΔ,hΔhi⟩ := hsmall N hN2 Δ hlo hhi
  have consume : ∀ {i : ℕ} (W : Fin i → Finset ℕ), i ≤ 3 →
      (∀ j p, p ∈ W j → p.Prime ∧ p.Coprime N ∧ (N : ℝ)^highEta ≤ p) →
      (∀ d ∈ boxConvolutionSupport W, (d : ℝ) ≤ (N : ℝ)^(1/2-δ-10*highEta)) →
      HighCross.rosserUpper N δ s W ≤
        (wuUpperCoefficient s+ε)*boxTheta N ((N : ℝ)^(1/2-δ)) W+C*N/log (N : ℝ)^(18 : ℝ) ∧
      wuBoxPhi N δ W s ≤
        (wuUpperCoefficient s+ε)*boxTheta N ((N : ℝ)^(1/2-δ)) W+C*N/log (N : ℝ)^(18 : ℝ) := by
    intro i W hi hW hsize
    have hmain := hm N hN0 he i W (fun j p hp => (hW j p hp).1) hsize s hs hs10
    have hAP := hBV N hN1 i hi W hW
    have hR : HighCross.rosserUpper N δ s W ≤
        (wuUpperCoefficient s+ε)*boxTheta N ((N : ℝ)^(1/2-δ)) W+C*N/log (N : ℝ)^(18 : ℝ) :=
      add_le_add hmain hAP
    have hg := HighCross.support_admission W (show 2 ≤ N by omega) hη
      (fun j p hp => (hW j p hp).1) hsize
    exact ⟨hR,(HighCross.rosser_upper W hg.2 (by linarith)).trans hR⟩
  have hg := original_box_geometry (show 2 ≤ N by omega) hδhi hΔ hΔhi hV hr
  refine ⟨consume _ (by norm_num)
    (fun j p hp => ⟨(hg.1 j p hp).1,(mem_convolutionWuWindows.mp hp).2.1,(hg.1 j p hp).2⟩) hg.2,?_⟩
  intro U hu
  have hig := inserted_box_geometry (show 2 ≤ N by omega) hδhi hΔ hΔhi hV hr hu
  exact consume _ le_rfl
    (fun j p hp => ⟨(hig.1 j p hp).1,(mem_convolutionWuWindows.mp hp).2.1,(hig.1 j p hp).2⟩) hig.2

end
end HighFull
