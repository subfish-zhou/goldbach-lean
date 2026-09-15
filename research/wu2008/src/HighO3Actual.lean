import HighO3Normalize
import HighO3Losses

namespace HighO3
open Finset Real Wu2008DoubleSieve HighBoxRecovery HighTheta Filter
open scoped Classical Topology
noncomputable section

/-- Fixed delta and rho coefficient from the original physical sieve. -/
def densityFactor (δ ρ : ℝ) : ℝ :=
  (1+ρ)*(1+ρ*exp (-eulerMascheroniConstant))*(8/(1-2*δ))

/-- Actual closed switched count PLUS all three switching losses, bounded by
the original integral. Both thresholds precede the moving original/insertion boxes. -/
theorem original_and_inserted_integral {δ ρ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 50*highEta) (hρ : 0 < ρ) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N → ∀ Δ : ℝ,
      1+log (N : ℝ)^(-4 : ℝ) ≤ Δ → Δ < 1+2*log (N : ℝ)^(-4 : ℝ) →
      ∀ V : Fin 2 → ℝ, (∀ j, (N : ℝ)^(100/1327 : ℝ) ≤ V j) → OriginalRectangles N V →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → t ≤ 10 →
      (let W := convolutionWuWindows N Δ V
       omega3SwitchedSiftedCountLE N δ s t (sqrt ((N : ℝ)^(1/2-δ))) W+
         HighCross.switchingLoss N δ s t W ≤
       omega3XIntegralMain N δ s t W*(densityFactor δ ρ*wuSingularSeries N/log N)+
         ε*boxTheta N ((N : ℝ)^(1/2-δ)) W) ∧
      ∀ U : ℝ, ActualInsertion N δ Δ U V →
      let W := convolutionWuWindows N Δ (Fin.cons U V)
      omega3SwitchedSiftedCountLE N δ s t (sqrt ((N : ℝ)^(1/2-δ))) W+
        HighCross.switchingLoss N δ s t W ≤
      omega3XIntegralMain N δ s t W*(densityFactor δ ρ*wuSingularSeries N/log N)+
        ε*boxTheta N ((N : ℝ)^(1/2-δ)) W := by
  have hη : 0 < highEta := by norm_num [highEta]
  have hδhalf : δ < 1/2 := lt_of_le_of_lt hδhi (by norm_num [highEta])
  have hK : 0 < densityFactor δ ρ := omega3X_fixed_density_factor_pos hδhalf hρ
  have hε3 : 0 < ε/3 := by positivity
  obtain ⟨T1,hT14,hX⟩ := X_integral_scaled hδ hδhalf hη hK hε3
  obtain ⟨T2,_,hL⟩ := losses_paid hδ hδhalf hη hε3
  obtain ⟨T3,_,hR⟩ := original_and_inserted_relative hδ hδhi hε3
  obtain ⟨T4,_,hS⟩ := omega3_switched_upper_source_density hδ hδhalf hρ
  obtain ⟨T5,hsmall⟩ := eventually_atTop.mp delta_eventually_small
  refine ⟨max T1 (max T2 (max T3 (max T4 T5))),hT14.trans (le_max_left _ _),?_⟩
  intro N hN he Δ hlo hhi V hV hrect s t hs hst ht
  have hN1 := (le_max_left T1 _).trans hN
  have hN2 := (le_max_left T2 _).trans ((le_max_right T1 _).trans hN)
  have hN3 := (le_max_left T3 _).trans ((le_max_right T2 _).trans ((le_max_right T1 _).trans hN))
  have hN4 := (le_max_left T4 T5).trans ((le_max_right T3 _).trans ((le_max_right T2 _).trans ((le_max_right T1 _).trans hN)))
  have hN5 := (le_max_right T4 T5).trans ((le_max_right T3 _).trans ((le_max_right T2 _).trans ((le_max_right T1 _).trans hN)))
  have hNfour := hT14.trans hN1
  obtain ⟨hΔ,hΔhi⟩ := hsmall N hN5 Δ hlo hhi
  have hr := hR N hN3 Δ hlo hhi V hV hrect s t hs hst ht
  have hconsume : ∀ {i : ℕ} (W : Fin i → Finset ℕ),
      (∀ j p, p ∈ W j → p.Prime ∧ (N : ℝ)^highEta ≤ p) →
      (∀ d ∈ boxConvolutionSupport W, (d : ℝ) ≤ (N : ℝ)^(1/2-δ-10*highEta)) →
      RelativeRemainders N δ (ε/3) s t W →
      omega3SwitchedSiftedCountLE N δ s t (sqrt ((N : ℝ)^(1/2-δ))) W+
        HighCross.switchingLoss N δ s t W ≤
      omega3XIntegralMain N δ s t W*(densityFactor δ ρ*wuSingularSeries N/log N)+
        ε*boxTheta N ((N : ℝ)^(1/2-δ)) W := by
    intro i W hW hsize hrem
    have hx := hX N hN1 i W (fun d hd =>
      ⟨boxConvolutionSupport_pos (fun j p hp => (hW j p hp).1.pos) hd,hsize d hd⟩) s t hs hst ht
    have hloss := hL N hN2 he i W hW hsize s t hs hst ht
    have hsieve := hS N hN4 he i s t W
    dsimp only at hsieve
    change _ ≤ omega3SieveX N δ s t W*(densityFactor δ ρ*wuSingularSeries N/log N)+_+_ at hsieve
    dsimp [RelativeRemainders] at hrem
    linarith
  have hg := original_box_geometry (show 2 ≤ N by omega) hδhi hΔ hΔhi hV hrect
  refine ⟨hconsume _ hg.1 hg.2 hr.1,?_⟩
  intro U hw
  have hig := inserted_box_geometry (show 2 ≤ N by omega) hδhi hΔ hΔhi hV hrect hw
  exact hconsume _ hig.1 hig.2 (hr.2 U hw)

/-- The strict switched convention is below the closed one without changing
any of the three losses or any coefficient. -/
theorem strict_add_loss_le_closed {i N : ℕ} {δ s t : ℝ} (W : Fin i → Finset ℕ)
    (hW : ∀ j p, p ∈ W j → p.Prime) :
    omega3SwitchedSiftedCount N δ s t (sqrt ((N : ℝ)^(1/2-δ))) W+
      HighCross.switchingLoss N δ s t W ≤
    omega3SwitchedSiftedCountLE N δ s t (sqrt ((N : ℝ)^(1/2-δ))) W+
      HighCross.switchingLoss N δ s t W :=
  add_le_add (omega3_switched_sifted_le_closed N δ s t _ W
    (fun _d hd => boxConvolutionSupport_pos (fun j p hp => (hW j p hp).pos) hd)) le_rfl

/-- Actual unswitched Omega3 and repeated-prime count feed the proved terminal.
No coprimality loss is suppressed, and the exceptional union is charged once. -/
theorem omega3_add_repeated_le_closed {i N : ℕ} {δ s t : ℝ} (W : Fin i → Finset ℕ)
    (hN : 4 ≤ N) (he : Even N) (hW : ∀ j p, p ∈ W j → p.Prime) :
    wuOmega3Sum N δ s t W+wuOmegaRepeatedSum N δ s t W ≤
    omega3SwitchedSiftedCountLE N δ s t (sqrt ((N : ℝ)^(1/2-δ))) W+
      HighCross.switchingLoss N δ s t W := by
  have hf := wuOmega3Sum_le_switched_add_badD_add_exceptional
    (δ := δ) (s := s) (t := t) (W := W) hN he
    (fun _d hd => boxConvolutionSupport_pos (fun j p hp => (hW j p hp).pos) hd)
  have hc := strict_add_loss_le_closed (N := N) (δ := δ) (s := s) (t := t) W hW
  unfold HighCross.switchingLoss at hc ⊢
  linarith

end
end HighO3
