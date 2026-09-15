import BuchstabCountActual

namespace BuchstabCount
open Finset Real Wu2008DoubleSieve HighBoxRecovery
open scoped Classical
noncomputable section

/-- The existing classical endpoint lower, with its full logarithmic
remainder absorbed into the true original Theta. This is an actual count
producer, not a lower bound for an upper Rosser main term. -/
theorem classical_three_lower {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 50*highEta) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N → ∀ Δ : ℝ,
      1+log (N : ℝ)^(-4 : ℝ) ≤ Δ → Δ < 1+2*log (N : ℝ)^(-4 : ℝ) →
      ∀ V : Fin 2 → ℝ, (∀ j, (N : ℝ)^(100/1327 : ℝ) ≤ V j) → OriginalRectangles N V →
      (log 2-ε)*boxTheta N ((N : ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) ≤
        wuBoxPhi N δ (convolutionWuWindows N Δ V) 3 := by
  let e : ℝ := min 1 (ε/8)
  have he : 0 < e := lt_min (by norm_num) (by positivity)
  have he1 : e ≤ 1 := min_le_left _ _
  have heε : e ≤ ε/8 := min_le_right _ _
  obtain ⟨C,_,T0,hT04,hlower⟩ := HighOmega2.original_inserted_lower hδ hδhi he he1
  obtain ⟨T1,_,hpay⟩ := ActualLogGain.original_remainder_relative C hδ hδhi
    (show 0 < ε/2 by positivity)
  refine ⟨max T0 T1,hT04.trans (le_max_left _ _),?_⟩
  intro N hN heven Δ hlo hhi V hV hrect
  have hN0 : T0 ≤ N := by omega
  have hN1 : T1 ≤ N := by omega
  have hl := (hlower N hN0 heven Δ hlo hhi V hV hrect 3 (by norm_num) (by norm_num)).1.1
  obtain ⟨hθ,hr⟩ := hpay N hN1 Δ hlo hhi V hV hrect
  norm_num only [show (3 : ℝ)-1=2 by norm_num] at hl
  have heBudget : (4*e+ε/2)*boxTheta N ((N : ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) ≤
      ε*boxTheta N ((N : ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) :=
    mul_le_mul_of_nonneg_right (by linarith only [heε]) hθ.le
  nlinarith only [hl,hr,heBudget]

/-- Complete original Buchstab lower from the actually paid inserted H.
All original boxes use the same positive delta; the common threshold is
chosen before N, Delta, endpoints, s, and the symbolic grid terminal r.
The literal parent coverTheta includes every occupied endpoint cell. -/
theorem original_lower {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 50*highEta) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N → ∀ Δ : ℝ,
      1+log (N : ℝ)^(-4 : ℝ) ≤ Δ → Δ < 1+2*log (N : ℝ)^(-4 : ℝ) →
      ∀ V : Fin 2 → ℝ, (∀ j, (N : ℝ)^(100/1327 : ℝ) ≤ V j) → OriginalRectangles N V →
      ∀ s : ℝ, 2 ≤ s → s ≤ 29/10 → ∀ r : ℕ,
      (reboxingAlpha ((N : ℝ)^(1/2-δ)/(∏ l, V l)) Δ 3 r ≤
        ((N : ℝ)^(1/2-δ)/(∏ l, V l))^(1/s) ∧
      ((N : ℝ)^(1/2-δ)/(∏ l, V l))^(1/s) <
        reboxingAlpha ((N : ℝ)^(1/2-δ)/(∏ l, V l)) Δ 3 (r+1)) →
      (log 2-ε)*boxTheta N ((N : ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) -
        (1-1/10000)*InsertedGain.coverTheta N δ Δ V s r ≤
          wuBoxPhi N δ (convolutionWuWindows N Δ V) s := by
  obtain ⟨T0,hT04,hclassical⟩ := classical_three_lower hδ hδhi hε
  obtain ⟨T1,_,htail⟩ := occupied_tail_paid hδ hδhi
  refine ⟨max T0 T1,hT04.trans (le_max_left _ _),?_⟩
  intro N hN he Δ hlo hhi V hV hrect s hs hsmax r hr
  have hN0 : T0 ≤ N := by omega
  have hN1 : T1 ≤ N := by omega
  have hc := hclassical N hN0 he Δ hlo hhi V hV hrect
  have ht := htail N hN1 he Δ hlo hhi V hV hrect s hs hsmax r hr.2
  linarith only [hc,ht]

end
end BuchstabCount
