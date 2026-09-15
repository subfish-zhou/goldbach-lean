import HighThetaEndpoints

namespace HighTheta
open Finset Real Wu2008DoubleSieve HighBoxRecovery Filter
open scoped Classical Topology
noncomputable section

/-- The literal complete R1 and R2, paid against genuine boxTheta. -/
def RelativeRemainders {i : ℕ} (N : ℕ) (δ ε s t : ℝ) (W : Fin i → Finset ℕ) : Prop :=
  let Q := (N : ℝ)^(1/2-δ)
  omega3SieveR1 N (⌊Q⌋₊+1) δ s t (sqrt Q) W +
    omega3SieveR2 N (⌊Q⌋₊+1) δ s t (sqrt Q) W ≤ ε*boxTheta N Q W

/-- One threshold before all original rectangles and all actual occupied
insertions. No endpoint or balanced-profile hypothesis remains. -/
theorem original_and_inserted_relative {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 50*highEta) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ Δ : ℝ,
      1+log (N : ℝ)^(-4 : ℝ) ≤ Δ → Δ < 1+2*log (N : ℝ)^(-4 : ℝ) →
      ∀ V : Fin 2 → ℝ, (∀ j, (N : ℝ)^(100/1327 : ℝ) ≤ V j) → OriginalRectangles N V →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → t ≤ 10 →
        RelativeRemainders N δ ε s t (convolutionWuWindows N Δ V) ∧
        ∀ U : ℝ, ActualInsertion N δ Δ U V →
          RelativeRemainders N δ ε s t (convolutionWuWindows N Δ (Fin.cons U V)) := by
  have hη : 0 < highEta := by norm_num [highEta]
  have hδhalf : δ < 1/2 := lt_of_le_of_lt hδhi (by norm_num [highEta])
  obtain ⟨T1,hT14,hpay⟩ := remainders_relative hδ hδhalf hη hε
  obtain ⟨T2,hsmall⟩ := eventually_atTop.mp delta_eventually_small
  refine ⟨max T1 T2,hT14.trans (le_max_left _ _),?_⟩
  intro N hN Δ hlo hhi V hV hrect s t hs hst ht
  have hN1 := (le_max_left T1 T2).trans hN
  have hN2 := (le_max_right T1 T2).trans hN
  have hN4 := hT14.trans hN1
  obtain ⟨hΔ,hΔhi⟩ := hsmall N hN2 Δ hlo hhi
  have he := original_endpoints (show 2 ≤ N by omega) hV hrect
  have hg := original_box_geometry (show 2 ≤ N by omega) hδhi hΔ hΔhi hV hrect
  refine ⟨hpay N hN1 2 (by norm_num) Δ hlo hhi V he.1 he.2 hg.1 hg.2 s t hs hst ht, ?_⟩
  intro U hw
  have hie := inserted_endpoints (show 2 ≤ N by omega) hδ.le hδhi hΔ hΔhi hV hrect hw
  have hig := inserted_box_geometry (show 2 ≤ N by omega) hδhi hΔ hΔhi hV hrect hw
  exact hpay N hN1 3 le_rfl Δ hlo hhi (Fin.cons U V) hie.1 hie.2 hig.1 hig.2 s t hs hst ht

end
end HighTheta
