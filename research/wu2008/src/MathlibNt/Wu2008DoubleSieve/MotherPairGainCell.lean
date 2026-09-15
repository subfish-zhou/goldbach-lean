import MathlibNt.Wu2008DoubleSieve.MotherPairGainAdmission

namespace Wu2008DoubleSieve.MotherPair
open Finset Set Real Filter
open scoped Classical Topology

/-- A fixed strict mother rectangle yields the actual sorted H improvement for
all physical microcells after one threshold. No admission or ratio hypothesis
is exposed by this terminal, and the returned count is the original termCount. -/
theorem rectangle_cell_upper (p : SecondFunctionalParameters) (h : AnalyticParameters p)
    (j : Term) (r : GainRectangle p j) (k : ℕ) {δ η : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1/10) (hη : 0 < η) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ i : ℕ, ∀ Δ : ℝ, ∀ V : Fin i → ℝ,
      wuSourceBox k δ N i Δ V → ∀ P Q : ℝ,
      ((N:ℝ)^(1/2-δ)/(∏ a, V a))^r.A ≤ P →
      P ≤ ((N:ℝ)^(1/2-δ)/(∏ a, V a))^r.B →
      ((N:ℝ)^(1/2-δ)/(∏ a, V a))^r.C ≤ Q →
      Q ≤ ((N:ℝ)^(1/2-δ)/(∏ a, V a))^r.D →
      gamma5GainCell N Δ P Q (convolutionWuWindows N Δ V) ⊆
        termLabels p j N δ (convolutionWuWindows N Δ V) ∧
      termCount p j N δ (convolutionWuWindows N Δ V)
        (gamma5GainCell N Δ P Q (convolutionWuWindows N Δ V)) ≤
      (1-wuImprovementLimit true δ r.sample+η)*gamma5ClassicalMainMass N δ
        (convolutionWuWindows N Δ V) (gamma5GainCell N Δ P Q (convolutionWuWindows N Δ V)) := by
  obtain ⟨T,hT4,hT⟩ := gain_grid_comparison p h j k hδ hδhi hη r.sample
    ⟨r.sample_lower.le,r.sample_upper.le⟩
  obtain ⟨Tg,hTg⟩ := eventually_atTop.mp (rectangle_admission p h j r k hδ hδhi)
  refine ⟨max T Tg,hT4.trans (le_max_left _ _),?_⟩
  intro N hN he i Δ V hb P Q hPA hPB hQC hQD
  have hg := hTg N ((le_max_right _ _).trans hN) i Δ V hb
  obtain ⟨hsub,hRatio⟩ := hg.2 P Q hPA hPB hQC hQD
  have hslots := rectangle_sorted_slots p h j r hg.1 hPA hPB hQC hQD
  have heq : gamma5GainScale N δ V/Q = (N:ℝ)^(1/2-δ)/((∏ a, V a)*Q) := by
    unfold gamma5GainScale
    ring
  rw [heq] at hslots
  exact ⟨hsub,hT N ((le_max_left _ _).trans hN) he i Δ P Q V hb
    hslots.1 hslots.2.1 hslots.2.2.1 hslots.2.2.2 hsub hRatio⟩

end Wu2008DoubleSieve.MotherPair
