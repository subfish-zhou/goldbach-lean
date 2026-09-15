import MathlibNt.Wu2008DoubleSieve.Gamma78GainIntegral

namespace Wu2008DoubleSieve

open Finset Set Real Filter
open scoped Classical Topology

theorem gamma78Gain_labels_sub_rectangle {i k N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1/2)
    (hb : wuSourceBox k δ N i Δ V) (tri : Bool) :
    gamma78GainLabels tri N δ (convolutionWuWindows N Δ V) ⊆
      gamma5MassRectLabels N δ (convolutionWuWindows N Δ V)
        gamma5MassA gamma6BaseB (gamma78GainLower tri) (gamma78GainUpper tri) := by
  intro x hx
  obtain ⟨hxl,hpu,hql,hqu⟩ := mem_filter.mp hx
  obtain ⟨hd,hp,hq,hpN,hqN,hpl,hpq,_⟩ :=
    (gamma5Classical_mem_labels_iff hN hδ hδhi hb x).mp hxl
  have hR := (gamma5Mass_support_geometry hN hδ hδhi hb hd).2.2.1
  have hpc := gamma5Gain_window_coordinate hR
    (mem_primeWindow.mpr ⟨hp,hpN,hpl,hpu⟩)
  have hqlo : ((N : ℝ)^(1/2-δ)/x.1)^(gamma78GainLower tri) ≤ (x.2.2 : ℝ) := by
    cases tri
    · exact hql
    · exact hpl.trans (by exact_mod_cast hpq.le)
  have hqc := gamma5Gain_window_coordinate hR (mem_primeWindow.mpr ⟨hq,hqN,hqlo,hqu⟩)
  exact mem_filter.mpr ⟨hxl,hpc.1,hpc.2.le,hqc.1,hqc.2.le⟩

/-- Endpoint atoms are retained in the closed rectangle used for the upper mass. -/
theorem gamma78Gain_full_mass_upper (tri : Bool) (k : ℕ) (hk : 1 ≤ k) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1/10) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ i : ℕ, ∀ Δ : ℝ, ∀ V : Fin i → ℝ, wuSourceBox k δ N i Δ V →
      gamma5ClassicalMainMass N δ (convolutionWuWindows N Δ V)
        (gamma78GainLabels tri N δ (convolutionWuWindows N Δ V)) ≤
      (gamma78GainC tri + ε) *
        boxTheta N ((N : ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) := by
  obtain ⟨T,hT,hm⟩ := gamma5Mass_rectangle_mass k hk hδ hδhi hε
  refine ⟨T,hT,?_⟩
  intro N hN i Δ V hb
  have hbds := gamma78Gain_constants tri
  have hh := hm N hN i Δ V hb gamma5MassA gamma6BaseB
    (gamma78GainLower tri) (gamma78GainUpper tri)
    le_rfl hbds.1.le hbds.2.1.le hbds.2.2.1 hbds.2.2.2.1.le hbds.2.2.2.2.2
  rw [gamma78Gain_C_rectangle] at hh
  have hmono := gamma5Gain_mass_mono (by omega : 2 ≤ N) hδ (by linarith) hb
    (gamma78Gain_labels_sub_rectangle (by omega) hδ (by linarith) hb tri)
    (filter_subset _ _)
  have hupper := (le_abs_self _).trans hh
  nlinarith

end Wu2008DoubleSieve
