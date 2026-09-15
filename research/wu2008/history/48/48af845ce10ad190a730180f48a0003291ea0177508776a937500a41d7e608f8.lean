import MathlibNt.Wu2008DoubleSieve.Gamma78GainGeometry

namespace Wu2008DoubleSieve

open Finset Set Real Filter
open scoped Classical Topology

theorem gamma78Gain_packing_actual (k : ℕ) {δ η : ℝ} {tri : Bool}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) (hη : 0 < η) (r : Gamma78GainRectangle tri) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ i : ℕ, ∀ Δ : ℝ, ∀ V : Fin i → ℝ, wuSourceBox k δ N i Δ V →
      gamma5GainPacking N δ Δ V r.box ⊆ gamma78GainLabels tri N δ (convolutionWuWindows N Δ V) ∧
      gamma78GainCount N (convolutionWuWindows N Δ V) (gamma5GainPacking N δ Δ V r.box) ≤
        (1 - wuImprovementLimit true δ r.s + η) *
          gamma5ClassicalMainMass N δ (convolutionWuWindows N Δ V) (gamma5GainPacking N δ Δ V r.box) := by
  obtain ⟨TC,hTC,hc⟩ := gamma78Gain_grid_comparison k hδ hδhi hη {r.s}
    (by intro s hs; have he : s = r.s := mem_singleton.mp hs; subst s
        exact gamma78Gain_rectangle_parameter r)
  obtain ⟨TA,ha⟩ := eventually_atTop.mp (gamma78Gain_rectangle_admission k hδ hδhi r)
  refine ⟨max TC TA,hTC.trans (le_max_left _ _),?_⟩
  intro N hN he i Δ V hb
  have hNC : TC ≤ N := (le_max_left _ _).trans hN
  have hh := ha N ((le_max_right _ _).trans hN) i Δ V hb
  have hsub := fun x hx => (hh.2.2 x (gamma5Gain_packing_coarse hh.2.1 hh.1 r.box hx)).1
  refine ⟨hsub,?_⟩
  let R := gamma5GainScale N δ V
  have hcell (j : ℕ) (hj : j < gamma5GainSize R Δ r.box.A r.box.B)
      (l : ℕ) (hl : l < gamma5GainSize R Δ r.box.C r.box.D) :
      gamma78GainCount N (convolutionWuWindows N Δ V)
        (gamma5GainCell N Δ (gamma5GainEnd R Δ r.box.A j) (gamma5GainEnd R Δ r.box.C l)
          (convolutionWuWindows N Δ V)) ≤
      (1 - wuImprovementLimit true δ r.s + η) *
        gamma5ClassicalMainMass N δ (convolutionWuWindows N Δ V)
          (gamma5GainCell N Δ (gamma5GainEnd R Δ r.box.A j) (gamma5GainEnd R Δ r.box.C l)
            (convolutionWuWindows N Δ V)) := by
    have hp := gamma5Gain_point_bounds hh.2.1 hh.1 r.box.first.le hj
    have hq := gamma5Gain_point_bounds hh.2.1 hh.1 r.box.second.le hl
    have hpm := (gamma5Gain_point_strictMono hh.2.1 hh.1 r.box.A).monotone (Nat.le_succ j)
    have hqm := (gamma5Gain_point_strictMono hh.2.1 hh.1 r.box.C).monotone (Nat.le_succ l)
    have had := gamma5Gain_endpoint_admission hh.2.1 r.box
      ⟨hp.1.trans hpm,hp.2⟩ ⟨hq.1.trans hqm,hq.2⟩
    have hcoarse : gamma5GainCell N Δ (gamma5GainEnd R Δ r.box.A j) (gamma5GainEnd R Δ r.box.C l)
        (convolutionWuWindows N Δ V) ⊆
        boxConvolutionSupport (convolutionWuWindows N Δ V) ×ˢ
          (primeWindow N (R^r.box.A) (R^r.box.B) ×ˢ primeWindow N (R^r.box.C) (R^r.box.D)) := by
      intro x hx
      obtain ⟨hd,hpq⟩ := mem_product.mp hx
      obtain ⟨hpx,hqx⟩ := mem_product.mp hpq
      exact mem_product.mpr ⟨hd,mem_product.mpr
        ⟨gamma5Gain_micro_window hh.2.1 hh.1 r.box.first.le hj N hpx,
          gamma5Gain_micro_window hh.2.1 hh.1 r.box.second.le hl N hqx⟩⟩
    have heq : (N : ℝ)^(1/2-δ)/((∏ j,V j)*gamma5GainEnd R Δ r.box.C l) =
        R/gamma5GainEnd R Δ r.box.C l := by dsimp [R,gamma5GainScale]; ring
    exact hc N hNC he r.s (mem_singleton_self _) i Δ _ _ V hb had.1 had.2.1
      (by rw [heq]; exact had.2.2.1) (by rw [heq]; exact had.2.2.2)
      (fun x hx => (mem_filter.mp (hh.2.2 x (hcoarse hx)).1).1)
      (fun x hx => (hh.2.2 x (hcoarse hx)).2)
  unfold gamma78GainCount gamma5ClassicalMainMass
  rw [gamma5Gain_packing_sum hh.2.1 hh.1,gamma5Gain_packing_sum hh.2.1 hh.1]
  simp only [mul_sum]
  apply sum_le_sum
  intro j hj
  apply sum_le_sum
  intro l hl
  simpa only [gamma78GainCount,gamma5ClassicalMainMass,mul_sum] using
    hcell j (mem_range.mp hj) l (mem_range.mp hl)

end Wu2008DoubleSieve
