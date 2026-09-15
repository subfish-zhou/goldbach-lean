import MathlibNt.Wu2008DoubleSieve.MotherPairGainGeometry

namespace Wu2008DoubleSieve.MotherPair
open Finset Set Real Filter
open scoped Classical Topology

/-- One threshold controls every original source factor and every physical microcell. -/
theorem rectangle_admission (p : SecondFunctionalParameters) (h : AnalyticParameters p)
    (j : Term) (r : GainRectangle p j) (k : ℕ) {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1/10) :
    ∀ᶠ N : ℕ in atTop, ∀ i : ℕ, ∀ Δ : ℝ, ∀ V : Fin i → ℝ,
      wuSourceBox k δ N i Δ V →
      1 < gamma5GainScale N δ V ∧ ∀ P Q : ℝ,
      (gamma5GainScale N δ V)^r.A ≤ P → P ≤ (gamma5GainScale N δ V)^r.B →
      (gamma5GainScale N δ V)^r.C ≤ Q → Q ≤ (gamma5GainScale N δ V)^r.D →
      gamma5GainCell N Δ P Q (convolutionWuWindows N Δ V) ⊆
        termLabels p j N δ (convolutionWuWindows N Δ V) ∧
      ∀ x ∈ gamma5GainCell N Δ P Q (convolutionWuWindows N Δ V),
        Hratio p j (gamma5MassCoordinate ((N:ℝ)^(1/2-δ)/x.1) x.2.1)
          (gamma5MassCoordinate ((N:ℝ)^(1/2-δ)/x.1) x.2.2) ≤ r.sample := by
  obtain ⟨e,he,hratio⟩ := ratio_margin p h j r
  let ε := min e (min (r.A-1/p.S) (min (r.C-lowerQ p j) (r.C-r.B)))
  have hε : 0 < ε := lt_min he (lt_min (sub_pos.mpr r.lowerP_lt_A)
    (lt_min (sub_pos.mpr r.lowerQ_lt_C) (sub_pos.mpr r.B_lt_C)))
  have hεe : ε ≤ e := min_le_left _ _
  have hεA : ε ≤ r.A-1/p.S := (min_le_right _ _).trans (min_le_left _ _)
  have hεC : ε ≤ r.C-lowerQ p j :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hεgap : ε ≤ r.C-r.B :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hD : r.D ≤ 1 := by linarith [r.twiceD_lt_one]
  have hB : r.B ≤ 1 := by linarith [r.B_lt_C,r.C_lt_D]
  filter_upwards [gamma5Gain_mesh_eventually k hδ hδhi hε,
    eventually_ge_atTop (2:ℕ)] with N hm hN
  intro i Δ V hb
  obtain ⟨hΔ,hR,hmesh⟩ := hm i Δ V hb
  refine ⟨hR,?_⟩
  intro P Q hPA hPB hQC hQD
  have point (x : Gamma5ClassicalLabel)
      (hx : x ∈ gamma5GainCell N Δ P Q (convolutionWuWindows N Δ V)) :
      x ∈ termLabels p j N δ (convolutionWuWindows N Δ V) ∧
      Hratio p j (gamma5MassCoordinate ((N:ℝ)^(1/2-δ)/x.1) x.2.1)
        (gamma5MassCoordinate ((N:ℝ)^(1/2-δ)/x.1) x.2.2) ≤ r.sample := by
    obtain ⟨hd,hpq⟩ := mem_product.mp hx
    obtain ⟨hp,hq⟩ := mem_product.mp hpq
    have hpc := micro_source_coordinate hN hδ hδhi hb hR hΔ hB hPA hPB hd hp
    have hqc := micro_source_coordinate hN hδ hδhi hb hR hΔ hD hQC hQD hd hq
    have hp' := mem_primeWindow.mp hp
    have hq' := mem_primeWindow.mp hq
    have hRd := (gamma5Mass_support_geometry hN hδ (by linarith) hb hd).2.2.1
    have hpa : 1/p.S ≤ gamma5MassCoordinate ((N:ℝ)^(1/2-δ)/x.1) x.2.1 := by
      linarith [hpc.1]
    have hqa : lowerQ p j ≤ gamma5MassCoordinate ((N:ℝ)^(1/2-δ)/x.1) x.2.2 := by
      linarith [hqc.1]
    have hpw := mem_primeWindow.mp (gamma5Gain_coordinate_window hRd hp'.1 hp'.2.1 hpa hpc.2)
    have hqw := mem_primeWindow.mp (gamma5Gain_coordinate_window hRd hq'.1 hq'.2.1 hqa hqc.2)
    have hpN : x.2.1 < N+1 := by
      have hz := cutoff_le_N hN hδ (by linarith) hb hB hd
      have hh : (x.2.1:ℝ) ≤ N := hpw.2.2.2.le.trans hz
      have hn : x.2.1 ≤ N := by exact_mod_cast hh
      omega
    have hqN : x.2.2 < N+1 := by
      have hz := cutoff_le_N hN hδ (by linarith) hb hD hd
      have hh : (x.2.2:ℝ) ≤ N := hqw.2.2.2.le.trans hz
      have hn : x.2.2 ≤ N := by exact_mod_cast hh
      omega
    have hpq' : x.2.1 < x.2.2 := by
      by_contra hn
      have hn' : (x.2.2:ℝ) ≤ x.2.1 := by exact_mod_cast (not_lt.mp hn)
      have hl := div_le_div_of_nonneg_right
        (log_le_log (by exact_mod_cast hq'.1.pos) hn') (log_pos hRd).le
      change gamma5MassCoordinate ((N:ℝ)^(1/2-δ)/x.1) x.2.2 ≤
        gamma5MassCoordinate ((N:ℝ)^(1/2-δ)/x.1) x.2.1 at hl
      linarith [hpc.2,hqc.1]
    constructor
    · rw [termLabels_eq_rect]
      apply mem_filter.mpr
      refine ⟨mem_product.mpr ⟨hd,mem_product.mpr ⟨mem_range.mpr hpN,mem_range.mpr hqN⟩⟩,
        hp'.1,hq'.1,hp'.2.1,hq'.2.1,hpw.2.2.1,?_,hqw.2.2.1,?_,hpq'⟩
      · exact hpw.2.2.2.trans_le (rpow_le_rpow_of_exponent_le hRd.le r.B_lt_upperP.le)
      · exact hqw.2.2.2.trans_le (rpow_le_rpow_of_exponent_le hRd.le r.D_lt_upperQ.le)
    · apply hratio
      · linarith [hpc.1]
      · linarith [hqc.1]
  exact ⟨fun x hx => (point x hx).1, fun x hx => (point x hx).2⟩

end Wu2008DoubleSieve.MotherPair
