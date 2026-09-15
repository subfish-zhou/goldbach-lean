import MathlibNt.Wu2008DoubleSieve.Gamma78GainCell

namespace Wu2008DoubleSieve

open Finset Set Real Filter
open scoped Classical Topology

/-- The inherited rectangle is used only for its geometric packing and
mass. Its fixed-cutoff H parameter is not the new variable-cutoff sample. -/
structure Gamma78GainRectangle (tri : Bool) where
  box : Gamma5GainRectangle
  firstUpper : box.B < gamma6BaseB
  secondLower : gamma78GainLower tri < box.C
  upper : box.D < gamma78GainUpper tri
  s : ℝ
  rightEnd : gamma78GainV box.A box.C < s
  parameter : s < 3

theorem gamma78Gain_rectangle_parameter {tri : Bool} (r : Gamma78GainRectangle tri) :
    r.s ∈ Icc (1 : ℝ) 3 := by
  have hreg : (r.box.A,r.box.C) ∈ gamma78GainRegion tri := by
    refine ⟨⟨r.box.lower.le,(r.box.first.trans r.firstUpper).le⟩,?_,(r.box.second.trans r.upper).le⟩
    cases tri
    · exact r.secondLower.le
    · exact (r.box.first.trans r.box.ordered).le
  exact ⟨((gamma78Gain_region_bounds hreg).2.2.2.2.2.2.2.2.1.trans r.rightEnd).le,r.parameter.le⟩

theorem gamma78Gain_ratio_drift_identity {R R₀ p q : ℝ}
    (hR : 1 < R) (hR₀ : 1 < R₀) (hp : 1 < p) :
    gamma78GainV (log p/log R) (log q/log R) =
      gamma78GainV (log p/log R₀) (log q/log R₀) +
        (log R/log R₀ - 1)/(log p/log R₀) := by
  unfold gamma78GainV
  field_simp [(log_pos hR).ne', (log_pos hR₀).ne', (log_pos hp).ne']
  ring

theorem gamma78Gain_ratio_drift {i k N p q : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) (hb : wuSourceBox k δ N i Δ V)
    (hΔ : 1 < Δ) (hR₀ : 1 < gamma5GainScale N δ V) {d : ℕ}
    (hd : d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V))
    (hp : 1 < p) (ht : gamma5MassA ≤ gamma5MassCoordinate (gamma5GainScale N δ V) p) :
    gamma78GainV (gamma5MassCoordinate ((N : ℝ)^(1/2-δ)/d) p)
        (gamma5MassCoordinate ((N : ℝ)^(1/2-δ)/d) q) ≤
      gamma78GainV (gamma5MassCoordinate (gamma5GainScale N δ V) p)
        (gamma5MassCoordinate (gamma5GainScale N δ V) q) +
        ((i : ℝ)*log Δ/log (gamma5GainScale N δ V))/gamma5MassA := by
  have hV : ∀ j, 0 < V j := fun j =>
    (rpow_pos_of_pos (by exact_mod_cast (show 0 < N by omega)) _).trans_le (hb.2.2.2.2.1 j)
  have hr := reboxing_support_level_bounds (Q := (N : ℝ)^(1/2-δ))
    (rpow_nonneg (Nat.cast_nonneg N) _) (by linarith : 0 < Δ) hV hd
  have hRd := (gamma5Mass_support_geometry hN hδ (by linarith) hb hd).2.2.1
  have hlo := log_le_log (by linarith : 0 < gamma5GainScale N δ V) hr.1
  have hhi := log_le_log (by linarith : 0 < (N : ℝ)^(1/2-δ)/d) hr.2
  change log ((N : ℝ)^(1/2-δ)/d) ≤ log (gamma5GainScale N δ V * Δ^i) at hhi
  rw [log_mul (by linarith : gamma5GainScale N δ V ≠ 0)
    (pow_pos (by linarith : 0 < Δ) i).ne',log_pow] at hhi
  have hlog := log_pos hR₀
  have hλ : log ((N : ℝ)^(1/2-δ)/d)/log (gamma5GainScale N δ V)-1 ≤
      (i : ℝ)*log Δ/log (gamma5GainScale N δ V) := by
    apply (le_of_mul_le_mul_right ?_ hlog)
    field_simp
    linarith
  have hλ0 : 0 ≤ log ((N : ℝ)^(1/2-δ)/d)/log (gamma5GainScale N δ V)-1 := by
    have hh := (le_div_iff₀ hlog).mpr hlo
    linarith
  have ha : 0 < gamma5MassA := by norm_num [gamma5MassA,gamma5ClassicalS]
  rw [show gamma78GainV (gamma5MassCoordinate ((N : ℝ)^(1/2-δ)/d) p)
      (gamma5MassCoordinate ((N : ℝ)^(1/2-δ)/d) q) =
      gamma78GainV (gamma5MassCoordinate (gamma5GainScale N δ V) p)
        (gamma5MassCoordinate (gamma5GainScale N δ V) q) +
        (log ((N : ℝ)^(1/2-δ)/d)/log (gamma5GainScale N δ V)-1) /
          gamma5MassCoordinate (gamma5GainScale N δ V) p from
    gamma78Gain_ratio_drift_identity hRd hR₀ (by exact_mod_cast hp)]
  exact add_le_add_left
    ((div_le_div_of_nonneg_left hλ0 ha ht).trans (div_le_div_of_nonneg_right hλ ha.le)) _

theorem gamma78Gain_rectangle_admission (k : ℕ) {δ : ℝ} {tri : Bool}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) (r : Gamma78GainRectangle tri) :
    ∀ᶠ N : ℕ in atTop, ∀ i : ℕ, ∀ Δ : ℝ, ∀ V : Fin i → ℝ,
      wuSourceBox k δ N i Δ V →
      1 < Δ ∧ 1 < gamma5GainScale N δ V ∧
      ∀ x ∈ boxConvolutionSupport (convolutionWuWindows N Δ V) ×ˢ
        (primeWindow N ((gamma5GainScale N δ V)^r.box.A) ((gamma5GainScale N δ V)^r.box.B) ×ˢ
         primeWindow N ((gamma5GainScale N δ V)^r.box.C) ((gamma5GainScale N δ V)^r.box.D)),
        x ∈ gamma78GainLabels tri N δ (convolutionWuWindows N Δ V) ∧
        gamma78GainV (gamma5MassCoordinate ((N : ℝ)^(1/2-δ)/x.1) x.2.1)
          (gamma5MassCoordinate ((N : ℝ)^(1/2-δ)/x.1) x.2.2) ≤ r.s := by
  let e := min (r.box.C-gamma78GainLower tri)
    (gamma5MassA*(r.s-gamma78GainV r.box.A r.box.C))
  have ha : 0 < gamma5MassA := by norm_num [gamma5MassA,gamma5ClassicalS]
  have he : 0 < e := lt_min (sub_pos.mpr r.secondLower) (mul_pos ha (sub_pos.mpr r.rightEnd))
  filter_upwards [gamma5Gain_rectangle_admission k hδ hδhi r.box,
    gamma5Gain_mesh_eventually k hδ hδhi he, eventually_ge_atTop (2 : ℕ)] with N had hm hN
  intro i Δ V hb
  have had := had i Δ V hb
  have hm := hm i Δ V hb
  refine ⟨had.1,had.2.1,?_⟩
  intro x hx
  have hxl := (had.2.2 x hx).1
  obtain ⟨hd,hp,hq,hpN,hqN,_hz,hpq,hqu⟩ :=
    (gamma5Classical_mem_labels_iff hN hδ (by linarith) hb x).mp hxl
  obtain ⟨_,hpw,hqw⟩ := mem_product.mp hx |>.imp_right mem_product.mp
  have hpc := gamma5Gain_window_coordinate had.2.1 hpw
  have hqc := gamma5Gain_window_coordinate had.2.1 hqw
  have hRd := (gamma5Mass_support_geometry hN hδ (by linarith) hb hd).2.2.1
  have hpow := rpow_le_rpow_of_exponent_le hRd.le (by norm_num [gamma5ClassicalB] : gamma5ClassicalB ≤ 1)
  rw [rpow_one] at hpow
  have hqR := hqu.le.trans hpow
  have hpR := (by exact_mod_cast hpq.le : (x.2.1 : ℝ) ≤ x.2.2).trans hqR
  have hpd := gamma5Gain_coordinate_drift hN hδ hδhi hb hd hp.one_le hpR
  have hqd := gamma5Gain_coordinate_drift hN hδ hδhi hb hd hq.one_le hqR
  have him : (i : ℝ) ≤ (k : ℝ)+1 := by exact_mod_cast hb.1.trans (Nat.le_succ k)
  have hmu : (i : ℝ)*log Δ/log (gamma5GainScale N δ V) ≤ e :=
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right him (log_pos had.1).le)
      (log_pos had.2.1).le).trans hm.2.2.le
  have hpb : gamma5MassCoordinate ((N : ℝ)^(1/2-δ)/x.1) x.2.1 < gamma6BaseB := by
    linarith [r.firstUpper]
  have hqU : gamma5MassCoordinate ((N : ℝ)^(1/2-δ)/x.1) x.2.2 < gamma78GainUpper tri := by
    linarith [r.upper]
  have hqL : gamma78GainLower tri ≤ gamma5MassCoordinate ((N : ℝ)^(1/2-δ)/x.1) x.2.2 := by
    have hh : e ≤ r.box.C-gamma78GainLower tri := min_le_left _ _
    linarith
  have hpm := gamma5Gain_coordinate_window hRd hp hpN
    (by linarith [hpc.1,hpd.2,hmu] : r.box.A-e ≤ gamma5MassCoordinate ((N : ℝ)^(1/2-δ)/x.1) x.2.1) hpb
  have hqm := gamma5Gain_coordinate_window hRd hq hqN hqL hqU
  refine ⟨mem_filter.mpr ⟨hxl,(mem_primeWindow.mp hpm).2.2.2,?_,(mem_primeWindow.mp hqm).2.2.2⟩,?_⟩
  · cases tri
    · exact (mem_primeWindow.mp hqm).2.2.1
    · trivial
  · have hdr := gamma78Gain_ratio_drift hN hδ hδhi hb had.1 had.2.1 hd hp.one_lt (r.box.lower.le.trans hpc.1)
    have han := gamma78Gain_V_antitone (ha.trans r.box.lower) hpc.1 hqc.1
      (hqc.2.le.trans (gamma5Gain_rectangle_bounds r.box).2.2.2.1.le)
    have he' : e/gamma5MassA ≤ r.s-gamma78GainV r.box.A r.box.C := by
      apply (div_le_iff₀ ha).mpr
      have hh : e ≤ gamma5MassA*(r.s-gamma78GainV r.box.A r.box.C) := min_le_right _ _
      linarith
    have hpay := div_le_div_of_nonneg_right hmu ha.le
    linarith

end Wu2008DoubleSieve
