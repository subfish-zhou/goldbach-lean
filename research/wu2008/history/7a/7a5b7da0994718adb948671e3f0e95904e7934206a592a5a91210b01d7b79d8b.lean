import MathlibNt.Wu2008DoubleSieve.Gamma5GainAdmission

/-!
# Constructed complete-box packings and their actual H comparison
-/

namespace Wu2008DoubleSieve

open Finset Set Real Filter
open scoped Classical Topology

theorem gamma5Gain_window_mono (N : ℕ) {a b c d : ℝ} (ha : a ≤ b) (hd : c ≤ d) :
    primeWindow N b c ⊆ primeWindow N a d := by
  intro p hp
  obtain ⟨hp, hc, hlo, hhi⟩ := mem_primeWindow.mp hp
  exact mem_primeWindow.mpr ⟨hp, hc, ha.trans hlo, hhi.trans_le hd⟩

theorem gamma5Gain_micro_window {R Δ A B : ℝ} {j : ℕ}
    (hR : 1 < R) (hΔ : 1 < Δ) (hAB : A ≤ B) (hj : j < gamma5GainSize R Δ A B) (N : ℕ) :
    primeWindow N (gamma5GainEnd R Δ A j / Δ) (gamma5GainEnd R Δ A j) ⊆
      primeWindow N (R ^ A) (R ^ B) := by
  have hp := gamma5Gain_point_bounds hR hΔ hAB hj
  rw [gamma5Gain_end_lower hR hΔ, gamma5GainEnd]
  exact gamma5Gain_window_mono N
    (rpow_le_rpow_of_exponent_le hR.le hp.1)
    (rpow_le_rpow_of_exponent_le hR.le hp.2)

theorem gamma5Gain_packing_coarse {i N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hR : 1 < gamma5GainScale N δ V) (hΔ : 1 < Δ) (r : Gamma5GainRectangle) :
    gamma5GainPacking N δ Δ V r ⊆
      boxConvolutionSupport (convolutionWuWindows N Δ V) ×ˢ
        (primeWindow N ((gamma5GainScale N δ V) ^ r.A) ((gamma5GainScale N δ V) ^ r.B) ×ˢ
        primeWindow N ((gamma5GainScale N δ V) ^ r.C) ((gamma5GainScale N δ V) ^ r.D)) := by
  intro x hx
  obtain ⟨hd, hpq⟩ := mem_product.mp hx
  obtain ⟨hp, hq⟩ := mem_product.mp hpq
  exact mem_product.mpr ⟨hd, mem_product.mpr ⟨
    gamma5Gain_window_mono N le_rfl (rpow_le_rpow_of_exponent_le hR.le
      (gamma5Gain_terminal_bounds hR hΔ r.first.le).2.1) hp,
    gamma5Gain_window_mono N le_rfl (rpow_le_rpow_of_exponent_le hR.le
      (gamma5Gain_terminal_bounds hR hΔ r.second.le).2.1) hq⟩⟩

theorem gamma5Gain_rectangle_admission (k : ℕ) {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) (r : Gamma5GainRectangle) :
    ∀ᶠ N : ℕ in atTop, ∀ i : ℕ, ∀ Δ : ℝ, ∀ V : Fin i → ℝ,
      wuSourceBox k δ N i Δ V →
      1 < Δ ∧ 1 < gamma5GainScale N δ V ∧
      ∀ x ∈ boxConvolutionSupport (convolutionWuWindows N Δ V) ×ˢ
        (primeWindow N ((gamma5GainScale N δ V) ^ r.A) ((gamma5GainScale N δ V) ^ r.B) ×ˢ
        primeWindow N ((gamma5GainScale N δ V) ^ r.C) ((gamma5GainScale N δ V) ^ r.D)),
        x ∈ gamma5ClassicalLabels N δ (convolutionWuWindows N Δ V) ∧
        gamma5GainV
          (gamma5MassCoordinate ((N : ℝ) ^ (1 / 2 - δ) / x.1) x.2.1)
          (gamma5MassCoordinate ((N : ℝ) ^ (1 / 2 - δ) / x.1) x.2.2) ≤ r.s := by
  let e := min (r.A - gamma5MassA) ((r.s - gamma5GainV r.A r.C) / (2 * gamma5ClassicalS))
  have hS : 0 < gamma5ClassicalS := by norm_num [gamma5ClassicalS]
  have he : 0 < e := lt_min (sub_pos.mpr r.lower) (div_pos (sub_pos.mpr r.rightEnd) (by positivity))
  filter_upwards [gamma5Gain_mesh_eventually k hδ hδhi he, eventually_ge_atTop (2 : ℕ)]
    with N hm hN
  intro i Δ V hb
  have hh := hm i Δ V hb
  refine ⟨hh.1, hh.2.1, ?_⟩
  intro x hx
  obtain ⟨hd, hpq⟩ := mem_product.mp hx
  obtain ⟨hp, hq⟩ := mem_product.mp hpq
  have him : (i : ℝ) ≤ (k : ℝ) + 1 := by exact_mod_cast (show i ≤ k + 1 by omega)
  have hstep : 0 ≤ gamma5GainStep (gamma5GainScale N δ V) Δ :=
    (gamma5Gain_step_pos hh.2.1 hh.1).le
  have hmesh : (i : ℝ) * gamma5GainStep (gamma5GainScale N δ V) Δ ≤ e :=
    (mul_le_mul_of_nonneg_right him hstep).trans (by
      simpa only [gamma5GainStep, mul_div_assoc] using hh.2.2.le)
  exact gamma5Gain_coarse_label hN hδ hδhi hb hh.2.1 hh.1 r (min_le_left _ _)
    (by have h := min_le_right (r.A - gamma5MassA)
          ((r.s - gamma5GainV r.A r.C) / (2 * gamma5ClassicalS))
        exact (mul_comm _ _).le.trans ((le_div_iff₀ (by positivity)).mp h))
    hmesh hd hp hq

theorem gamma5Gain_packing_actual (k : ℕ) {δ η : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) (hη : 0 < η) (r : Gamma5GainRectangle) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ i : ℕ, ∀ Δ : ℝ, ∀ V : Fin i → ℝ, wuSourceBox k δ N i Δ V →
      gamma5GainPacking N δ Δ V r ⊆ gamma5ClassicalLabels N δ (convolutionWuWindows N Δ V) ∧
      gamma5ClassicalCount N δ (convolutionWuWindows N Δ V) (gamma5GainPacking N δ Δ V r) ≤
        (1 - wuImprovementLimit true δ r.s + η) *
          gamma5ClassicalMainMass N δ (convolutionWuWindows N Δ V) (gamma5GainPacking N δ Δ V r) := by
  have hr := gamma5Gain_rectangle_bounds r
  obtain ⟨TC, hTC, hc⟩ := gamma5Gain_grid_comparison k hδ hδhi hη {r.s}
    (by intro s hs; have he : s = r.s := mem_singleton.mp hs; subst s; exact ⟨hr.2.2.2.2.2.1.le, r.parameter.le⟩)
  obtain ⟨TA, ha⟩ := eventually_atTop.mp (gamma5Gain_rectangle_admission k hδ hδhi r)
  refine ⟨max TC TA, hTC.trans (le_max_left _ _), ?_⟩
  intro N hN he i Δ V hb
  have hNC : TC ≤ N := (le_max_left _ _).trans hN
  have hh := ha N ((le_max_right _ _).trans hN) i Δ V hb
  have hN4 : 4 ≤ N := hTC.trans hNC
  have hsub := fun x hx => (hh.2.2 x (gamma5Gain_packing_coarse hh.2.1 hh.1 r hx)).1
  refine ⟨hsub, ?_⟩
  let R := gamma5GainScale N δ V
  have hcell (j : ℕ) (hj : j < gamma5GainSize R Δ r.A r.B)
      (l : ℕ) (hl : l < gamma5GainSize R Δ r.C r.D) :
      gamma5ClassicalCount N δ (convolutionWuWindows N Δ V)
        (gamma5GainCell N Δ (gamma5GainEnd R Δ r.A j) (gamma5GainEnd R Δ r.C l)
          (convolutionWuWindows N Δ V)) ≤
      (1 - wuImprovementLimit true δ r.s + η) *
        gamma5ClassicalMainMass N δ (convolutionWuWindows N Δ V)
          (gamma5GainCell N Δ (gamma5GainEnd R Δ r.A j) (gamma5GainEnd R Δ r.C l)
            (convolutionWuWindows N Δ V)) := by
    have hp := gamma5Gain_point_bounds hh.2.1 hh.1 r.first.le hj
    have hq := gamma5Gain_point_bounds hh.2.1 hh.1 r.second.le hl
    have hpm := (gamma5Gain_point_strictMono hh.2.1 hh.1 r.A).monotone (Nat.le_succ j)
    have hqm := (gamma5Gain_point_strictMono hh.2.1 hh.1 r.C).monotone (Nat.le_succ l)
    have had := gamma5Gain_endpoint_admission hh.2.1 r ⟨hp.1.trans hpm, hp.2⟩ ⟨hq.1.trans hqm, hq.2⟩
    have hcoarse : gamma5GainCell N Δ (gamma5GainEnd R Δ r.A j) (gamma5GainEnd R Δ r.C l)
        (convolutionWuWindows N Δ V) ⊆
        boxConvolutionSupport (convolutionWuWindows N Δ V) ×ˢ
          (primeWindow N (R ^ r.A) (R ^ r.B) ×ˢ primeWindow N (R ^ r.C) (R ^ r.D)) := by
      intro x hx
      obtain ⟨hd, hpq⟩ := mem_product.mp hx
      obtain ⟨hpx, hqx⟩ := mem_product.mp hpq
      exact mem_product.mpr ⟨hd, mem_product.mpr
        ⟨gamma5Gain_micro_window hh.2.1 hh.1 r.first.le hj N hpx,
          gamma5Gain_micro_window hh.2.1 hh.1 r.second.le hl N hqx⟩⟩
    have heq : (N : ℝ) ^ (1 / 2 - δ) / ((∏ j, V j) * gamma5GainEnd R Δ r.C l) =
        R / gamma5GainEnd R Δ r.C l := by dsimp [R, gamma5GainScale]; ring
    exact hc N hNC he r.s (mem_singleton_self _) i Δ _ _ V hb had.1 had.2.1
      (by rw [heq]; exact had.2.2.1) (by rw [heq]; exact had.2.2.2)
      (fun x hx => (hh.2.2 x (hcoarse hx)).1) (fun x hx => (hh.2.2 x (hcoarse hx)).2)
  unfold gamma5ClassicalCount gamma5ClassicalMainMass
  rw [gamma5Gain_packing_sum hh.2.1 hh.1]
  rw [gamma5Gain_packing_sum hh.2.1 hh.1]
  simp only [mul_sum]
  exact sum_le_sum (fun j hj => sum_le_sum (fun l hl => hcell j (mem_range.mp hj) l (mem_range.mp hl)))

end Wu2008DoubleSieve
