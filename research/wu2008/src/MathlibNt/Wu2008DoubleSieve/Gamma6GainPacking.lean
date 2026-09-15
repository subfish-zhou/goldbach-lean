import MathlibNt.Wu2008DoubleSieve.Gamma6GainCell

namespace Wu2008DoubleSieve

open Finset Set Real Filter
open scoped Classical Topology

noncomputable def gamma6GainPacking {i : ℕ} (N : ℕ) (δ Δ : ℝ) (V : Fin i → ℝ)
    (r : Gamma6GainRectangle) : Finset Gamma5ClassicalLabel :=
  boxConvolutionSupport (convolutionWuWindows N Δ V) ×ˢ
    (primeWindow N ((gamma5GainScale N δ V) ^ r.A)
      ((gamma5GainScale N δ V) ^ gamma5GainTerminal (gamma5GainScale N δ V) Δ r.A r.B) ×ˢ
    primeWindow N ((gamma5GainScale N δ V) ^ r.C)
      ((gamma5GainScale N δ V) ^ gamma5GainTerminal (gamma5GainScale N δ V) Δ r.C r.D))

theorem gamma6Gain_packing_sum {i N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hR : 1 < gamma5GainScale N δ V) (hΔ : 1 < Δ) (r : Gamma6GainRectangle)
    (f : Gamma5ClassicalLabel → ℝ) :
    (∑ x ∈ gamma6GainPacking N δ Δ V r, f x) =
      ∑ j ∈ range (gamma5GainSize (gamma5GainScale N δ V) Δ r.A r.B),
        ∑ l ∈ range (gamma5GainSize (gamma5GainScale N δ V) Δ r.C r.D),
          ∑ x ∈ gamma5GainCell N Δ
            (gamma5GainEnd (gamma5GainScale N δ V) Δ r.A j)
            (gamma5GainEnd (gamma5GainScale N δ V) Δ r.C l)
            (convolutionWuWindows N Δ V), f x := by
  unfold gamma6GainPacking gamma5GainCell
  simp_rw [sum_product]
  simp_rw [gamma5Gain_grid_sum hR hΔ]
  rw [sum_comm]
  apply sum_congr rfl
  intro j _
  trans ∑ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
    ∑ l ∈ range (gamma5GainSize (gamma5GainScale N δ V) Δ r.C r.D),
      ∑ p ∈ primeWindow N
        (gamma5GainEnd (gamma5GainScale N δ V) Δ r.A j / Δ)
        (gamma5GainEnd (gamma5GainScale N δ V) Δ r.A j),
        ∑ q ∈ primeWindow N
          (gamma5GainEnd (gamma5GainScale N δ V) Δ r.C l / Δ)
          (gamma5GainEnd (gamma5GainScale N δ V) Δ r.C l), f (d, p, q)
  · apply sum_congr rfl
    intro d _
    exact sum_comm
  · exact sum_comm

theorem gamma6Gain_packing_coarse {i N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hR : 1 < gamma5GainScale N δ V) (hΔ : 1 < Δ) (r : Gamma6GainRectangle) :
    gamma6GainPacking N δ Δ V r ⊆
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

theorem gamma6Gain_rectangle_admission (k : ℕ) {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) (r : Gamma6GainRectangle) :
    ∀ᶠ N : ℕ in atTop, ∀ i : ℕ, ∀ Δ : ℝ, ∀ V : Fin i → ℝ,
      wuSourceBox k δ N i Δ V →
      1 < Δ ∧ 1 < gamma5GainScale N δ V ∧
      ∀ x ∈ boxConvolutionSupport (convolutionWuWindows N Δ V) ×ˢ
        (primeWindow N ((gamma5GainScale N δ V) ^ r.A) ((gamma5GainScale N δ V) ^ r.B) ×ˢ
        primeWindow N ((gamma5GainScale N δ V) ^ r.C) ((gamma5GainScale N δ V) ^ r.D)),
        x ∈ gamma6BaseLabels N δ (convolutionWuWindows N Δ V) ∧
        gamma5GainV
          (gamma5MassCoordinate ((N : ℝ) ^ (1 / 2 - δ) / x.1) x.2.1)
          (gamma5MassCoordinate ((N : ℝ) ^ (1 / 2 - δ) / x.1) x.2.2) ≤ r.s := by
  let e := min (min (r.A - gamma5MassA) (r.C - gamma6BaseC))
    ((r.s - gamma5GainV r.A r.C) / (2 * gamma5ClassicalS))
  have hS : 0 < gamma5ClassicalS := by norm_num [gamma5ClassicalS]
  have he : 0 < e := lt_min
    (lt_min (sub_pos.mpr r.lower) (sub_pos.mpr r.secondLower))
    (div_pos (sub_pos.mpr r.rightEnd) (by positivity))
  filter_upwards [gamma5Gain_mesh_eventually k hδ hδhi he, eventually_ge_atTop (2 : ℕ)]
    with N hm hN
  intro i Δ V hb
  have hh := hm i Δ V hb
  refine ⟨hh.1, hh.2.1, ?_⟩
  intro x hx
  obtain ⟨hd, hpq⟩ := mem_product.mp hx
  obtain ⟨hp, hq⟩ := mem_product.mp hpq
  have him : (i : ℝ) ≤ (k : ℝ) + 1 := by exact_mod_cast hb.1.trans (Nat.le_succ k)
  have hstep := (gamma5Gain_step_pos hh.2.1 hh.1).le
  have hmesh : (i : ℝ) * gamma5GainStep (gamma5GainScale N δ V) Δ ≤ e :=
    (mul_le_mul_of_nonneg_right him hstep).trans (by
      simpa only [gamma5GainStep, mul_div_assoc] using hh.2.2.le)
  exact gamma6Gain_coarse_label hN hδ hδhi hb hh.2.1 hh.1 r
    ((min_le_left _ _).trans (min_le_left _ _))
    ((min_le_left _ _).trans (min_le_right _ _))
    (by have h : e ≤ (r.s - gamma5GainV r.A r.C) / (2 * gamma5ClassicalS) := min_le_right _ _
        have hh := (le_div_iff₀ (by positivity : 0 < 2 * gamma5ClassicalS)).mp h
        linarith)
    hmesh hd hp hq

theorem gamma6Gain_packing_actual (k : ℕ) {δ η : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) (hη : 0 < η) (r : Gamma6GainRectangle) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ i : ℕ, ∀ Δ : ℝ, ∀ V : Fin i → ℝ, wuSourceBox k δ N i Δ V →
      gamma6GainPacking N δ Δ V r ⊆ gamma6BaseLabels N δ (convolutionWuWindows N Δ V) ∧
      gamma5ClassicalCount N δ (convolutionWuWindows N Δ V) (gamma6GainPacking N δ Δ V r) ≤
        (1 - wuImprovementLimit true δ r.s + η) *
          gamma5ClassicalMainMass N δ (convolutionWuWindows N Δ V) (gamma6GainPacking N δ Δ V r) := by
  have hr := gamma6Gain_rectangle_bounds r
  obtain ⟨TC, hTC, hc⟩ := gamma6Gain_grid_comparison k hδ hδhi hη {r.s}
    (by intro s hs; have he : s = r.s := mem_singleton.mp hs; subst s
        exact ⟨hr.2.2.2.2.2.2.2.le, r.parameter.le⟩)
  obtain ⟨TA, ha⟩ := eventually_atTop.mp (gamma6Gain_rectangle_admission k hδ hδhi r)
  refine ⟨max TC TA, hTC.trans (le_max_left _ _), ?_⟩
  intro N hN he i Δ V hb
  have hNC : TC ≤ N := (le_max_left _ _).trans hN
  have hh := ha N ((le_max_right _ _).trans hN) i Δ V hb
  have hsub := fun x hx => (hh.2.2 x (gamma6Gain_packing_coarse hh.2.1 hh.1 r hx)).1
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
    have had := gamma6Gain_endpoint_admission hh.2.1 r ⟨hp.1.trans hpm, hp.2⟩ ⟨hq.1.trans hqm, hq.2⟩
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
  rw [gamma6Gain_packing_sum hh.2.1 hh.1, gamma6Gain_packing_sum hh.2.1 hh.1]
  simp only [mul_sum]
  apply sum_le_sum
  intro j hj
  apply sum_le_sum
  intro l hl
  simpa only [gamma5ClassicalCount, gamma5ClassicalMainMass, mul_sum] using
    hcell j (mem_range.mp hj) l (mem_range.mp hl)

end Wu2008DoubleSieve
