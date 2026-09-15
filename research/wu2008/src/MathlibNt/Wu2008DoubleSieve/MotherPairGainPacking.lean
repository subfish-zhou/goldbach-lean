import MathlibNt.Wu2008DoubleSieve.MotherPairGainCell
import MathlibNt.Wu2008DoubleSieve.Gamma5GainPacking

namespace Wu2008DoubleSieve.MotherPair
open Finset Set Real Filter
open scoped Classical Topology

noncomputable def packing {i : ℕ} (N : ℕ) (δ Δ : ℝ) (V : Fin i → ℝ)
    {p : SecondFunctionalParameters} {j : Term} (r : GainRectangle p j) : Finset Gamma5ClassicalLabel :=
  boxConvolutionSupport (convolutionWuWindows N Δ V) ×ˢ
    (primeWindow N ((gamma5GainScale N δ V) ^ r.A)
      ((gamma5GainScale N δ V) ^ gamma5GainTerminal (gamma5GainScale N δ V) Δ r.A r.B) ×ˢ
    primeWindow N ((gamma5GainScale N δ V) ^ r.C)
      ((gamma5GainScale N δ V) ^ gamma5GainTerminal (gamma5GainScale N δ V) Δ r.C r.D))

theorem packing_sum {i N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hR : 1 < gamma5GainScale N δ V) (hΔ : 1 < Δ) {p : SecondFunctionalParameters} {j : Term} (r : GainRectangle p j)
    (f : Gamma5ClassicalLabel → ℝ) :
    (∑ x ∈ packing N δ Δ V r, f x) =
      ∑ j ∈ range (gamma5GainSize (gamma5GainScale N δ V) Δ r.A r.B),
        ∑ l ∈ range (gamma5GainSize (gamma5GainScale N δ V) Δ r.C r.D),
          ∑ x ∈ gamma5GainCell N Δ
            (gamma5GainEnd (gamma5GainScale N δ V) Δ r.A j)
            (gamma5GainEnd (gamma5GainScale N δ V) Δ r.C l)
            (convolutionWuWindows N Δ V), f x := by
  unfold packing gamma5GainCell
  simp_rw [sum_product]
  simp_rw [gamma5Gain_grid_sum hR hΔ]
  rw [sum_comm]
  apply sum_congr rfl
  intro j _
  trans ∑ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
    ∑ l ∈ range (gamma5GainSize (gamma5GainScale N δ V) Δ r.C r.D),
      ∑ p ∈ primeWindow N (gamma5GainEnd (gamma5GainScale N δ V) Δ r.A j / Δ)
        (gamma5GainEnd (gamma5GainScale N δ V) Δ r.A j),
        ∑ q ∈ primeWindow N (gamma5GainEnd (gamma5GainScale N δ V) Δ r.C l / Δ)
          (gamma5GainEnd (gamma5GainScale N δ V) Δ r.C l), f (d, p, q)
  · apply sum_congr rfl
    intro d _
    exact sum_comm
  · exact sum_comm

theorem packing_subset_of_cells {i N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    {p : SecondFunctionalParameters} {j : Term} (r : GainRectangle p j)
    (hR : 1 < gamma5GainScale N δ V) (hΔ : 1 < Δ)
    {X : Finset Gamma5ClassicalLabel}
    (hc : ∀ a ∈ range (gamma5GainSize (gamma5GainScale N δ V) Δ r.A r.B),
      ∀ b ∈ range (gamma5GainSize (gamma5GainScale N δ V) Δ r.C r.D),
      gamma5GainCell N Δ (gamma5GainEnd (gamma5GainScale N δ V) Δ r.A a)
        (gamma5GainEnd (gamma5GainScale N δ V) Δ r.C b)
        (convolutionWuWindows N Δ V) ⊆ X) : packing N δ Δ V r ⊆ X := by
  intro x hx
  by_contra hn
  have hz : (∑ y ∈ packing N δ Δ V r, if y = x then (1 : ℝ) else 0) = 0 := by
    rw [packing_sum hR hΔ]
    apply sum_eq_zero
    intro a ha
    apply sum_eq_zero
    intro b hb
    apply sum_eq_zero
    intro y hy
    have hyx : y ≠ x := by
      intro he
      subst y
      exact hn (hc a ha b hb hy)
    simp only [if_neg hyx]
  simp [hx] at hz

theorem packing_actual (p : SecondFunctionalParameters) (h : AnalyticParameters p)
    (j : Term) (r : GainRectangle p j) (k : ℕ) {δ η : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1/10) (hη : 0 < η) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ i : ℕ, ∀ Δ : ℝ, ∀ V : Fin i → ℝ, wuSourceBox k δ N i Δ V →
      packing N δ Δ V r ⊆ termLabels p j N δ (convolutionWuWindows N Δ V) ∧
      termCount p j N δ (convolutionWuWindows N Δ V) (packing N δ Δ V r) ≤
        (1-wuImprovementLimit true δ r.sample+η)*gamma5ClassicalMainMass N δ
          (convolutionWuWindows N Δ V) (packing N δ Δ V r) := by
  obtain ⟨TC,hTC,hc⟩ := rectangle_cell_upper p h j r k hδ hδhi hη
  obtain ⟨TG,hg⟩ := eventually_atTop.mp (gamma5Gain_mesh_eventually k hδ hδhi (by norm_num : (0:ℝ)<1))
  refine ⟨max TC TG,hTC.trans (le_max_left _ _),?_⟩
  intro N hN he i Δ V hb
  obtain ⟨hΔ,hR,_⟩ := hg N ((le_max_right _ _).trans hN) i Δ V hb
  have cell (a : ℕ) (ha : a ∈ range (gamma5GainSize (gamma5GainScale N δ V) Δ r.A r.B))
      (b : ℕ) (hb' : b ∈ range (gamma5GainSize (gamma5GainScale N δ V) Δ r.C r.D)) := by
    have hp := gamma5Gain_point_bounds hR hΔ r.A_lt_B.le (mem_range.mp ha)
    have hq := gamma5Gain_point_bounds hR hΔ r.C_lt_D.le (mem_range.mp hb')
    have hpm := (gamma5Gain_point_strictMono hR hΔ r.A).monotone (Nat.le_succ a)
    have hqm := (gamma5Gain_point_strictMono hR hΔ r.C).monotone (Nat.le_succ b)
    exact hc N ((le_max_left _ _).trans hN) he i Δ V hb
      (gamma5GainEnd (gamma5GainScale N δ V) Δ r.A a)
      (gamma5GainEnd (gamma5GainScale N δ V) Δ r.C b)
      (rpow_le_rpow_of_exponent_le hR.le (hp.1.trans hpm))
      (rpow_le_rpow_of_exponent_le hR.le hp.2)
      (rpow_le_rpow_of_exponent_le hR.le (hq.1.trans hqm))
      (rpow_le_rpow_of_exponent_le hR.le hq.2)
  refine ⟨packing_subset_of_cells r hR hΔ (fun a ha b hb' => (cell a ha b hb').1),?_⟩
  cases j <;>
    simp only [termCount, fixedCount, gamma5ClassicalMainMass] at cell ⊢ <;>
    rw [packing_sum hR hΔ, packing_sum hR hΔ] <;>
    simp only [mul_sum] <;>
    apply sum_le_sum <;> intro a ha <;>
    apply sum_le_sum <;> intro b hb' <;>
    simpa only [mul_sum] using (cell a ha b hb').2

theorem packing_coarse {i N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    {p : SecondFunctionalParameters} {j : Term} (r : GainRectangle p j)
    (hR : 1 < gamma5GainScale N δ V) (hΔ : 1 < Δ) :
    packing N δ Δ V r ⊆ boxConvolutionSupport (convolutionWuWindows N Δ V) ×ˢ
      (primeWindow N ((gamma5GainScale N δ V)^r.A) ((gamma5GainScale N δ V)^r.B) ×ˢ
       primeWindow N ((gamma5GainScale N δ V)^r.C) ((gamma5GainScale N δ V)^r.D)) := by
  intro x hx
  obtain ⟨hd,hpq⟩ := mem_product.mp hx
  obtain ⟨hp,hq⟩ := mem_product.mp hpq
  exact mem_product.mpr ⟨hd,mem_product.mpr ⟨
    gamma5Gain_window_mono N le_rfl (rpow_le_rpow_of_exponent_le hR.le
      (gamma5Gain_terminal_bounds hR hΔ r.A_lt_B.le).2.1) hp,
    gamma5Gain_window_mono N le_rfl (rpow_le_rpow_of_exponent_le hR.le
      (gamma5Gain_terminal_bounds hR hΔ r.C_lt_D.le).2.1) hq⟩⟩

theorem packing_coordinates {i N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    {p : SecondFunctionalParameters} {j : Term} (r : GainRectangle p j)
    (hR : 1 < gamma5GainScale N δ V) (hΔ : 1 < Δ)
    {x : Gamma5ClassicalLabel} (hx : x ∈ packing N δ Δ V r) :
    (gamma5MassCoordinate (gamma5GainScale N δ V) x.2.1,
      gamma5MassCoordinate (gamma5GainScale N δ V) x.2.2) ∈
      Set.Ico r.A r.B ×ˢ Set.Ico r.C r.D := by
  obtain ⟨_,hpq⟩ := mem_product.mp (packing_coarse r hR hΔ hx)
  obtain ⟨hp,hq⟩ := mem_product.mp hpq
  have coord {a : ℕ} {A B : ℝ}
      (ha : a ∈ primeWindow N ((gamma5GainScale N δ V)^A) ((gamma5GainScale N δ V)^B)) :
      gamma5MassCoordinate (gamma5GainScale N δ V) a ∈ Set.Ico A B := by
    obtain ⟨hp,_,hl,hu⟩ := mem_primeWindow.mp ha
    have hpos : (0:ℝ)<a := by exact_mod_cast hp.pos
    have hR0 : 0<gamma5GainScale N δ V := by linarith
    constructor
    · apply (le_div_iff₀ (log_pos hR)).mpr
      simpa only [log_rpow hR0] using log_le_log (rpow_pos_of_pos hR0 A) hl
    · apply (div_lt_iff₀ (log_pos hR)).mpr
      simpa only [log_rpow hR0] using log_lt_log hpos hu
  exact ⟨coord hp,coord hq⟩

theorem packing_disjoint {i N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    {p : SecondFunctionalParameters} {j : Term} {r s : GainRectangle p j}
    (hR : 1 < gamma5GainScale N δ V) (hΔ : 1 < Δ)
    (hrs : Disjoint (Set.Ico r.A r.B ×ˢ Set.Ico r.C r.D)
      (Set.Ico s.A s.B ×ˢ Set.Ico s.C s.D)) :
    Disjoint (packing N δ Δ V r) (packing N δ Δ V s) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  exact Set.disjoint_left.mp hrs (packing_coordinates r hR hΔ hx)
    (packing_coordinates s hR hΔ hy)

theorem packing_admission (p : SecondFunctionalParameters) (h : AnalyticParameters p)
    (j : Term) (r : GainRectangle p j) (k : ℕ) {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1/10) :
    ∀ᶠ N : ℕ in atTop, ∀ i : ℕ, ∀ Δ : ℝ, ∀ V : Fin i → ℝ,
      wuSourceBox k δ N i Δ V →
      packing N δ Δ V r ⊆ termLabels p j N δ (convolutionWuWindows N Δ V) := by
  filter_upwards [rectangle_admission p h j r k hδ hδhi,
    gamma5Gain_mesh_eventually k hδ hδhi (by norm_num : (0:ℝ)<1)] with N ha hm
  intro i Δ V hb
  obtain ⟨hΔ,hR,_⟩ := hm i Δ V hb
  apply packing_subset_of_cells r hR hΔ
  intro a ha' b hb'
  have hp := gamma5Gain_point_bounds hR hΔ r.A_lt_B.le (mem_range.mp ha')
  have hq := gamma5Gain_point_bounds hR hΔ r.C_lt_D.le (mem_range.mp hb')
  have hpm := (gamma5Gain_point_strictMono hR hΔ r.A).monotone (Nat.le_succ a)
  have hqm := (gamma5Gain_point_strictMono hR hΔ r.C).monotone (Nat.le_succ b)
  exact ((ha i Δ V hb).2 _ _
    (rpow_le_rpow_of_exponent_le hR.le (hp.1.trans hpm))
    (rpow_le_rpow_of_exponent_le hR.le hp.2)
    (rpow_le_rpow_of_exponent_le hR.le (hq.1.trans hqm))
    (rpow_le_rpow_of_exponent_le hR.le hq.2)).1

end Wu2008DoubleSieve.MotherPair
