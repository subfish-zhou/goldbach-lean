import Wu18938Campaign.M1.Confirmed.FullFiveRectangle

noncomputable section

namespace Wu18938Campaign.M1.Confirmed.FullFive

open Wu2008DoubleSieve MotherPair Finset Set Real Filter
open scoped Classical Topology

def packing {i : ℕ} (N : ℕ) (δ Δ : ℝ) (V : Fin i → ℝ)
    {p : SecondFunctionalParameters} (r : Rectangle p) : Finset Gamma5ClassicalLabel :=
  boxConvolutionSupport (convolutionWuWindows N Δ V) ×ˢ
    (primeWindow N ((gamma5GainScale N δ V) ^ r.A)
      ((gamma5GainScale N δ V) ^ gamma5GainTerminal (gamma5GainScale N δ V) Δ r.A r.B) ×ˢ
    primeWindow N ((gamma5GainScale N δ V) ^ r.C)
      ((gamma5GainScale N δ V) ^ gamma5GainTerminal (gamma5GainScale N δ V) Δ r.C r.D))

theorem packing_sum {i N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hR : 1 < gamma5GainScale N δ V) (hΔ : 1 < Δ)
    {p : SecondFunctionalParameters} (r : Rectangle p) (f : Gamma5ClassicalLabel → ℝ) :
    (∑ x ∈ packing N δ Δ V r, f x) =
      ∑ a ∈ range (gamma5GainSize (gamma5GainScale N δ V) Δ r.A r.B),
        ∑ b ∈ range (gamma5GainSize (gamma5GainScale N δ V) Δ r.C r.D),
          ∑ x ∈ gamma5GainCell N Δ
            (gamma5GainEnd (gamma5GainScale N δ V) Δ r.A a)
            (gamma5GainEnd (gamma5GainScale N δ V) Δ r.C b)
            (convolutionWuWindows N Δ V), f x := by
  unfold packing gamma5GainCell
  simp_rw [sum_product]
  simp_rw [gamma5Gain_grid_sum hR hΔ]
  rw [sum_comm]
  apply sum_congr rfl
  intro a _
  trans ∑ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
    ∑ b ∈ range (gamma5GainSize (gamma5GainScale N δ V) Δ r.C r.D),
      ∑ q ∈ primeWindow N (gamma5GainEnd (gamma5GainScale N δ V) Δ r.A a / Δ)
        (gamma5GainEnd (gamma5GainScale N δ V) Δ r.A a),
        ∑ l ∈ primeWindow N (gamma5GainEnd (gamma5GainScale N δ V) Δ r.C b / Δ)
          (gamma5GainEnd (gamma5GainScale N δ V) Δ r.C b), f (d,q,l)
  · apply sum_congr rfl
    intro d _
    exact sum_comm
  · exact sum_comm

theorem packing_subset_of_cells {i N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    {p : SecondFunctionalParameters} (r : Rectangle p)
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
    have hyx : y ≠ x := fun he => hn (he ▸ hc a ha b hb hy)
    simp only [if_neg hyx]
  simp [hx] at hz

theorem packing_coordinates {i N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    {p : SecondFunctionalParameters} (r : Rectangle p)
    (hR : 1 < gamma5GainScale N δ V) (hΔ : 1 < Δ)
    {x : Gamma5ClassicalLabel} (hx : x ∈ packing N δ Δ V r) :
    (gamma5MassCoordinate (gamma5GainScale N δ V) x.2.1,
      gamma5MassCoordinate (gamma5GainScale N δ V) x.2.2) ∈
      Ico r.A r.B ×ˢ Ico r.C r.D := by
  obtain ⟨_,hpq⟩ := mem_product.mp hx
  obtain ⟨hp,hq⟩ := mem_product.mp hpq
  have coord {a : ℕ} {A B : ℝ} (hAB : A ≤ B)
      (ha : a ∈ primeWindow N ((gamma5GainScale N δ V)^A)
        ((gamma5GainScale N δ V)^gamma5GainTerminal (gamma5GainScale N δ V) Δ A B)) :
      gamma5MassCoordinate (gamma5GainScale N δ V) a ∈ Ico A B := by
    have ha' := gamma5Gain_window_mono N le_rfl
      (rpow_le_rpow_of_exponent_le hR.le (gamma5Gain_terminal_bounds hR hΔ hAB).2.1) ha
    obtain ⟨hprime,_,hl,hu⟩ := mem_primeWindow.mp ha'
    have hpos : (0 : ℝ) < a := by exact_mod_cast hprime.pos
    have hR0 : 0 < gamma5GainScale N δ V := by linarith
    constructor
    · apply (le_div_iff₀ (log_pos hR)).mpr
      simpa only [log_rpow hR0] using log_le_log (rpow_pos_of_pos hR0 A) hl
    · apply (div_lt_iff₀ (log_pos hR)).mpr
      simpa only [log_rpow hR0] using log_lt_log hpos hu
  exact ⟨coord r.A_lt_B.le hp,coord r.C_lt_D.le hq⟩

theorem packing_disjoint {i N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    {p : SecondFunctionalParameters} {r s : Rectangle p}
    (hR : 1 < gamma5GainScale N δ V) (hΔ : 1 < Δ)
    (hrs : Disjoint (Ico r.A r.B ×ˢ Ico r.C r.D) (Ico s.A s.B ×ˢ Ico s.C s.D)) :
    Disjoint (packing N δ Δ V r) (packing N δ Δ V s) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  exact Set.disjoint_left.mp hrs (packing_coordinates r hR hΔ hx)
    (packing_coordinates s hR hΔ hy)

theorem rectangle_node (p : SecondFunctionalParameters) (hp : AnalyticParameters p)
    (r : Rectangle p) (m : ℕ) {η δ : ℝ} (hη : 0 < η) (hδ : 0 < δ) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      ∀ c : ℝ,
      (∀ (k : ℕ) (U : Fin k → ℝ), RoughBox (m + 2) (Pair.childEta p η) δ N k Δ U →
        wuBoxPhi N δ (convolutionWuWindows N Δ U) r.sample ≤
          c * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ U)) →
      ∀ P Q : ℝ,
      (gamma5GainScale N δ V) ^ r.A ≤ P → P ≤ (gamma5GainScale N δ V) ^ r.B →
      (gamma5GainScale N δ V) ^ r.C ≤ Q → Q ≤ (gamma5GainScale N δ V) ^ r.D →
      gamma5GainCell N Δ P Q (convolutionWuWindows N Δ V) ⊆
        termLabels p .gammaFive N δ (convolutionWuWindows N Δ V) ∧
      termCount p .gammaFive N δ (convolutionWuWindows N Δ V)
        (gamma5GainCell N Δ P Q (convolutionWuWindows N Δ V)) ≤
        c * gamma5ClassicalMainMass N δ (convolutionWuWindows N Δ V)
          (gamma5GainCell N Δ P Q (convolutionWuWindows N Δ V)) := by
  have hS : 0 < p.S := by linarith [hp.three_le_S]
  have hζ : 0 < η / (4 * p.S) := by positivity
  obtain ⟨T1,hT14,h1⟩ := rectangle_admitted p hp r m hη hδ
  obtain ⟨T2,_,h2⟩ := Rebox.scale m hη hδ
  obtain ⟨T3,h3⟩ := eventually_atTop.mp
    (((tendsto_rpow_atTop hζ).comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (3 : ℝ)))
  refine ⟨max T1 (max T2 T3),hT14.trans (le_max_left _ _),?_⟩
  intro N hN i Δ V hb c hn P Q hPA hPB hQC hQD
  obtain ⟨hΔ,hL,hRlo,hR,hRN,_⟩ := h2 N (by omega) i Δ V hb
  obtain ⟨hsub,hratio⟩ := (h1 N (by omega) i Δ V hb).2 P Q hPA hPB hQC hQD
  have hweak := hb.weaken (by omega) le_rfl (show η / 4 ≤ η by linarith)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hΔZ : Δ ≤ (N : ℝ) ^ (η / (4 * p.S)) :=
    (Rebox.mesh_log hb hL).2.2.trans (h3 N (by omega))
  have hpow : (N : ℝ) ^ (η / (4 * p.S)) * (N : ℝ) ^ (η / (4 * p.S)) =
      ((N : ℝ) ^ (η / 2)) ^ (1 / p.S) := by
    rw [← rpow_add hN0,← rpow_mul hN0.le]
    congr 1
    ring
  have hlow (U A : ℝ) (hA : 1 / p.S ≤ A) (hU : (gamma5GainScale N δ V) ^ A ≤ U) :
      (N : ℝ) ^ Pair.childEta p η ≤ U / Δ := by
    have hUpow : ((N : ℝ) ^ (η / 2)) ^ (1 / p.S) ≤ U :=
      (rpow_le_rpow (rpow_nonneg hN0.le _) hRlo (one_div_pos.mpr hS).le).trans
        ((rpow_le_rpow_of_exponent_le hR.le hA).trans hU)
    have hdiv : (N : ℝ) ^ (η / (4 * p.S)) ≤ U / Δ := by
      apply (le_div_iff₀ (by linarith : 0 < Δ)).mpr
      calc
        _ ≤ (N : ℝ) ^ (η / (4 * p.S)) * (N : ℝ) ^ (η / (4 * p.S)) :=
          mul_le_mul_of_nonneg_left hΔZ (rpow_nonneg hN0.le _)
        _ ≤ U := by rw [hpow]; exact hUpow
    apply (rpow_le_rpow_of_exponent_le hN1 _).trans hdiv
    have hh := mul_le_mul_of_nonneg_left
      (min_le_left (1 / p.S) ((1 - 2 / p.kappa3) / 2)) (show 0 ≤ η / 4 by positivity)
    exact hh.trans_eq (by ring)
  have hU (U E : ℝ) (hE : E ≤ 1) (hU : U ≤ (gamma5GainScale N δ V) ^ E) : U ≤ N :=
    hU.trans ((by simpa only [rpow_one,gamma5GainScale] using rpow_le_rpow_of_exponent_le hR.le hE :
      (gamma5GainScale N δ V) ^ E ≤ gamma5GainScale N δ V).trans hRN)
  have hc := classical_cap hp
  have hsub' := hsub.trans (Pair.term_cap hweak (by omega) (by positivity) hδ p hp .gammaFive)
  have hchild := Pair.child_rough hweak (by omega) (by positivity) hδ hc
    (by simpa only [Pair.childEta,mul_one_div] using hlow P r.A r.lowerP_lt_A.le hPA)
    (by simpa only [Pair.childEta,mul_one_div] using
      hlow Q r.C (r.lowerP_lt_A.le.trans (r.A_lt_B.le.trans r.B_lt_C.le)) hQC)
    (hU P r.B (by linarith [r.B_lt_C,r.C_lt_D,r.twiceD_lt_one]) hPB)
    (hU Q r.D (by linarith [r.twiceD_lt_one]) hQD) hsub'
  have hn' := hn (i + 2) (Fin.cons P (Fin.cons Q V))
    (by simpa only [Pair.childEta,mul_one_div] using hchild)
  rw [Pair.child_theta] at hn'
  exact ⟨hsub,(Pair.cell_count hb (by omega) hη hδ p hp .gammaFive
    (by linarith [r.sample_lower]) hsub hratio).trans hn'⟩

theorem packing_node (p : SecondFunctionalParameters) (hp : AnalyticParameters p)
    (r : Rectangle p) (m : ℕ) {η δ : ℝ} (hη : 0 < η) (hδ : 0 < δ) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      ∀ c : ℝ,
      (∀ (k : ℕ) (U : Fin k → ℝ), RoughBox (m + 2) (Pair.childEta p η) δ N k Δ U →
        wuBoxPhi N δ (convolutionWuWindows N Δ U) r.sample ≤
          c * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ U)) →
      packing N δ Δ V r ⊆ termLabels p .gammaFive N δ (convolutionWuWindows N Δ V) ∧
      termCount p .gammaFive N δ (convolutionWuWindows N Δ V) (packing N δ Δ V r) ≤
        c * gamma5ClassicalMainMass N δ (convolutionWuWindows N Δ V) (packing N δ Δ V r) := by
  obtain ⟨T0,hT04,h0⟩ := rectangle_node p hp r m hη hδ
  obtain ⟨T1,_,h1⟩ := Pair.gain_mesh m hη hδ (show (0 : ℝ) < 1 by norm_num)
  refine ⟨max T0 T1,hT04.trans (le_max_left _ _),?_⟩
  intro N hN i Δ V hb c hn
  obtain ⟨hΔ,hR,_⟩ := h1 N (by omega) i Δ V hb
  have cell (a : ℕ) (ha : a ∈ range (gamma5GainSize (gamma5GainScale N δ V) Δ r.A r.B))
      (b : ℕ) (hb' : b ∈ range (gamma5GainSize (gamma5GainScale N δ V) Δ r.C r.D)) := by
    have hpa := gamma5Gain_point_bounds hR hΔ r.A_lt_B.le (mem_range.mp ha)
    have hqb := gamma5Gain_point_bounds hR hΔ r.C_lt_D.le (mem_range.mp hb')
    have hpm := (gamma5Gain_point_strictMono hR hΔ r.A).monotone (Nat.le_succ a)
    have hqm := (gamma5Gain_point_strictMono hR hΔ r.C).monotone (Nat.le_succ b)
    exact h0 N (by omega) i Δ V hb c hn
      (gamma5GainEnd (gamma5GainScale N δ V) Δ r.A a)
      (gamma5GainEnd (gamma5GainScale N δ V) Δ r.C b)
      (rpow_le_rpow_of_exponent_le hR.le (hpa.1.trans hpm))
      (rpow_le_rpow_of_exponent_le hR.le hpa.2)
      (rpow_le_rpow_of_exponent_le hR.le (hqb.1.trans hqm))
      (rpow_le_rpow_of_exponent_le hR.le hqb.2)
  refine ⟨packing_subset_of_cells r hR hΔ (fun a ha b hb' => (cell a ha b hb').1),?_⟩
  simp only [termCount,fixedCount,gamma5ClassicalMainMass] at cell ⊢
  rw [packing_sum hR hΔ,packing_sum hR hΔ]
  simp only [mul_sum]
  apply sum_le_sum
  intro a ha
  apply sum_le_sum
  intro b hb'
  simpa only [mul_sum] using (cell a ha b hb').2

end Wu18938Campaign.M1.Confirmed.FullFive
