import Wu18938Campaign.M1.Confirmed.PairGainGeometry

noncomputable section

namespace Wu18938Campaign.M1.Confirmed.Pair

open Wu2008DoubleSieve MotherPair Finset Real Filter
open scoped Classical Topology

theorem rectangle_seed (p : SecondFunctionalParameters) (hp : AnalyticParameters p)
    (j : Term) (r : GainRectangle p j) (hrs : r.sample ≤ 13 / 5)
    (m : ℕ) {η δ ε : ℝ} (hη : 0 < η) (hδ : 0 < δ) (hδhi : δ ≤ 1 / 100) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      ∀ P Q : ℝ,
      (gamma5GainScale N δ V) ^ r.A ≤ P → P ≤ (gamma5GainScale N δ V) ^ r.B →
      (gamma5GainScale N δ V) ^ r.C ≤ Q → Q ≤ (gamma5GainScale N δ V) ^ r.D →
      gamma5GainCell N Δ P Q (convolutionWuWindows N Δ V) ⊆
        termLabels p j N δ (convolutionWuWindows N Δ V) ∧
      termCount p j N δ (convolutionWuWindows N Δ V)
        (gamma5GainCell N Δ P Q (convolutionWuWindows N Δ V)) ≤
        (1 - HighSixPhase7.seed + ε) * gamma5ClassicalMainMass N δ
          (convolutionWuWindows N Δ V) (gamma5GainCell N Δ P Q (convolutionWuWindows N Δ V)) := by
  have hS : 0 < p.S := by linarith [hp.three_le_S]
  have hζ : 0 < η / (4 * p.S) := by positivity
  obtain ⟨T0,hT04,h0⟩ := cell_seed p hp m (show 0 < η / 4 by positivity) hδ hδhi he
  obtain ⟨T1,_,h1⟩ := rectangle_admitted p hp j r m hη hδ
  obtain ⟨T2,_,h2⟩ := Rebox.scale m hη hδ
  obtain ⟨T3,h3⟩ := eventually_atTop.mp
    (((tendsto_rpow_atTop hζ).comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (3 : ℝ)))
  refine ⟨max T0 (max T1 (max T2 T3)),hT04.trans (le_max_left _ _),?_⟩
  intro N hN heven i Δ V hb P Q hPA hPB hQC hQD
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
      (N : ℝ) ^ ((η / 4) * min (1 / p.S) ((1 - 2 / p.kappa3) / 2)) ≤ U / Δ := by
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
    calc
      _ ≤ (η / 4) * (1 / p.S) := hh
      _ = η / (4 * p.S) := by ring
  have hU (U E : ℝ) (hE : E ≤ 1) (hU : U ≤ (gamma5GainScale N δ V) ^ E) : U ≤ N :=
    hU.trans ((by simpa only [rpow_one,gamma5GainScale] using rpow_le_rpow_of_exponent_le hR.le hE :
      (gamma5GainScale N δ V) ^ E ≤ gamma5GainScale N δ V).trans hRN)
  refine ⟨hsub,h0 N (by omega) heven i Δ P Q V hweak
    (hlow P r.A r.lowerP_lt_A.le hPA)
    (hlow Q r.C (r.lowerP_lt_A.le.trans (r.A_lt_B.le.trans r.B_lt_C.le)) hQC)
    (hU P r.B (by linarith [r.B_lt_C,r.C_lt_D,r.twiceD_lt_one]) hPB)
    (hU Q r.D (by linarith [r.twiceD_lt_one]) hQD) j hsub ?_⟩
  exact fun x hx => (hratio x hx).trans hrs

theorem packing_seed (p : SecondFunctionalParameters) (hp : AnalyticParameters p)
    (j : Term) (r : GainRectangle p j) (hrs : r.sample ≤ 13 / 5)
    (m : ℕ) {η δ ε : ℝ} (hη : 0 < η) (hδ : 0 < δ) (hδhi : δ ≤ 1 / 100) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      packing N δ Δ V r ⊆ termLabels p j N δ (convolutionWuWindows N Δ V) ∧
      termCount p j N δ (convolutionWuWindows N Δ V) (packing N δ Δ V r) ≤
        (1 - HighSixPhase7.seed + ε) *
          gamma5ClassicalMainMass N δ (convolutionWuWindows N Δ V) (packing N δ Δ V r) := by
  obtain ⟨T0,hT04,h0⟩ := rectangle_seed p hp j r hrs m hη hδ hδhi he
  obtain ⟨T1,_,h1⟩ := gain_mesh m hη hδ (show (0 : ℝ) < 1 by norm_num)
  refine ⟨max T0 T1,hT04.trans (le_max_left _ _),?_⟩
  intro N hN heven i Δ V hb
  obtain ⟨hΔ,hR,_⟩ := h1 N (by omega) i Δ V hb
  have cell (a : ℕ) (ha : a ∈ range (gamma5GainSize (gamma5GainScale N δ V) Δ r.A r.B))
      (b : ℕ) (hb' : b ∈ range (gamma5GainSize (gamma5GainScale N δ V) Δ r.C r.D)) := by
    have hpa := gamma5Gain_point_bounds hR hΔ r.A_lt_B.le (mem_range.mp ha)
    have hqb := gamma5Gain_point_bounds hR hΔ r.C_lt_D.le (mem_range.mp hb')
    have hpm := (gamma5Gain_point_strictMono hR hΔ r.A).monotone (Nat.le_succ a)
    have hqm := (gamma5Gain_point_strictMono hR hΔ r.C).monotone (Nat.le_succ b)
    exact h0 N (by omega) heven i Δ V hb
      (gamma5GainEnd (gamma5GainScale N δ V) Δ r.A a)
      (gamma5GainEnd (gamma5GainScale N δ V) Δ r.C b)
      (rpow_le_rpow_of_exponent_le hR.le (hpa.1.trans hpm))
      (rpow_le_rpow_of_exponent_le hR.le hpa.2)
      (rpow_le_rpow_of_exponent_le hR.le (hqb.1.trans hqm))
      (rpow_le_rpow_of_exponent_le hR.le hqb.2)
  refine ⟨packing_subset_of_cells r hR hΔ (fun a ha b hb' => (cell a ha b hb').1),?_⟩
  cases j <;>
    simp only [termCount,fixedCount,gamma5ClassicalMainMass] at cell ⊢ <;>
    rw [packing_sum hR hΔ,packing_sum hR hΔ] <;>
    simp only [mul_sum] <;>
    apply sum_le_sum <;> intro a ha <;>
    apply sum_le_sum <;> intro b hb' <;>
    simpa only [mul_sum] using (cell a ha b hb').2

end Wu18938Campaign.M1.Confirmed.Pair
