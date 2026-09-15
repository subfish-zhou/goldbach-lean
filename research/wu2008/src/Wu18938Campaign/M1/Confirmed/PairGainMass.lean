import Wu18938Campaign.M1.Confirmed.PairFinitePacking
import MathlibNt.Wu2008DoubleSieve.MotherPairGainMass

noncomputable section

namespace Wu18938Campaign.M1.Confirmed.Pair

open Wu2008DoubleSieve MotherPair Finset Real Filter
open scoped Classical Topology

theorem packing_admitted (p : SecondFunctionalParameters) (hp : AnalyticParameters p)
    (j : Term) (r : GainRectangle p j) (m : ℕ) {η δ : ℝ} (hη : 0 < η) (hδ : 0 < δ) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      packing N δ Δ V r ⊆ termLabels p j N δ (convolutionWuWindows N Δ V) := by
  obtain ⟨T0,hT04,h0⟩ := rectangle_admitted p hp j r m hη hδ
  obtain ⟨T1,_,h1⟩ := gain_mesh m hη hδ (show (0 : ℝ) < 1 by norm_num)
  refine ⟨max T0 T1,hT04.trans (le_max_left _ _),?_⟩
  intro N hN i Δ V hb
  obtain ⟨hΔ,hR,_⟩ := h1 N (by omega) i Δ V hb
  apply packing_subset_of_cells r hR hΔ
  intro a ha b hb'
  have hpa := gamma5Gain_point_bounds hR hΔ r.A_lt_B.le (mem_range.mp ha)
  have hqb := gamma5Gain_point_bounds hR hΔ r.C_lt_D.le (mem_range.mp hb')
  have hpm := (gamma5Gain_point_strictMono hR hΔ r.A).monotone (Nat.le_succ a)
  have hqm := (gamma5Gain_point_strictMono hR hΔ r.C).monotone (Nat.le_succ b)
  exact ((h0 N (by omega) i Δ V hb).2
    (gamma5GainEnd (gamma5GainScale N δ V) Δ r.A a)
    (gamma5GainEnd (gamma5GainScale N δ V) Δ r.C b)
    (rpow_le_rpow_of_exponent_le hR.le (hpa.1.trans hpm))
    (rpow_le_rpow_of_exponent_le hR.le hpa.2)
    (rpow_le_rpow_of_exponent_le hR.le (hqb.1.trans hqm))
    (rpow_le_rpow_of_exponent_le hR.le hqb.2)).1

theorem packing_inner (m : ℕ) {η δ τ : ℝ}
    (hη : 0 < η) (hδ : 0 < δ) (hτ : 0 < τ)
    {p : SecondFunctionalParameters} {j : Term} (r : GainRectangle p j) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      rectLabels N δ (convolutionWuWindows N Δ V)
        (r.A + τ) (r.B - τ) (r.C + τ) (r.D - τ) ⊆ packing N δ Δ V r := by
  obtain ⟨T,hT4,hT⟩ := gain_mesh m hη hδ (half_pos hτ)
  refine ⟨T,hT4,?_⟩
  intro N hN i Δ V hb x hx
  obtain ⟨hΔ,hR,hm⟩ := hT N hN i Δ V hb
  have hstep := gamma5Gain_step_pos hR hΔ
  have hsmall : ((m : ℝ) + 1) * gamma5GainStep (gamma5GainScale N δ V) Δ < τ / 2 := by
    simpa only [gamma5GainStep,mul_div_assoc] using hm
  have hstepτ : gamma5GainStep (gamma5GainScale N δ V) Δ < τ / 2 :=
    (le_mul_of_one_le_left hstep.le (by positivity : (1 : ℝ) ≤ m + 1)).trans_lt hsmall
  have him : (i : ℝ) ≤ (m : ℝ) + 1 := by exact_mod_cast hb.depth.trans (Nat.le_succ m)
  have hime : (i : ℝ) * log Δ / log (gamma5GainScale N δ V) < τ / 2 := by
    simpa only [gamma5GainStep,mul_div_assoc] using
      (mul_le_mul_of_nonneg_right him hstep.le).trans_lt hsmall
  obtain ⟨hxl,hp,hq,hpN,hqN,hpa,hpb,hqc,hqd,_⟩ := mem_filter.mp hx
  have hd := (mem_product.mp hxl).1
  have hRd := (hb.support_geometry (by omega) hη hδ hd).2.2.1
  have hp0 : (0 : ℝ) < x.2.1 := by exact_mod_cast hp.pos
  have hq0 : (0 : ℝ) < x.2.2 := by exact_mod_cast hq.pos
  have hRd0 : 0 < (N : ℝ) ^ (1 / 2 - δ) / x.1 := by linarith
  have hcoords : r.A + τ ≤ gamma5MassCoordinate ((N : ℝ) ^ (1 / 2 - δ) / x.1) x.2.1 ∧
      gamma5MassCoordinate ((N : ℝ) ^ (1 / 2 - δ) / x.1) x.2.1 < r.B - τ ∧
      r.C + τ ≤ gamma5MassCoordinate ((N : ℝ) ^ (1 / 2 - δ) / x.1) x.2.2 ∧
      gamma5MassCoordinate ((N : ℝ) ^ (1 / 2 - δ) / x.1) x.2.2 < r.D - τ := by
    refine ⟨?_,?_,?_,?_⟩
    · apply (le_div_iff₀ (log_pos hRd)).mpr
      simpa only [log_rpow hRd0] using log_le_log (rpow_pos_of_pos hRd0 _) hpa
    · apply (div_lt_iff₀ (log_pos hRd)).mpr
      simpa only [log_rpow hRd0] using log_lt_log hp0 hpb
    · apply (le_div_iff₀ (log_pos hRd)).mpr
      simpa only [log_rpow hRd0] using log_le_log (rpow_pos_of_pos hRd0 _) hqc
    · apply (div_lt_iff₀ (log_pos hRd)).mpr
      simpa only [log_rpow hRd0] using log_lt_log hq0 hqd
  have hqR : (x.2.2 : ℝ) ≤ (N : ℝ) ^ (1 / 2 - δ) / x.1 := by
    apply hqd.le.trans
    simpa only [rpow_one] using rpow_le_rpow_of_exponent_le hRd.le
      (show r.D - τ ≤ 1 by linarith [r.twiceD_lt_one])
  have hpR : (x.2.1 : ℝ) ≤ (N : ℝ) ^ (1 / 2 - δ) / x.1 := by
    apply hpb.le.trans
    simpa only [rpow_one] using rpow_le_rpow_of_exponent_le hRd.le
      (show r.B - τ ≤ 1 by linarith [r.B_lt_C,r.C_lt_D,r.twiceD_lt_one])
  have hpdr := coordinate_drift hb (by omega) hη hδ hR hΔ hd hp.one_le hpR
  have hqdr := coordinate_drift hb (by omega) hη hδ hR hΔ hd hq.one_le hqR
  have hpt := (gamma5Gain_terminal_bounds hR hΔ r.A_lt_B.le).2.2
  have hqt := (gamma5Gain_terminal_bounds hR hΔ r.C_lt_D.le).2.2
  refine mem_product.mpr ⟨hd,mem_product.mpr ⟨?_,?_⟩⟩
  · exact gamma5Gain_coordinate_window hR hp hpN (by linarith [hcoords.1])
      (by linarith [hcoords.2.1])
  · exact gamma5Gain_coordinate_window hR hq hqN (by linarith [hcoords.2.2.1])
      (by linarith [hcoords.2.2.2])

theorem packing_mass_lower (p : SecondFunctionalParameters) (hp : AnalyticParameters p)
    (j : Term) (r : GainRectangle p j) (m : ℕ) {η δ ε : ℝ}
    (hη : 0 < η) (hδ : 0 < δ) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      (rectIntegral r.A r.B r.C r.D - ε) *
        boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) ≤
      gamma5ClassicalMainMass N δ (convolutionWuWindows N Δ V) (packing N δ Δ V r) := by
  have hA : 1 / 10 ≤ r.A := by linarith [(parameter_order hp).1,r.lowerP_lt_A]
  obtain ⟨τ,hτ,hAB,hCD,hcoef⟩ := packing_inner_approx r hA (half_pos he)
  obtain ⟨T0,hT04,h0⟩ := packing_inner m hη hδ hτ r
  obtain ⟨T1,_,h1⟩ := packing_admitted p hp j r m hη hδ
  obtain ⟨T2,_,h2⟩ := rectangle_mass (le_rfl : (1 / 10 : ℝ) ≤ 1 / 10)
    (show r.D < 1 / 2 by linarith [r.twiceD_lt_one]) m hη hδ (half_pos he)
  refine ⟨max T0 (max T1 T2),hT04.trans (le_max_left _ _),?_⟩
  intro N hN i Δ V hb
  have hsub := h1 N (by omega) i Δ V hb
  have hmass := h2 N (by omega) i Δ V hb (r.A + τ) (r.B - τ) (r.C + τ) (r.D - τ)
    (by linarith) hAB.le (by linarith [r.B_lt_C,r.C_lt_D])
    (by linarith [r.A_lt_B,r.B_lt_C]) hCD.le (by linarith)
  have htheta := Rebox.theta_nonneg hb (by omega) hη hδ
  have hmono := term_mass_mono hb (by omega) hη hδ p hp j (h0 N (by omega) i Δ V hb) hsub
  have hpaid := mul_le_mul_of_nonneg_right hcoef.le htheta
  have hlow := (neg_le_abs _).trans hmass
  nlinarith only [hmono,hpaid,hlow]

end Wu18938Campaign.M1.Confirmed.Pair
