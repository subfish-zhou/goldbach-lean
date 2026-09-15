import MathlibNt.Wu2008DoubleSieve.MotherPairGainPacking
import MathlibNt.Wu2008DoubleSieve.Gamma5GainRectangleIntegral

namespace Wu2008DoubleSieve.MotherPair
open Finset Set Real Filter MeasureTheory
open scoped Classical Topology Interval
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418

noncomputable def packingSmooth (U : ℝ) (v : ℝ × ℝ) : ℝ :=
  1 / (max (1/10:ℝ) v.1 * max (1/10:ℝ) v.2 * max (1-2*U) (1-v.1-v.2))

theorem packing_smooth_continuous {U : ℝ} (hU : U < 1/2) : Continuous (packingSmooth U) := by
  have hd (v : ℝ × ℝ) : 0 < max (1/10:ℝ) v.1 * max (1/10:ℝ) v.2 *
      max (1-2*U) (1-v.1-v.2) :=
    mul_pos (mul_pos ((by norm_num : (0:ℝ)<1/10).trans_le (le_max_left _ _))
      ((by norm_num : (0:ℝ)<1/10).trans_le (le_max_left _ _)))
      ((by linarith : 0<1-2*U).trans_le (le_max_left _ _))
  exact continuous_const.div (by fun_prop) (fun v => (hd v).ne')

theorem packing_smooth_eq {U t u : ℝ}
    (ht : t ∈ Icc (1/10:ℝ) U) (hu : u ∈ Icc (1/10:ℝ) U) :
    packingSmooth U (t,u) = gamma5MassKernel t u := by
  simp only [packingSmooth, gamma5MassKernel, max_eq_right ht.1, max_eq_right hu.1,
    max_eq_right (show 1-2*U ≤ 1-t-u by linarith [ht.2,hu.2])]

noncomputable def packingSmoothRectangle (U A B C D : ℝ) : ℝ :=
  ∫ t in A..B, ∫ u in C..D, packingSmooth U (t,u)

theorem packing_smooth_rectangle_continuous {U : ℝ} (hU : U < 1/2) :
    Continuous (fun z : ℝ × ℝ × ℝ × ℝ => packingSmoothRectangle U z.1 z.2.1 z.2.2.1 z.2.2.2) := by
  unfold packingSmoothRectangle
  apply gamma5Gain_moving_integral
  · apply gamma5Gain_moving_integral
    · exact (packing_smooth_continuous hU).comp (by fun_prop)
    · fun_prop
    · fun_prop
  · fun_prop
  · fun_prop

theorem packing_smooth_rectangle_eq {U A B C D : ℝ}
    (hA : 1/10 ≤ A) (hAB : A ≤ B) (hBC : B ≤ C) (hCD : C ≤ D) (hD : D ≤ U) :
    packingSmoothRectangle U A B C D = rectIntegral A B C D := by
  unfold packingSmoothRectangle rectIntegral
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ Icc A B := by simpa only [uIcc_of_le hAB] using ht
  dsimp only
  simp only [max_eq_left (ht'.2.trans hBC), min_eq_right hCD]
  apply intervalIntegral.integral_congr
  intro u hu
  have hu' : u ∈ Icc C D := by simpa only [uIcc_of_le hCD] using hu
  exact packing_smooth_eq ⟨hA.trans ht'.1,ht'.2.trans (hBC.trans (hCD.trans hD))⟩
    ⟨hA.trans (hAB.trans (hBC.trans hu'.1)),hu'.2.trans hD⟩

theorem packing_inner_approx {p : SecondFunctionalParameters} {j : Term} (r : GainRectangle p j)
    (hA0 : 1/10 ≤ r.A) {ε : ℝ} (hε : 0 < ε) :
    ∃ τ : ℝ, 0 < τ ∧ r.A + τ < r.B - τ ∧ r.C + τ < r.D - τ ∧
      rectIntegral r.A r.B r.C r.D - ε <
        rectIntegral (r.A + τ) (r.B - τ) (r.C + τ) (r.D - τ) := by
  have ht : Tendsto (fun τ : ℝ =>
      packingSmoothRectangle r.D (r.A + τ) (r.B - τ) (r.C + τ) (r.D - τ))
      (𝓝 0) (𝓝 (packingSmoothRectangle r.D r.A r.B r.C r.D)) := by
    have hc : Continuous (fun τ : ℝ => (r.A + τ, r.B - τ, r.C + τ, r.D - τ)) := by fun_prop
    simpa only [Function.comp_def, add_zero, sub_zero] using
      ((packing_smooth_rectangle_continuous (by linarith [r.twiceD_lt_one] : r.D < 1/2)).comp hc).continuousAt.tendsto (x := (0 : ℝ))
  have he := ht.eventually (lt_mem_nhds (sub_lt_self _ hε))
  have hab : ∀ᶠ τ : ℝ in 𝓝 0, r.A + τ < r.B - τ :=
    (isOpen_lt (by fun_prop) (by fun_prop)).mem_nhds (by simpa using r.A_lt_B)
  have hcd : ∀ᶠ τ : ℝ in 𝓝 0, r.C + τ < r.D - τ :=
    (isOpen_lt (by fun_prop) (by fun_prop)).mem_nhds (by simpa using r.C_lt_D)
  obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff.mp (hab.and (hcd.and he))
  let τ := ρ / 2
  have hτ : 0 < τ := half_pos hρ
  obtain ⟨hA, hC, hI⟩ := hball (show dist τ 0 < ρ by
    rw [Real.dist_eq, sub_zero, abs_of_pos hτ]
    dsimp [τ]
    linarith)
  refine ⟨τ, hτ, hA, hC, ?_⟩
  rw [packing_smooth_rectangle_eq hA0 r.A_lt_B.le r.B_lt_C.le r.C_lt_D.le le_rfl,
    packing_smooth_rectangle_eq (by linarith) hA.le
      (by linarith [r.B_lt_C]) hC.le (by linarith)] at hI
  exact hI

theorem term_mask_mass_summand_nonneg {p : SecondFunctionalParameters} (h : AnalyticParameters p) (j : Term) {i k N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hb : wuSourceBox k δ N i Δ V)
    {x : Gamma5ClassicalLabel} (hx : x ∈ termLabels p j N δ (convolutionWuWindows N Δ V)) :
    0 ≤ (convolutionCoeff (convolutionWuWindows N Δ V) x.1 : ℝ) *
      wuSingularSeries (gamma5ClassicalProduct x * N) /
        ((Nat.totient (gamma5ClassicalProduct x) : ℝ) *
          log ((N : ℝ) ^ (1 / 2 - δ) / gamma5ClassicalProduct x)) := by
  have hg := classical_label_geometry (classical_cap h) hN hδ hδhi hb
    (termLabels_subset_cap h j hN hδ hδhi hb hx)
  have hs := wuSingularSeries_pos (gamma5ClassicalProduct x * N)
    (Nat.mul_pos hg.product_pos (by omega))
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) hs.le)
    (mul_nonneg (Nat.cast_nonneg _) (log_pos hg.level_gt_one).le)

theorem term_mask_mass_mono {p : SecondFunctionalParameters} (h : AnalyticParameters p) (j : Term) {i k N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hb : wuSourceBox k δ N i Δ V)
    {X Y : Finset Gamma5ClassicalLabel} (hXY : X ⊆ Y)
    (hY : Y ⊆ termLabels p j N δ (convolutionWuWindows N Δ V)) :
    gamma5ClassicalMainMass N δ (convolutionWuWindows N Δ V) X ≤
      gamma5ClassicalMainMass N δ (convolutionWuWindows N Δ V) Y := by
  have hli : 0 ≤ 4 * logarithmicIntegral N :=
    mul_nonneg (by norm_num) (MathlibNt.SieveTheory.LiuWeight.liuLogarithmicIntegral_nonneg
      0 (by norm_num) (by exact_mod_cast hN))
  apply mul_le_mul_of_nonneg_left _ hli
  exact sum_le_sum_of_subset_of_nonneg hXY
    (fun x hx _ => term_mask_mass_summand_nonneg h j hN hδ hδhi hb (hY hx))

theorem term_mask_mass_nonneg {p : SecondFunctionalParameters} (h : AnalyticParameters p) (j : Term) {i k N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hb : wuSourceBox k δ N i Δ V)
    {X : Finset Gamma5ClassicalLabel}
    (hX : X ⊆ termLabels p j N δ (convolutionWuWindows N Δ V)) :
    0 ≤ gamma5ClassicalMainMass N δ (convolutionWuWindows N Δ V) X := by
  simpa only [gamma5ClassicalMainMass, sum_empty, mul_zero] using
    term_mask_mass_mono h j hN hδ hδhi hb (empty_subset X) hX

theorem packing_contains_inner {p : SecondFunctionalParameters} {j : Term} (k : ℕ) {δ τ : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) (hτ : 0 < τ) (r : GainRectangle p j) :
    ∀ᶠ N : ℕ in atTop, ∀ i : ℕ, ∀ Δ : ℝ, ∀ V : Fin i → ℝ,
      wuSourceBox k δ N i Δ V →
      rectLabels N δ (convolutionWuWindows N Δ V)
        (r.A + τ) (r.B - τ) (r.C + τ) (r.D - τ) ⊆ packing N δ Δ V r := by
  filter_upwards [gamma5Gain_mesh_eventually k hδ hδhi (half_pos hτ),
    eventually_ge_atTop (2 : ℕ)] with N hm hN
  intro i Δ V hb x hx
  have hh := hm i Δ V hb
  have hstep := gamma5Gain_step_pos hh.2.1 hh.1
  have hsmall : ((k : ℝ) + 1) * gamma5GainStep (gamma5GainScale N δ V) Δ < τ / 2 := by
    simpa only [gamma5GainStep, mul_div_assoc] using hh.2.2
  have hstepτ : gamma5GainStep (gamma5GainScale N δ V) Δ < τ / 2 :=
    (le_mul_of_one_le_left hstep.le
      (by linarith [show (0 : ℝ) ≤ k by positivity] : (1 : ℝ) ≤ (k : ℝ) + 1)).trans_lt hsmall
  have him : (i : ℝ) ≤ (k : ℝ) + 1 := by exact_mod_cast hb.1.trans (Nat.le_succ k)
  have hime : (i : ℝ) * log Δ / log (gamma5GainScale N δ V) < τ / 2 := by
    simpa only [gamma5GainStep, mul_div_assoc] using
      (mul_le_mul_of_nonneg_right him hstep.le).trans_lt hsmall
  obtain ⟨hxl,hp,hq,hpN,hqN,hpa,hpb,hqc,hqd,_⟩ := mem_filter.mp hx
  have hd := (mem_product.mp hxl).1
  have hRd := (gamma5Mass_support_geometry hN hδ (by linarith) hb hd).2.2.1
  have hp0 : (0:ℝ)<x.2.1 := by exact_mod_cast hp.pos
  have hq0 : (0:ℝ)<x.2.2 := by exact_mod_cast hq.pos
  have hRd0 : 0<(N:ℝ)^(1/2-δ)/x.1 := by linarith
  have hcoords : r.A+τ ≤ gamma5MassCoordinate ((N:ℝ)^(1/2-δ)/x.1) x.2.1 ∧
      gamma5MassCoordinate ((N:ℝ)^(1/2-δ)/x.1) x.2.1 < r.B-τ ∧
      r.C+τ ≤ gamma5MassCoordinate ((N:ℝ)^(1/2-δ)/x.1) x.2.2 ∧
      gamma5MassCoordinate ((N:ℝ)^(1/2-δ)/x.1) x.2.2 < r.D-τ := by
    refine ⟨?_,?_,?_,?_⟩
    · apply (le_div_iff₀ (log_pos hRd)).mpr
      simpa only [log_rpow hRd0] using log_le_log (rpow_pos_of_pos hRd0 _) hpa
    · apply (div_lt_iff₀ (log_pos hRd)).mpr
      simpa only [log_rpow hRd0] using log_lt_log hp0 hpb
    · apply (le_div_iff₀ (log_pos hRd)).mpr
      simpa only [log_rpow hRd0] using log_le_log (rpow_pos_of_pos hRd0 _) hqc
    · apply (div_lt_iff₀ (log_pos hRd)).mpr
      simpa only [log_rpow hRd0] using log_lt_log hq0 hqd
  have hqR : (x.2.2:ℝ) ≤ (N:ℝ)^(1/2-δ)/x.1 := by
    apply hqd.le.trans
    simpa only [rpow_one] using rpow_le_rpow_of_exponent_le hRd.le
      (show r.D-τ ≤ 1 by linarith [r.twiceD_lt_one])
  have hpR : (x.2.1:ℝ) ≤ (N:ℝ)^(1/2-δ)/x.1 := by
    apply hpb.le.trans
    simpa only [rpow_one] using rpow_le_rpow_of_exponent_le hRd.le
      (show r.B-τ ≤ 1 by linarith [r.B_lt_C,r.C_lt_D,r.twiceD_lt_one])
  have hpd := gamma5Gain_coordinate_drift hN hδ hδhi hb hd hp.one_le hpR
  have hqd := gamma5Gain_coordinate_drift hN hδ hδhi hb hd hq.one_le hqR
  have hpt := (gamma5Gain_terminal_bounds hh.2.1 hh.1 r.A_lt_B.le).2.2
  have hqt := (gamma5Gain_terminal_bounds hh.2.1 hh.1 r.C_lt_D.le).2.2
  refine mem_product.mpr ⟨hd, mem_product.mpr ⟨?_, ?_⟩⟩
  · exact gamma5Gain_coordinate_window hh.2.1 hp hpN (by linarith [hcoords.1])
      (by linarith [hcoords.2.1])
  · exact gamma5Gain_coordinate_window hh.2.1 hq hqN (by linarith [hcoords.2.2.1])
      (by linarith [hcoords.2.2.2])

theorem packing_mass (p : SecondFunctionalParameters) (h : AnalyticParameters p)
    (j : Term) (r : GainRectangle p j) (k : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1/10) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ i : ℕ, ∀ Δ : ℝ, ∀ V : Fin i → ℝ, wuSourceBox k δ N i Δ V →
      (rectIntegral r.A r.B r.C r.D-ε)*
        boxTheta N ((N:ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) ≤
      gamma5ClassicalMainMass N δ (convolutionWuWindows N Δ V) (packing N δ Δ V r) := by
  have hA : 1/10 ≤ r.A := by linarith [(parameter_order h).1,r.lowerP_lt_A]
  obtain ⟨τ,hτ,hAB,hCD,hcoef⟩ := packing_inner_approx r hA (half_pos hε)
  obtain ⟨TI,hi⟩ := eventually_atTop.mp (packing_contains_inner k hδ hδhi hτ r)
  obtain ⟨TA,ha⟩ := eventually_atTop.mp (packing_admission p h j r k hδ hδhi)
  obtain ⟨TM,hTM,hm⟩ := rectangle_mass (le_rfl : (1/10:ℝ) ≤ 1/10)
    (show 1/10 ≤ r.D by linarith [r.A_lt_B,r.B_lt_C,r.C_lt_D])
    (show r.D < 1/2 by linarith [r.twiceD_lt_one]) k hδ hδhi (half_pos hε)
  refine ⟨max TM (max TI TA),hTM.trans (le_max_left _ _),?_⟩
  intro N hN i Δ V hb
  have hNM : TM ≤ N := (le_max_left _ _).trans hN
  have hNI : TI ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hNA : TA ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  have hN2 : 2 ≤ N := by have := hTM.trans hNM; omega
  have hsub := ha N hNA i Δ V hb
  have hmass := hm N hNM i Δ V hb (r.A+τ) (r.B-τ) (r.C+τ) (r.D-τ)
    (by linarith) hAB.le (by linarith [r.B_lt_C,r.C_lt_D])
    (by linarith [r.A_lt_B,r.B_lt_C]) hCD.le (by linarith)
  have htheta := gamma5Mass_theta_nonneg hN2 hδ (by linarith) hb
  have hmono := term_mask_mass_mono h j hN2 hδ (by linarith) hb (hi N hNI i Δ V hb) hsub
  have hpaid := mul_le_mul_of_nonneg_right hcoef.le htheta
  have hlow := (neg_le_abs _).trans hmass
  nlinarith

end Wu2008DoubleSieve.MotherPair
