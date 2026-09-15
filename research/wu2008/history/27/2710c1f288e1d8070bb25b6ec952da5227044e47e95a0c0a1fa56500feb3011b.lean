import MathlibNt.Wu2008DoubleSieve.Gamma6GainIntegral
import MathlibNt.Wu2008DoubleSieve.Gamma6GainPacking

namespace Wu2008DoubleSieve

open Finset Set Real Filter
open scoped Classical Topology
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418

theorem gamma6Gain_mass_summand_nonneg {i k N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hb : wuSourceBox k δ N i Δ V)
    {x : Gamma5ClassicalLabel} (hx : x ∈ gamma6BaseLabels N δ (convolutionWuWindows N Δ V)) :
    0 ≤ (convolutionCoeff (convolutionWuWindows N Δ V) x.1 : ℝ) *
      wuSingularSeries (gamma5ClassicalProduct x * N) /
        ((Nat.totient (gamma5ClassicalProduct x) : ℝ) *
          log ((N : ℝ) ^ (1 / 2 - δ) / gamma5ClassicalProduct x)) := by
  have hg := gamma6Base_label_geometry hN hδ hδhi hb hx
  have hs := wuSingularSeries_pos (gamma5ClassicalProduct x * N)
    (Nat.mul_pos hg.product_pos (by omega))
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) hs.le)
    (mul_nonneg (Nat.cast_nonneg _) (log_pos hg.level_gt_one).le)

theorem gamma6Gain_mass_mono {i k N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hb : wuSourceBox k δ N i Δ V)
    {X Y : Finset Gamma5ClassicalLabel} (hXY : X ⊆ Y)
    (hY : Y ⊆ gamma6BaseLabels N δ (convolutionWuWindows N Δ V)) :
    gamma5ClassicalMainMass N δ (convolutionWuWindows N Δ V) X ≤
      gamma5ClassicalMainMass N δ (convolutionWuWindows N Δ V) Y := by
  have hli : 0 ≤ 4 * logarithmicIntegral N :=
    mul_nonneg (by norm_num) (MathlibNt.SieveTheory.LiuWeight.liuLogarithmicIntegral_nonneg
      0 (by norm_num) (by exact_mod_cast hN))
  apply mul_le_mul_of_nonneg_left _ hli
  exact sum_le_sum_of_subset_of_nonneg hXY
    (fun x hx _ => gamma6Gain_mass_summand_nonneg hN hδ hδhi hb (hY hx))

theorem gamma6Gain_mass_nonneg {i k N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hb : wuSourceBox k δ N i Δ V)
    {X : Finset Gamma5ClassicalLabel}
    (hX : X ⊆ gamma6BaseLabels N δ (convolutionWuWindows N Δ V)) :
    0 ≤ gamma5ClassicalMainMass N δ (convolutionWuWindows N Δ V) X := by
  simpa only [gamma5ClassicalMainMass, sum_empty, mul_zero] using
    gamma6Gain_mass_mono hN hδ hδhi hb (empty_subset X) hX

theorem gamma6Gain_packing_contains_inner (k : ℕ) {δ τ : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) (hτ : 0 < τ) (r : Gamma6GainRectangle) :
    ∀ᶠ N : ℕ in atTop, ∀ i : ℕ, ∀ Δ : ℝ, ∀ V : Fin i → ℝ,
      wuSourceBox k δ N i Δ V →
      gamma6BaseRectLabels N δ (convolutionWuWindows N Δ V)
        (r.A + τ) (r.B - τ) (r.C + τ) (r.D - τ) ⊆ gamma6GainPacking N δ Δ V r := by
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
  obtain ⟨hxl, hcoords⟩ := mem_filter.mp hx
  obtain ⟨hd, hp, hq, hpN, hqN, _hz, hpu, hql, hqu⟩ :=
    (gamma6Base_mem_labels_iff hN hδ (by linarith) hb x).mp hxl
  have hRd := (gamma5Mass_support_geometry hN hδ (by linarith) hb hd).2.2.1
  have hpow := rpow_le_rpow_of_exponent_le hRd.le
    (by norm_num [gamma6BaseF] : gamma6BaseF ≤ 1)
  rw [rpow_one] at hpow
  have hqR : (x.2.2 : ℝ) ≤ (N : ℝ) ^ (1 / 2 - δ) / x.1 := hqu.le.trans hpow
  have hpR : (x.2.1 : ℝ) ≤ (N : ℝ) ^ (1 / 2 - δ) / x.1 :=
    (gamma6Base_prime_order hRd hpu hql).le.trans hqR
  have hpd := gamma5Gain_coordinate_drift hN hδ hδhi hb hd hp.one_le hpR
  have hqd := gamma5Gain_coordinate_drift hN hδ hδhi hb hd hq.one_le hqR
  have hpt := (gamma5Gain_terminal_bounds hh.2.1 hh.1 r.first.le).2.2
  have hqt := (gamma5Gain_terminal_bounds hh.2.1 hh.1 r.second.le).2.2
  refine mem_product.mpr ⟨hd, mem_product.mpr ⟨?_, ?_⟩⟩
  · exact gamma5Gain_coordinate_window hh.2.1 hp hpN (by linarith [hcoords.1])
      (by linarith [hcoords.2.1])
  · exact gamma5Gain_coordinate_window hh.2.1 hq hqN (by linarith [hcoords.2.2.1])
      (by linarith [hcoords.2.2.2])

theorem gamma6Gain_packing_mass (k : ℕ) (hk : 1 ≤ k) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) (hε : 0 < ε) (r : Gamma6GainRectangle) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ i : ℕ, ∀ Δ : ℝ, ∀ V : Fin i → ℝ, wuSourceBox k δ N i Δ V →
      (gamma6BaseIntegral r.A r.B r.C r.D - ε) *
        boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) ≤
      gamma5ClassicalMainMass N δ (convolutionWuWindows N Δ V) (gamma6GainPacking N δ Δ V r) := by
  obtain ⟨τ, hτ, hAB, hCD, hcoef⟩ := gamma6Gain_rectangle_inner_approx r (half_pos hε)
  obtain ⟨TI, hi⟩ := eventually_atTop.mp (gamma6Gain_packing_contains_inner k hδ hδhi hτ r)
  obtain ⟨TA, ha⟩ := eventually_atTop.mp (gamma6Gain_rectangle_admission k hδ hδhi r)
  obtain ⟨TM, hTM, hm⟩ := gamma6Base_rectangle_mass k hk hδ hδhi (half_pos hε)
  refine ⟨max TM (max TI TA), hTM.trans (le_max_left _ _), ?_⟩
  intro N hN i Δ V hb
  have hNM : TM ≤ N := (le_max_left _ _).trans hN
  have hNI : TI ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hNA : TA ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  have hN2 : 2 ≤ N := by have := hTM.trans hNM; omega
  have had := ha N hNA i Δ V hb
  have hsub := fun x hx => (had.2.2 x (gamma6Gain_packing_coarse had.2.1 had.1 r hx)).1
  have hmass := hm N hNM i Δ V hb (r.A + τ) (r.B - τ) (r.C + τ) (r.D - τ)
    (by linarith [r.lower]) hAB.le (by linarith [r.firstUpper])
    (by linarith [r.secondLower]) hCD.le (by linarith [r.upper])
  have htheta := gamma5Mass_theta_nonneg hN2 hδ (by linarith) hb
  have hmono := gamma6Gain_mass_mono hN2 hδ (by linarith) hb (hi N hNI i Δ V hb) hsub
  have hpaid := mul_le_mul_of_nonneg_right hcoef.le htheta
  have hlow := (neg_le_abs _).trans hmass
  nlinarith

end Wu2008DoubleSieve
