import MathlibNt.Wu2008DoubleSieve.MotherPairGainMass

noncomputable section

namespace WuPaper.R2Gamma5

open Finset Set Real Filter MeasureTheory Wu2008DoubleSieve
open Wu2008DoubleSieve.MotherPair
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418
open scoped Classical Topology Interval

structure FullParameters (p : SecondFunctionalParameters) : Prop
    extends AnalyticParameters p where
  ratio_lower : 1 ≤ p.S - 2 * p.S / p.kappa2

def FullRectangle (p : SecondFunctionalParameters) (A B C D : ℝ) : Prop :=
  1 / p.S ≤ A ∧ A ≤ B ∧ B ≤ 1 / p.kappa2 ∧
    1 / p.S ≤ C ∧ C ≤ D ∧ D ≤ 1 / p.kappa2

def localRatio (p : SecondFunctionalParameters) (N : ℕ) (δ : ℝ)
    (x : Gamma5ClassicalLabel) : ℝ :=
  p.S * (1 - gamma5MassCoordinate ((N : ℝ) ^ (1 / 2 - δ) / x.1) x.2.1 -
    gamma5MassCoordinate ((N : ℝ) ^ (1 / 2 - δ) / x.1) x.2.2)

def fullHMass {i : ℕ} (p : SecondFunctionalParameters) (N : ℕ) (δ : ℝ)
    (W : Fin i → Finset ℕ) (X : Finset Gamma5ClassicalLabel) : ℝ :=
  4 * logarithmicIntegral N * ∑ x ∈ X,
    wuImprovementLimit true δ (localRatio p N δ x) *
      ((convolutionCoeff W x.1 : ℝ) *
        wuSingularSeries (gamma5ClassicalProduct x * N) /
        ((Nat.totient (gamma5ClassicalProduct x) : ℝ) *
          log ((N : ℝ) ^ (1 / 2 - δ) / gamma5ClassicalProduct x)))

theorem rectangle_coordinates {i k N : ℕ} {δ Δ A B C D : ℝ}
    {V : Fin i → ℝ} (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1 / 2)
    (hb : wuSourceBox k δ N i Δ V) {x : Gamma5ClassicalLabel}
    (hx : x ∈ rectLabels N δ (convolutionWuWindows N Δ V) A B C D) :
    gamma5MassCoordinate ((N : ℝ) ^ (1 / 2 - δ) / x.1) x.2.1 ∈ Ico A B ∧
      gamma5MassCoordinate ((N : ℝ) ^ (1 / 2 - δ) / x.1) x.2.2 ∈ Ico C D := by
  obtain ⟨hm, hp, hq, _, _, hpa, hpb, hqc, hqd, _⟩ := mem_filter.mp hx
  have hR := (gamma5Mass_support_geometry hN hδ hδhi hb
    (mem_product.mp hm).1).2.2.1
  have hR0 : 0 < (N : ℝ) ^ (1 / 2 - δ) / x.1 := by linarith
  have hp0 : (0 : ℝ) < x.2.1 := by exact_mod_cast hp.pos
  have hq0 : (0 : ℝ) < x.2.2 := by exact_mod_cast hq.pos
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · apply (le_div_iff₀ (log_pos hR)).mpr
    simpa only [log_rpow hR0] using
      log_le_log (rpow_pos_of_pos hR0 _) hpa
  · apply (div_lt_iff₀ (log_pos hR)).mpr
    simpa only [log_rpow hR0] using log_lt_log hp0 hpb
  · apply (le_div_iff₀ (log_pos hR)).mpr
    simpa only [log_rpow hR0] using
      log_le_log (rpow_pos_of_pos hR0 _) hqc
  · apply (div_lt_iff₀ (log_pos hR)).mpr
    simpa only [log_rpow hR0] using log_lt_log hq0 hqd

theorem full_rectangle_subset {p : SecondFunctionalParameters}
    {i k N : ℕ} {δ Δ A B C D : ℝ} {V : Fin i → ℝ}
    (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1 / 2)
    (hb : wuSourceBox k δ N i Δ V) (hr : FullRectangle p A B C D) :
    rectLabels N δ (convolutionWuWindows N Δ V) A B C D ⊆
      termLabels p .gammaFive N δ (convolutionWuWindows N Δ V) := by
  intro x hx
  obtain ⟨hm, hp, hq, hpN, hqN, hpa, hpb, hqc, hqd, hpq⟩ := mem_filter.mp hx
  have hR := (gamma5Mass_support_geometry hN hδ hδhi hb
    (mem_product.mp hm).1).2.2.1
  exact mem_filter.mpr ⟨hm, hp, hq, hpN, hqN,
    (rpow_le_rpow_of_exponent_le hR.le hr.1).trans hpa,
    hpb.trans_le (rpow_le_rpow_of_exponent_le hR.le hr.2.2.1),
    (rpow_le_rpow_of_exponent_le hR.le hr.2.2.2.1).trans hqc,
    hqd.trans_le (rpow_le_rpow_of_exponent_le hR.le hr.2.2.2.2.2), hpq⟩

theorem full_ratio_mem {p : SecondFunctionalParameters} (hp : FullParameters p)
    {t u : ℝ} (ht : t ∈ Icc (1 / p.S) (1 / p.kappa2))
    (hu : u ∈ Icc (1 / p.S) (1 / p.kappa2)) :
    p.S * (1 - t - u) ∈ Set.Icc 1 3 := by
  have hS : 0 < p.S := by linarith [hp.three_le_S]
  have hSt := mul_le_mul_of_nonneg_left ht.1 hS.le
  have hSu := mul_le_mul_of_nonneg_left hu.1 hS.le
  have htk := mul_le_mul_of_nonneg_left ht.2 hS.le
  have huk := mul_le_mul_of_nonneg_left hu.2 hS.le
  simp only [mul_one_div, div_self hS.ne'] at hSt hSu htk huk
  constructor <;> nlinarith [hp.ratio_lower, hp.S_le_five]

theorem full_label_ratio_mem {p : SecondFunctionalParameters} (hp : FullParameters p)
    {i k N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1 / 2)
    (hb : wuSourceBox k δ N i Δ V) {x : Gamma5ClassicalLabel}
    (hx : x ∈ termLabels p .gammaFive N δ (convolutionWuWindows N Δ V)) :
    localRatio p N δ x ∈ Set.Icc 1 3 := by
  have hc := rectangle_coordinates hN hδ hδhi hb hx
  exact full_ratio_mem hp ⟨hc.1.1, hc.1.2.le⟩ ⟨hc.2.1, hc.2.2.le⟩

theorem full_sample_bounds {p : SecondFunctionalParameters} (hp : FullParameters p)
    {δ A B C D : ℝ} (hδ : 0 < δ) (hδhi : δ < 1 / 2)
    (hr : FullRectangle p A B C D) :
    0 ≤ wuImprovementLimit true δ (p.S * (1 - A - C)) ∧
      wuImprovementLimit true δ (p.S * (1 - A - C)) ≤ 1 := by
  have hs := full_ratio_mem hp ⟨hr.1, hr.2.1.trans hr.2.2.1⟩
    ⟨hr.2.2.2.1, hr.2.2.2.2.1.trans hr.2.2.2.2.2⟩
  have hh := wuImprovementLimit_bounds hδ hδhi hs.1 (by linarith [hs.2])
  refine ⟨hh.1, hh.2.1.trans_eq ?_⟩
  exact MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne.jr1965F_normalized_initial
    (by linarith [hs.1]) hs.2

theorem fullHMass_mono {p : SecondFunctionalParameters} (hp : FullParameters p)
    {i k N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1 / 2)
    (hb : wuSourceBox k δ N i Δ V) {X Y : Finset Gamma5ClassicalLabel}
    (hXY : X ⊆ Y)
    (hY : Y ⊆ termLabels p .gammaFive N δ (convolutionWuWindows N Δ V)) :
    fullHMass p N δ (convolutionWuWindows N Δ V) X ≤
      fullHMass p N δ (convolutionWuWindows N Δ V) Y := by
  have hli : 0 ≤ 4 * logarithmicIntegral N := by
    have hh := MathlibNt.SieveTheory.LiuWeight.liuLogarithmicIntegral_nonneg
      0 (by norm_num) (by exact_mod_cast hN : (2 : ℝ) ≤ N)
    positivity
  apply mul_le_mul_of_nonneg_left _ hli
  apply sum_le_sum_of_subset_of_nonneg hXY
  intro x hx _
  have hs := full_label_ratio_mem hp hN hδ hδhi hb (hY hx)
  exact mul_nonneg
    (wuImprovementLimit_nonneg true hδ hδhi hs.1 (by linarith [hs.2]))
    (term_mask_mass_summand_nonneg hp.toAnalyticParameters .gammaFive
      hN hδ hδhi hb (hY hx))

theorem fullHMass_rectangle_lower {p : SecondFunctionalParameters} (hp : FullParameters p)
    {i k N : ℕ} {δ Δ A B C D : ℝ} {V : Fin i → ℝ}
    (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1 / 2)
    (hb : wuSourceBox k δ N i Δ V) (hr : FullRectangle p A B C D) :
    wuImprovementLimit true δ (p.S * (1 - A - C)) *
        gamma5ClassicalMainMass N δ (convolutionWuWindows N Δ V)
          (rectLabels N δ (convolutionWuWindows N Δ V) A B C D) ≤
      fullHMass p N δ (convolutionWuWindows N Δ V)
        (rectLabels N δ (convolutionWuWindows N Δ V) A B C D) := by
  have hs := full_ratio_mem hp ⟨hr.1, hr.2.1.trans hr.2.2.1⟩
    ⟨hr.2.2.2.1, hr.2.2.2.2.1.trans hr.2.2.2.2.2⟩
  have hS : 0 ≤ p.S := by linarith [hp.three_le_S]
  have hli : 0 ≤ 4 * logarithmicIntegral N := by
    have hh := MathlibNt.SieveTheory.LiuWeight.liuLogarithmicIntegral_nonneg
      0 (by norm_num) (by exact_mod_cast hN : (2 : ℝ) ≤ N)
    positivity
  unfold gamma5ClassicalMainMass fullHMass
  rw [← mul_assoc, mul_comm (wuImprovementLimit true δ _), mul_assoc, mul_sum]
  apply mul_le_mul_of_nonneg_left _ hli
  apply sum_le_sum
  intro x hx
  have hxl := full_rectangle_subset hN hδ hδhi hb hr hx
  have hv := full_label_ratio_mem hp hN hδ hδhi hb hxl
  have hc := rectangle_coordinates hN hδ hδhi hb hx
  have hratio : localRatio p N δ x ≤ p.S * (1 - A - C) := by
    unfold localRatio
    exact mul_le_mul_of_nonneg_left (by linarith [hc.1.1, hc.2.1]) hS
  exact mul_le_mul_of_nonneg_right
    (wuImprovementLimit_upper_antitone_initial hδ hδhi hv hs hratio)
    (term_mask_mass_summand_nonneg hp.toAnalyticParameters .gammaFive
      hN hδ hδhi hb hxl)

theorem fullHMass_rectangle_producer (p : SecondFunctionalParameters)
    (hp : FullParameters p) (k : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ A B C D : ℝ, FullRectangle p A B C D →
        (wuImprovementLimit true δ (p.S * (1 - A - C)) *
            rectIntegral A B C D - ε) *
            boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) ≤
          fullHMass p N δ (convolutionWuWindows N Δ V)
            (rectLabels N δ (convolutionWuWindows N Δ V) A B C D) := by
  have ho := parameter_order hp.toAnalyticParameters
  have ha : 1 / 10 ≤ 1 / p.S := by linarith [ho.1]
  have hU : 1 / p.kappa2 < 1 / 2 :=
    ho.2.2.2.1.trans_le ho.2.2.2.2.1 |>.trans ho.2.2.2.2.2
  obtain ⟨T, hT4, hT⟩ := rectangle_mass ha (ho.2.1.trans ho.2.2.1.le)
    hU k hδ hδhi hε
  refine ⟨T, hT4, ?_⟩
  intro N hN i Δ V hb A B C D hr
  have hN2 : 2 ≤ N := by omega
  have hδhalf : δ < 1 / 2 := by linarith
  have hm := hT N hN i Δ V hb A B C D hr.1 hr.2.1 hr.2.2.1
    hr.2.2.2.1 hr.2.2.2.2.1 hr.2.2.2.2.2
  have hH := full_sample_bounds hp hδ hδhalf hr
  have hθ := gamma5Mass_theta_nonneg hN2 hδ hδhalf hb
  have hlow := (abs_le.mp hm).1
  have hweighted := mul_le_mul_of_nonneg_left hlow hH.1
  have herr := mul_le_mul_of_nonneg_right hH.2 (mul_nonneg hε.le hθ)
  have hpoint := fullHMass_rectangle_lower hp hN2 hδ hδhalf hb hr
  nlinarith only [hweighted, herr, hpoint]

#check @FullParameters
#print axioms FullParameters
#check @FullRectangle
#print axioms FullRectangle
#check @localRatio
#print axioms localRatio
#check @fullHMass
#print axioms fullHMass
#check @rectangle_coordinates
#print axioms rectangle_coordinates
#check @full_rectangle_subset
#print axioms full_rectangle_subset
#check @full_ratio_mem
#print axioms full_ratio_mem
#check @full_label_ratio_mem
#print axioms full_label_ratio_mem
#check @full_sample_bounds
#print axioms full_sample_bounds
#check @fullHMass_mono
#print axioms fullHMass_mono
#check @fullHMass_rectangle_lower
#print axioms fullHMass_rectangle_lower
#check @fullHMass_rectangle_producer
#print axioms fullHMass_rectangle_producer

end WuPaper.R2Gamma5
