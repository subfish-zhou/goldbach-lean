import MathlibNt.Wu2008DoubleSieve.Gamma6BaseGeometry

/-! # Actual arbitrary-mask Gamma6 classical upper -/

namespace Wu2008DoubleSieve

open Finset Real Filter
open scoped Classical Topology
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne

theorem gamma6Base_windows_eventually (k : ℕ) {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) :
    ∀ᶠ N : ℕ in atTop, ∀ i : ℕ, ∀ Δ : ℝ, ∀ V : Fin i → ℝ,
      wuSourceBox k δ N i Δ V →
      (∀ j p, p ∈ convolutionWuWindows N Δ V j →
        p.Prime ∧ p.Coprime N ∧ (N : ℝ) ^ (gamma5ClassicalAlpha k δ) ≤ (p : ℝ)) ∧
      gamma6BaseLabels N δ (convolutionWuWindows N Δ V) ⊆
        boxConvolutionSupport (convolutionWuWindows N Δ V) ×ˢ
          (gamma5ClassicalLargePrimes N (gamma5ClassicalAlpha k δ) ×ˢ
            gamma5ClassicalLargePrimes N (gamma5ClassicalAlpha k δ)) := by
  filter_upwards [gamma5Classical_windows_eventually k hδ hδhi,
    eventually_ge_atTop (2 : ℕ)] with N hw hN
  intro i Δ V hb
  refine ⟨(hw i Δ V hb).1, ?_⟩
  intro x hx
  have hg := gamma6Base_label_geometry hN hδ hδhi hb hx
  obtain ⟨ha, hp, hq, hpN, hqN, _⟩ := mem_filter.mp hx
  obtain ⟨hd, hpqrange⟩ := mem_product.mp ha
  obtain ⟨hprange, hqrange⟩ := mem_product.mp hpqrange
  exact mem_product.mpr ⟨hd, mem_product.mpr
    ⟨mem_filter.mpr ⟨hprange, hp, hpN, hg.prime_lower⟩,
      mem_filter.mpr ⟨hqrange, hq, hqN,
        hg.prime_lower.trans (by exact_mod_cast hg.prime_order.le)⟩⟩⟩

theorem gamma6Base_masked_bombieri_vinogradov (k : ℕ) {δ A : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∃ T : ℕ, ∀ N : ℕ, T ≤ N →
      ∀ i : ℕ, ∀ Δ : ℝ, ∀ V : Fin i → ℝ, wuSourceBox k δ N i Δ V →
      ∀ X : Finset Gamma5ClassicalLabel,
        X ⊆ gamma6BaseLabels N δ (convolutionWuWindows N Δ V) →
      ∀ z : Gamma5ClassicalLabel → ℝ,
        |gamma5ClassicalRemainder N δ (convolutionWuWindows N Δ V) X z| ≤
          C * (N : ℝ) / log N ^ A := by
  have hα := (gamma5Classical_exponents_pos k hδ hδhi).1
  obtain ⟨C, hC, T, hBV⟩ := convolution_bombieri_vinogradov (k + 2) hα hδ hA
  refine ⟨C, hC, ?_⟩
  apply eventually_atTop.mp
  filter_upwards [eventually_ge_atTop T, gamma6Base_windows_eventually k hδ hδhi]
    with N hT hw
  intro i Δ V hbox X hX z
  obtain ⟨hW, hlabels⟩ := hw i Δ V hbox
  let P := gamma5ClassicalLargePrimes N (gamma5ClassicalAlpha k δ)
  have hP : ∀ p ∈ P, p.Prime ∧ p.Coprime N ∧
      (N : ℝ) ^ gamma5ClassicalAlpha k δ ≤ (p : ℝ) :=
    fun p hp => (mem_filter.mp hp).2
  apply (gamma5Classical_masked_remainder_le N δ _ P X (hX.trans hlabels) z).trans
  apply hBV N hT (i + 1 + 1) (by have := hbox.1; omega)
  intro j
  exact Fin.cases hP (fun j => Fin.cases hP hW j) j

theorem gamma6Base_remainder_relative (k : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hε : 0 < ε) :
    ∃ T : ℕ, ∀ N : ℕ, T ≤ N →
      ∀ i : ℕ, ∀ Δ : ℝ, ∀ V : Fin i → ℝ, wuSourceBox k δ N i Δ V →
      ∀ X : Finset Gamma5ClassicalLabel,
        X ⊆ gamma6BaseLabels N δ (convolutionWuWindows N Δ V) →
      ∀ z : Gamma5ClassicalLabel → ℝ,
        |gamma5ClassicalRemainder N δ (convolutionWuWindows N Δ V) X z| ≤
          ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  obtain ⟨C, hC, T1, hBV⟩ := gamma6Base_masked_bombieri_vinogradov k hδ hδhi
    (show (0 : ℝ) < (5 * k + 6 : ℕ) by positivity)
  obtain ⟨c, hc, T2, hTheta⟩ := wu_boxTheta_lower k hδ hδhi
  have hlogTop : Tendsto (fun N : ℕ => log (N : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlog4 := (tendsto_pow_atTop (show (4 : ℕ) ≠ 0 by norm_num)).comp hlogTop
  apply eventually_atTop.mp
  filter_upwards [eventually_ge_atTop T1, eventually_ge_atTop T2,
    eventually_ge_atTop (2 : ℕ),
    hlog4.eventually (eventually_ge_atTop (C / (ε * c)))]
      with N hT1 hT2 hN hbudget
  intro i Δ V hbox X hX z
  have hlog : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  have hB := hBV N hT1 i Δ V hbox X hX z
  rw [rpow_natCast] at hB
  have hT := hTheta N hT2 i hbox.1 Δ hbox.2.1 hbox.2.2.1 V
    hbox.2.2.2.2.1 hbox.2.2.2.2.2
  have hpay : C / log N ^ 4 ≤ ε * c := by
    apply (div_le_iff₀ (pow_pos hlog 4)).mpr
    have h := (div_le_iff₀ (mul_pos hε hc)).mp hbudget
    simpa only [Function.comp_apply, mul_comm] using h
  calc
    _ ≤ C * N / log N ^ (5 * k + 6) := hB
    _ = (C / log N ^ 4) * ((N : ℝ) / log N ^ (5 * k + 2)) := by
      rw [show 5 * k + 6 = (5 * k + 2) + 4 by omega, pow_add]
      ring
    _ ≤ (ε * c) * ((N : ℝ) / log N ^ (5 * k + 2)) :=
      mul_le_mul_of_nonneg_right hpay (by positivity)
    _ = ε * (c * (N : ℝ) / log N ^ (5 * k + 2)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hT hε.le

theorem gamma6Base_density_eventually (k : ℕ) {δ η : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hη : 0 < η) :
    ∃ T : ℕ, ∀ N : ℕ, T ≤ N → Even N →
      ∀ i : ℕ, ∀ Δ : ℝ, ∀ V : Fin i → ℝ, wuSourceBox k δ N i Δ V →
      ∀ x ∈ gamma6BaseLabels N δ (convolutionWuWindows N Δ V),
        ordinaryRosserMainSum true N (gamma5ClassicalProduct x)
          (wuVariableRosserLevel N δ (gamma5ClassicalProduct x))
          (gamma5ClassicalCutoff N δ x) ≤
        (1 + η) ^ 2 * (4 * wuSingularSeries (gamma5ClassicalProduct x * N) /
          log (gamma5ClassicalLevel N δ x)) := by
  let ρ : ℝ := 2 * exp eulerMascheroniConstant * η / 3
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hζ := gamma6Base_zeta_pos k hδ hδhi
  obtain ⟨ZD, hden⟩ := ordinaryRosser_upper_density_canonical_bounded_local hρ
  obtain ⟨ZE, hEuler⟩ := eventually_atTop.mp
    (eventually_localSieveProduct_relative (2 / gamma6BaseZeta k δ) η
      (by positivity) hη)
  have hlarge : ∀ᶠ N : ℕ in atTop,
      max 2 (max ZD ZE) ≤ (N : ℝ) ^ gamma6BaseZeta k δ :=
    ((tendsto_rpow_atTop hζ).comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop _)
  apply eventually_atTop.mp
  filter_upwards [hlarge, eventually_ge_atTop (2 : ℕ)] with N hlargeN hN
  intro he i Δ V hbox x hx
  have hg := gamma6Base_label_geometry hN hδ hδhi hbox hx
  let L := gamma5ClassicalLevel N δ x
  let z := gamma5ClassicalCutoff N δ x
  let r := log L / log z
  have hlL : 0 < log L := log_pos hg.level_gt_one
  have hlz : 0 < log z := log_pos hg.cutoff_gt_one
  have hr0 : 0 < r := div_pos hlL hlz
  have hr2 : r = 2 := hg.ratio_eq
  have hr3 : r ≤ 3 := by linarith
  have hzlarge : max 2 (max ZD ZE) ≤ z := hlargeN.trans hg.cutoff_lower
  have hz2 : 2 ≤ z := (le_max_left _ _).trans hzlarge
  have hzD : ZD ≤ z := (le_max_left _ _).trans ((le_max_right _ _).trans hzlarge)
  have hzE : ZE ≤ z := (le_max_right _ _).trans ((le_max_right _ _).trans hzlarge)
  have hdensity := hden N (gamma5ClassicalProduct x) he z L r hzD hz2
    (by linarith [hg.level_gt_one]) rfl (by linarith) (by linarith)
  have hMN : 0 < gamma5ClassicalProduct x * N :=
    Nat.mul_pos hg.product_pos (by omega)
  have hC : 0 < wuSingularSeries (gamma5ClassicalProduct x * N) :=
    wuSingularSeries_pos _ hMN
  have hnorm := hEuler z hzE (gamma5ClassicalProduct x * N) hMN
    (he.mul_left _) (gamma6Base_polynomial_envelope hζ hg)
  have hbase : 0 < 2 * exp (-eulerMascheroniConstant) *
      wuSingularSeries (gamma5ClassicalProduct x * N) / log z := by positivity
  have hprod : localSieveProduct (gamma5ClassicalProduct x * N) z ≤
      (1 + η) * (2 * r * wuSingularSeries (gamma5ClassicalProduct x * N) /
        (exp eulerMascheroniConstant * log L)) := by
    have hratio :
        localSieveProduct (gamma5ClassicalProduct x * N) z /
          (2 * exp (-eulerMascheroniConstant) *
            wuSingularSeries (gamma5ClassicalProduct x * N) / log z) ≤ 1 + η := by
      linarith [(le_abs_self (_ : ℝ)).trans hnorm]
    have h := (div_le_iff₀ hbase).mp hratio
    have heq : 2 * exp (-eulerMascheroniConstant) *
        wuSingularSeries (gamma5ClassicalProduct x * N) / log z =
      2 * r * wuSingularSeries (gamma5ClassicalProduct x * N) /
        (exp eulerMascheroniConstant * log L) := by
      rw [exp_neg]
      dsimp [r]
      field_simp
    rwa [heq] at h
  have hF : 0 ≤ jr1965F r + ρ := by
    rw [jr1965F_eq_of_le_three hr3]
    positivity
  exact hdensity.trans ((mul_le_mul_of_nonneg_left hprod hF).trans
    (canonical_upper_normalization_budget hr0 hr3 hC.le hlL hη.le))

theorem gamma6Base_label_finite_upper {i k N : ℕ} {δ Δ : ℝ}
    {V : Fin i → ℝ} (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1 / 2)
    (hbox : wuSourceBox k δ N i Δ V) {x : Gamma5ClassicalLabel}
    (hx : x ∈ gamma6BaseLabels N δ (convolutionWuWindows N Δ V)) :
    (sourceSieveCount N (gamma5ClassicalProduct x) (x.1 * N)
      (wuLocalCutoff N δ x.1 gamma5ClassicalS) : ℝ) ≤
      (logarithmicIntegral N / (Nat.totient (gamma5ClassicalProduct x) : ℝ)) *
        ordinaryRosserMainSum true N (gamma5ClassicalProduct x)
          (wuVariableRosserLevel N δ (gamma5ClassicalProduct x))
          (gamma5ClassicalCutoff N δ x) +
        ordinaryRosserRemainder true N (gamma5ClassicalProduct x)
          (wuVariableRosserLevel N δ (gamma5ClassicalProduct x))
          (gamma5ClassicalCutoff N δ x) := by
  have hg := gamma6Base_label_geometry hN hδ hδhi hbox hx
  obtain ⟨_hd, hp, hq, _hpN, _hqN, hzp, _⟩ :=
    (gamma6Base_mem_labels_iff hN hδ hδhi hbox x).mp hx
  have hsame := gamma5Classical_source_count_eq (N := N) (d := x.1) hp hq hzp
    (hzp.trans (by exact_mod_cast hg.prime_order.le))
  change sourceSieveCount N (gamma5ClassicalProduct x) (x.1 * N) _ =
    sourceSieveCount N (gamma5ClassicalProduct x) (gamma5ClassicalProduct x * N) _ at hsame
  rw [hsame]
  have hfloor : gamma5ClassicalLevel N δ x <
      (wuVariableRosserLevel N δ (gamma5ClassicalProduct x) : ℝ) := by
    exact_mod_cast Nat.lt_floor_add_one (gamma5ClassicalLevel N δ x)
  have hD : 1 < wuVariableRosserLevel N δ (gamma5ClassicalProduct x) := by
    exact_mod_cast hg.level_gt_one.trans hfloor
  apply (gamma5Classical_source_count_antitone N (gamma5ClassicalProduct x)
    (gamma5ClassicalProduct x * N) (min_le_left _ _)).trans
  exact ordinaryRosser_upper_finite hD (hg.cutoff_le_level.trans hfloor.le)

theorem gamma6Base_mask_upper (k : ℕ) (_hk : 1 ≤ k) {δ η ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) (hη : 0 < η) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ i : ℕ, ∀ Δ : ℝ, ∀ V : Fin i → ℝ, wuSourceBox k δ N i Δ V →
      ∀ X : Finset Gamma5ClassicalLabel,
        X ⊆ gamma6BaseLabels N δ (convolutionWuWindows N Δ V) →
        gamma5ClassicalCount N δ (convolutionWuWindows N Δ V) X ≤
          (1 + η) ^ 2 * gamma5ClassicalMainMass N δ (convolutionWuWindows N Δ V) X +
            ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  have hδhalf : δ < 1 / 2 := by linarith
  obtain ⟨TD, hden⟩ := gamma6Base_density_eventually k hδ hδhalf hη
  obtain ⟨TR, hrem⟩ := gamma6Base_remainder_relative k hδ hδhalf hε
  refine ⟨max 4 (max TD TR), le_max_left _ _, ?_⟩
  intro N hNT he i Δ V hbox X hX
  have hN4 : 4 ≤ N := (le_max_left _ _).trans hNT
  have hN : 2 ≤ N := by omega
  have hND : TD ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hNT)
  have hNR : TR ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hNT)
  have hli : 0 ≤ logarithmicIntegral N :=
    MathlibNt.SieveTheory.LiuWeight.liuLogarithmicIntegral_nonneg 0 (by norm_num)
      (by exact_mod_cast hN)
  have hpoint : ∀ x ∈ X,
      (sourceSieveCount N (gamma5ClassicalProduct x) (x.1 * N)
        (wuLocalCutoff N δ x.1 gamma5ClassicalS) : ℝ) ≤
        (logarithmicIntegral N / (Nat.totient (gamma5ClassicalProduct x) : ℝ)) *
          ((1 + η) ^ 2 * (4 * wuSingularSeries (gamma5ClassicalProduct x * N) /
            log (gamma5ClassicalLevel N δ x))) +
          ordinaryRosserRemainder true N (gamma5ClassicalProduct x)
            (wuVariableRosserLevel N δ (gamma5ClassicalProduct x))
            (gamma5ClassicalCutoff N δ x) := by
    intro x hx
    apply (gamma6Base_label_finite_upper hN hδ hδhalf hbox (hX hx)).trans
    exact add_le_add (mul_le_mul_of_nonneg_left
      (hden N hND he i Δ V hbox x (hX hx)) (div_nonneg hli (Nat.cast_nonneg _))) le_rfl
  have hfinite :
      gamma5ClassicalCount N δ (convolutionWuWindows N Δ V) X ≤
        (1 + η) ^ 2 * gamma5ClassicalMainMass N δ (convolutionWuWindows N Δ V) X +
          gamma5ClassicalRemainder N δ (convolutionWuWindows N Δ V) X
            (gamma5ClassicalCutoff N δ) := by
    unfold gamma5ClassicalCount gamma5ClassicalMainMass gamma5ClassicalRemainder
    rw [mul_sum, mul_sum, ← sum_add_distrib]
    apply sum_le_sum
    intro x hx
    have h := mul_le_mul_of_nonneg_left (hpoint x hx)
      (Nat.cast_nonneg (convolutionCoeff (convolutionWuWindows N Δ V) x.1))
    convert h using 1
    dsimp only [gamma5ClassicalLevel]
    ring
  exact hfinite.trans (add_le_add le_rfl
    ((le_abs_self _).trans (hrem N hNR i Δ V hbox X hX (gamma5ClassicalCutoff N δ))))

end Wu2008DoubleSieve
