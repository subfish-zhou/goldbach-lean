import MathlibNt.Wu2008DoubleSieve.MotherPairClassicalBV
/-! Canonical bounded local density and a single signed-remainder payment
produce the variable-cap, arbitrary-mask bound with the original mass. -/

namespace Wu2008DoubleSieve.MotherPair
open Finset Real Filter
open scoped Classical Topology
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne

/-- The lowered-cutoff density has the classical normalization at the
unchanged local level. The threshold precedes every box and label. -/
theorem classical_density_eventually {S U : ℝ} (hcap : CapAdmissible S U) (k : ℕ) {δ η : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hη : 0 < η) :
    ∃ T : ℕ, ∀ N : ℕ, T ≤ N → Even N →
      ∀ i : ℕ, ∀ Δ : ℝ, ∀ V : Fin i → ℝ, wuSourceBox k δ N i Δ V →
      ∀ x ∈ capLabels S U N δ (convolutionWuWindows N Δ V),
        ordinaryRosserMainSum true N (gamma5ClassicalProduct x)
          (wuVariableRosserLevel N δ (gamma5ClassicalProduct x))
          (classicalCutoff S N δ x) ≤
        (1 + η) ^ 2 * (4 * wuSingularSeries (gamma5ClassicalProduct x * N) /
          log (gamma5ClassicalLevel N δ x)) := by
  let ρ : ℝ := 2 * exp eulerMascheroniConstant * η / 3
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hζ := (classical_exponents_pos hcap k hδ hδhi).2
  obtain ⟨ZD, hden⟩ := ordinaryRosser_upper_density_canonical_bounded_local hρ
  obtain ⟨ZE, hEuler⟩ := eventually_atTop.mp
    (eventually_localSieveProduct_relative (2 / classicalZeta S U k δ) η
      (by positivity) hη)
  have hlarge : ∀ᶠ N : ℕ in atTop,
      max 2 (max ZD ZE) ≤ (N : ℝ) ^ classicalZeta S U k δ :=
    ((tendsto_rpow_atTop hζ).comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop _)
  apply eventually_atTop.mp
  filter_upwards [hlarge, eventually_ge_atTop (2 : ℕ)] with N hlargeN hN
  intro he i Δ V hbox x hx
  have hg := classical_label_geometry hcap hN hδ hδhi hbox hx
  let L := gamma5ClassicalLevel N δ x
  let z := classicalCutoff S N δ x
  let r := log L / log z
  have hlL : 0 < log L := log_pos hg.level_gt_one
  have hlz : 0 < log z := log_pos hg.cutoff_gt_one
  have hr0 : 0 < r := div_pos hlL hlz
  have hr3 : r ≤ 3 := hg.ratio_upper
  have hzlarge : max 2 (max ZD ZE) ≤ z := hlargeN.trans hg.cutoff_lower
  have hz2 : 2 ≤ z := (le_max_left _ _).trans hzlarge
  have hzD : ZD ≤ z := (le_max_left _ _).trans ((le_max_right _ _).trans hzlarge)
  have hzE : ZE ≤ z := (le_max_right _ _).trans ((le_max_right _ _).trans hzlarge)
  have hdensity := hden N (gamma5ClassicalProduct x) he z L r hzD hz2
    (by linarith [hg.level_gt_one]) rfl
    (by have := hg.ratio_lower; change 2 ≤ r at this; linarith) (by linarith)
  have hMN : 0 < gamma5ClassicalProduct x * N :=
    Nat.mul_pos hg.product_pos (by omega)
  have hC : 0 < wuSingularSeries (gamma5ClassicalProduct x * N) :=
    wuSingularSeries_pos _ hMN
  have hnorm := hEuler z hzE (gamma5ClassicalProduct x * N) hMN
    (he.mul_left _) (classical_polynomial_envelope hζ hg)
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

/-- The literal old count is bounded by the actual finite Rosser main and
its signed remainder, not by an assumed AP or density estimate. -/
theorem classical_label_finite_upper {S U : ℝ} (hcap : CapAdmissible S U) {i k N : ℕ} {δ Δ : ℝ}
    {V : Fin i → ℝ} (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1 / 2)
    (hbox : wuSourceBox k δ N i Δ V) {x : Gamma5ClassicalLabel}
    (hx : x ∈ capLabels S U N δ (convolutionWuWindows N Δ V)) :
    (sourceSieveCount N (gamma5ClassicalProduct x) (x.1 * N)
      (wuLocalCutoff N δ x.1 S) : ℝ) ≤
      (logarithmicIntegral N / (Nat.totient (gamma5ClassicalProduct x) : ℝ)) *
        ordinaryRosserMainSum true N (gamma5ClassicalProduct x)
          (wuVariableRosserLevel N δ (gamma5ClassicalProduct x))
          (classicalCutoff S N δ x) +
        ordinaryRosserRemainder true N (gamma5ClassicalProduct x)
          (wuVariableRosserLevel N δ (gamma5ClassicalProduct x))
          (classicalCutoff S N δ x) := by
  have hg := classical_label_geometry hcap hN hδ hδhi hbox hx
  obtain ⟨_ha, hp, hq, _hpN, _hqN, hzp, hpq, _hqu⟩ := mem_filter.mp hx
  have hsame := gamma5Classical_source_count_eq (N := N) (d := x.1) hp hq hzp
    (hzp.trans (by exact_mod_cast hpq.le))
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

/-- The real unconditional classical upper count for every actual mask.
All constants precede the even integer, the source box, and the mask. -/
theorem classical_mask_upper {S U : ℝ} (hcap : CapAdmissible S U) (k : ℕ) (_hk : 1 ≤ k) {δ η ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) (hη : 0 < η) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ i : ℕ, ∀ Δ : ℝ, ∀ V : Fin i → ℝ, wuSourceBox k δ N i Δ V →
      ∀ X : Finset Gamma5ClassicalLabel,
        X ⊆ capLabels S U N δ (convolutionWuWindows N Δ V) →
        fixedCount S N δ (convolutionWuWindows N Δ V) X ≤
          (1 + η) ^ 2 * gamma5ClassicalMainMass N δ (convolutionWuWindows N Δ V) X +
            ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  have hδhalf : δ < 1 / 2 := by linarith
  obtain ⟨TD, hden⟩ := classical_density_eventually hcap k hδ hδhalf hη
  obtain ⟨TR, hrem⟩ := classical_remainder_relative hcap k hδ hδhalf hε
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
        (wuLocalCutoff N δ x.1 S) : ℝ) ≤
        (logarithmicIntegral N / (Nat.totient (gamma5ClassicalProduct x) : ℝ)) *
          ((1 + η) ^ 2 * (4 * wuSingularSeries (gamma5ClassicalProduct x * N) /
            log (gamma5ClassicalLevel N δ x))) +
          ordinaryRosserRemainder true N (gamma5ClassicalProduct x)
            (wuVariableRosserLevel N δ (gamma5ClassicalProduct x))
            (classicalCutoff S N δ x) := by
    intro x hx
    apply (classical_label_finite_upper hcap hN hδ hδhalf hbox (hX hx)).trans
    exact add_le_add (mul_le_mul_of_nonneg_left
      (hden N hND he i Δ V hbox x (hX hx)) (div_nonneg hli (Nat.cast_nonneg _))) le_rfl
  have hfinite :
      fixedCount S N δ (convolutionWuWindows N Δ V) X ≤
        (1 + η) ^ 2 * gamma5ClassicalMainMass N δ (convolutionWuWindows N Δ V) X +
          gamma5ClassicalRemainder N δ (convolutionWuWindows N Δ V) X
            (classicalCutoff S N δ) := by
    unfold fixedCount gamma5ClassicalMainMass gamma5ClassicalRemainder
    rw [mul_sum, mul_sum, ← sum_add_distrib]
    apply sum_le_sum
    intro x hx
    have h := mul_le_mul_of_nonneg_left (hpoint x hx)
      (Nat.cast_nonneg (convolutionCoeff (convolutionWuWindows N Δ V) x.1))
    convert h using 1
    dsimp only [gamma5ClassicalLevel]
    ring
  exact hfinite.trans (add_le_add le_rfl
    ((le_abs_self _).trans (hrem N hNR i Δ V hbox X hX (classicalCutoff S N δ))))

/-- Explicit full-mask consumer of the unconditional count producer. -/
theorem classical_full_upper {S U : ℝ} (hcap : CapAdmissible S U) (k : ℕ) (hk : 1 ≤ k) {δ η ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) (hη : 0 < η) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ i : ℕ, ∀ Δ : ℝ, ∀ V : Fin i → ℝ, wuSourceBox k δ N i Δ V →
        fixedCount S N δ (convolutionWuWindows N Δ V)
            (capLabels S U N δ (convolutionWuWindows N Δ V)) ≤
          (1 + η) ^ 2 * gamma5ClassicalMainMass N δ (convolutionWuWindows N Δ V)
            (capLabels S U N δ (convolutionWuWindows N Δ V)) +
          ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  obtain ⟨T, hT, h⟩ := classical_mask_upper hcap k hk hδ hδhi hη hε
  exact ⟨T, hT, fun N hN he i Δ V hb => h N hN he i Δ V hb _ (Subset.refl _)⟩

end Wu2008DoubleSieve.MotherPair
