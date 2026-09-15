import MathlibNt.Wu2008DoubleSieve.Gamma5ClassicalGeometry

/-!
# Gamma5: arbitrary-window BV paid against the old Theta

There is one AP majorant for the whole selected mask. The exponent
`A = 5*k+6` is fixed before any threshold; the old box has lower mass
of order `N / log(N)^(5*k+2)`.
-/

namespace Wu2008DoubleSieve

open Finset Real Filter
open scoped Classical Topology

noncomputable def gamma5ClassicalLargePrimes (N : ℕ) (α : ℝ) : Finset ℕ :=
  (range (N + 1)).filter (fun p => p.Prime ∧ p.Coprime N ∧ (N : ℝ) ^ α ≤ (p : ℝ))

theorem gamma5Classical_windows_eventually (k : ℕ) {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) :
    ∀ᶠ N : ℕ in atTop, ∀ i : ℕ, ∀ Δ : ℝ, ∀ V : Fin i → ℝ,
      wuSourceBox k δ N i Δ V →
      (∀ j p, p ∈ convolutionWuWindows N Δ V j →
        p.Prime ∧ p.Coprime N ∧ (N : ℝ) ^ (gamma5ClassicalAlpha k δ) ≤ (p : ℝ)) ∧
      gamma5ClassicalLabels N δ (convolutionWuWindows N Δ V) ⊆
        boxConvolutionSupport (convolutionWuWindows N Δ V) ×ˢ
          (gamma5ClassicalLargePrimes N (gamma5ClassicalAlpha k δ) ×ˢ
            gamma5ClassicalLargePrimes N (gamma5ClassicalAlpha k δ)) := by
  filter_upwards [convolutionWuWindows_eventually_lower_cutoff (pow_pos hδ (k + 1)),
    eventually_ge_atTop (2 : ℕ)] with N hlow hN
  intro i Δ V hbox
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hβ := wuLocalExponent_pos k hδ hδhi
  have hβle : wuLocalExponent k δ ≤ δ ^ (k + 1) := min_le_left _ _
  have hαle : gamma5ClassicalAlpha k δ ≤ δ ^ (k + 1) / 2 := by
    norm_num [gamma5ClassicalAlpha, gamma5ClassicalS]
    linarith
  constructor
  · intro j p hp
    obtain ⟨hp, hc, hlo, _⟩ := mem_convolutionWuWindows.mp hp
    exact ⟨hp, hc, (rpow_le_rpow_of_exponent_le hN1 hαle).trans
      ((hlow Δ hbox.2.1 hbox.2.2.1 (V j) (hbox.2.2.2.2.1 j)).trans hlo)⟩
  · intro x hx
    have hg := gamma5Classical_label_geometry hN hδ hδhi hbox hx
    obtain ⟨ha, hp, hq, hpN, hqN, _hz, hpq, _hu⟩ := mem_filter.mp hx
    obtain ⟨hd, hpqrange⟩ := mem_product.mp ha
    obtain ⟨hprange, hqrange⟩ := mem_product.mp hpqrange
    exact mem_product.mpr ⟨hd, mem_product.mpr
      ⟨mem_filter.mpr ⟨hprange, hp, hpN, hg.prime_lower⟩,
        mem_filter.mpr ⟨hqrange, hq, hqN,
          hg.prime_lower.trans (by exact_mod_cast hpq.le)⟩⟩⟩

/-- Actual BV, uniformly over masks and full-label cutoffs. -/
theorem gamma5Classical_masked_bombieri_vinogradov (k : ℕ) {δ A : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∃ T : ℕ, ∀ N : ℕ, T ≤ N →
      ∀ i : ℕ, ∀ Δ : ℝ, ∀ V : Fin i → ℝ, wuSourceBox k δ N i Δ V →
      ∀ X : Finset Gamma5ClassicalLabel,
        X ⊆ gamma5ClassicalLabels N δ (convolutionWuWindows N Δ V) →
      ∀ z : Gamma5ClassicalLabel → ℝ,
        |gamma5ClassicalRemainder N δ (convolutionWuWindows N Δ V) X z| ≤
          C * (N : ℝ) / log N ^ A := by
  have hα := (gamma5Classical_exponents_pos k hδ hδhi).1
  obtain ⟨C, hC, T, hBV⟩ := convolution_bombieri_vinogradov (k + 2) hα hδ hA
  refine ⟨C, hC, ?_⟩
  apply eventually_atTop.mp
  filter_upwards [eventually_ge_atTop T, gamma5Classical_windows_eventually k hδ hδhi]
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

/-- The full signed AP remainder is paid once against the original box mass. -/
theorem gamma5Classical_remainder_relative (k : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hε : 0 < ε) :
    ∃ T : ℕ, ∀ N : ℕ, T ≤ N →
      ∀ i : ℕ, ∀ Δ : ℝ, ∀ V : Fin i → ℝ, wuSourceBox k δ N i Δ V →
      ∀ X : Finset Gamma5ClassicalLabel,
        X ⊆ gamma5ClassicalLabels N δ (convolutionWuWindows N Δ V) →
      ∀ z : Gamma5ClassicalLabel → ℝ,
        |gamma5ClassicalRemainder N δ (convolutionWuWindows N Δ V) X z| ≤
          ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  obtain ⟨C, hC, T1, hBV⟩ := gamma5Classical_masked_bombieri_vinogradov k hδ hδhi
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

end Wu2008DoubleSieve
