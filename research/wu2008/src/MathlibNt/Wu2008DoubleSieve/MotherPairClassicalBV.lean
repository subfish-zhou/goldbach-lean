import MathlibNt.Wu2008DoubleSieve.MotherPairClassicalGeometry
import MathlibNt.Wu2008DoubleSieve.Gamma5ClassicalBV
/-! One arbitrary-window BV call at depth k+2, with the original full
convolution coefficients; no cutoff or label enters the threshold. -/

namespace Wu2008DoubleSieve.MotherPair
open Finset Real Filter
open scoped Classical Topology
theorem classical_windows_eventually {S U : ℝ} (hcap : CapAdmissible S U) (k : ℕ) {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) :
    ∀ᶠ N : ℕ in atTop, ∀ i : ℕ, ∀ Δ : ℝ, ∀ V : Fin i → ℝ,
      wuSourceBox k δ N i Δ V →
      (∀ j p, p ∈ convolutionWuWindows N Δ V j →
        p.Prime ∧ p.Coprime N ∧ (N : ℝ) ^ (classicalAlpha S k δ) ≤ (p : ℝ)) ∧
      capLabels S U N δ (convolutionWuWindows N Δ V) ⊆
        boxConvolutionSupport (convolutionWuWindows N Δ V) ×ˢ
          (gamma5ClassicalLargePrimes N (classicalAlpha S k δ) ×ˢ
            gamma5ClassicalLargePrimes N (classicalAlpha S k δ)) := by
  filter_upwards [convolutionWuWindows_eventually_lower_cutoff (pow_pos hδ (k + 1)),
    eventually_ge_atTop (2 : ℕ)] with N hlow hN
  intro i Δ V hbox
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hβ := wuLocalExponent_pos k hδ hδhi
  have hβle : wuLocalExponent k δ ≤ δ ^ (k + 1) := min_le_left _ _
  have hαle : classicalAlpha S k δ ≤ δ ^ (k + 1) / 2 := by
    have hS : 1 ≤ S := by linarith [hcap.three_le_S]
    calc
      classicalAlpha S k δ ≤ wuLocalExponent k δ / 2 := by
        unfold classicalAlpha
        exact div_le_div_of_nonneg_left hβ.le (by norm_num) (by linarith)
      _ ≤ δ ^ (k + 1) / 2 := div_le_div_of_nonneg_right hβle (by norm_num)
  constructor
  · intro j p hp
    obtain ⟨hp, hc, hlo, _⟩ := mem_convolutionWuWindows.mp hp
    exact ⟨hp, hc, (rpow_le_rpow_of_exponent_le hN1 hαle).trans
      ((hlow Δ hbox.2.1 hbox.2.2.1 (V j) (hbox.2.2.2.2.1 j)).trans hlo)⟩
  · intro x hx
    have hg := classical_label_geometry hcap hN hδ hδhi hbox hx
    obtain ⟨ha, hp, hq, hpN, hqN, _hz, hpq, _hu⟩ := mem_filter.mp hx
    obtain ⟨hd, hpqrange⟩ := mem_product.mp ha
    obtain ⟨hprange, hqrange⟩ := mem_product.mp hpqrange
    exact mem_product.mpr ⟨hd, mem_product.mpr
      ⟨mem_filter.mpr ⟨hprange, hp, hpN, hg.prime_lower⟩,
        mem_filter.mpr ⟨hqrange, hq, hqN,
          hg.prime_lower.trans (by exact_mod_cast hpq.le)⟩⟩⟩

/-- Actual BV, uniformly over masks and full-label cutoffs. -/
theorem classical_masked_bombieri_vinogradov {S U : ℝ} (hcap : CapAdmissible S U) (k : ℕ) {δ A : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∃ T : ℕ, ∀ N : ℕ, T ≤ N →
      ∀ i : ℕ, ∀ Δ : ℝ, ∀ V : Fin i → ℝ, wuSourceBox k δ N i Δ V →
      ∀ X : Finset Gamma5ClassicalLabel,
        X ⊆ capLabels S U N δ (convolutionWuWindows N Δ V) →
      ∀ z : Gamma5ClassicalLabel → ℝ,
        |gamma5ClassicalRemainder N δ (convolutionWuWindows N Δ V) X z| ≤
          C * (N : ℝ) / log N ^ A := by
  have hα := (classical_exponents_pos hcap k hδ hδhi).1
  obtain ⟨C, hC, T, hBV⟩ := convolution_bombieri_vinogradov (k + 2) hα hδ hA
  refine ⟨C, hC, ?_⟩
  apply eventually_atTop.mp
  filter_upwards [eventually_ge_atTop T, classical_windows_eventually hcap k hδ hδhi]
    with N hT hw
  intro i Δ V hbox X hX z
  obtain ⟨hW, hlabels⟩ := hw i Δ V hbox
  let P := gamma5ClassicalLargePrimes N (classicalAlpha S k δ)
  have hP : ∀ p ∈ P, p.Prime ∧ p.Coprime N ∧
      (N : ℝ) ^ classicalAlpha S k δ ≤ (p : ℝ) :=
    fun p hp => (mem_filter.mp hp).2
  apply (gamma5Classical_masked_remainder_le N δ _ P X (hX.trans hlabels) z).trans
  apply hBV N hT (i + 1 + 1) (by have := hbox.1; omega)
  intro j
  exact Fin.cases hP (fun j => Fin.cases hP hW j) j

/-- The full signed AP remainder is paid once against the original box mass. -/
theorem classical_remainder_relative {S U : ℝ} (hcap : CapAdmissible S U) (k : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hε : 0 < ε) :
    ∃ T : ℕ, ∀ N : ℕ, T ≤ N →
      ∀ i : ℕ, ∀ Δ : ℝ, ∀ V : Fin i → ℝ, wuSourceBox k δ N i Δ V →
      ∀ X : Finset Gamma5ClassicalLabel,
        X ⊆ capLabels S U N δ (convolutionWuWindows N Δ V) →
      ∀ z : Gamma5ClassicalLabel → ℝ,
        |gamma5ClassicalRemainder N δ (convolutionWuWindows N Δ V) X z| ≤
          ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  obtain ⟨C, hC, T1, hBV⟩ := classical_masked_bombieri_vinogradov hcap k hδ hδhi
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

end Wu2008DoubleSieve.MotherPair
