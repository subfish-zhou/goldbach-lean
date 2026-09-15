import MathlibNt.Wu2008DoubleSieve.PrimeCoefficientIntegral

/-!
# Sharp uniform bounds for the actual effective coefficients

The threshold is chosen before the source parameter. Actual admissibility,
not a norm estimate for a surrogate, gives `0 ≤ A-H ≤ 11` and
`-1 ≤ a+h ≤ 10`.
-/

namespace Wu2008DoubleSieve

open Set Filter Real
open scoped Topology
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne

theorem wuEffectiveCoefficient_uniform_signed_bounds (upper : Bool)
    (k : ℕ) (hk : 1 ≤ k) {δ : ℝ} (hδ : 0 < δ) (hδhi : δ < 1 / 2) :
    ∀ᶠ N0 : ℕ in atTop, ∀ t ∈ Icc (1 : ℝ) 10,
      if upper then
        0 ≤ wuEffectiveCoefficient upper k δ N0 t ∧
          wuEffectiveCoefficient upper k δ N0 t ≤ 11
      else
        -1 ≤ wuEffectiveCoefficient upper k δ N0 t ∧
          wuEffectiveCoefficient upper k δ N0 t ≤ 10 := by
  filter_upwards [wuImprovementAt_uniform_eventually_attained upper k hk hδ hδhi]
    with N0 hN0
  intro t ht
  have ht0 : 0 < t := by linarith [ht.1]
  have hmem : wuImprovementAt upper k δ t N0 ∈ wuEventualImprovements upper k δ t :=
    ⟨N0, (hN0 t ht.1 ht.2).2.1⟩
  have hlow := (hN0 t ht.1 ht.2).2.2
  have ha : 0 ≤ wuLowerCoefficient t :=
    div_nonneg (mul_nonneg ht0.le (jr1965f_nonneg ht0)) (by positivity)
  have hA : wuUpperCoefficient t ≤ 10 := by
    unfold wuUpperCoefficient
    apply (div_le_iff₀ (by positivity : 0 < 2 * exp eulerMascheroniConstant)).2
    have hf := mul_le_mul_of_nonneg_left (jr1965F_le_delayConstant ht.1) ht0.le
    unfold jr1965DelayConstant at hf
    nlinarith [exp_pos eulerMascheroniConstant, ht.2]
  cases upper
  · have hup := wuEventualImprovements_lower_le hδ hδhi ht.1 ht.2 hmem
    change -1 ≤ wuLowerCoefficient t + wuImprovementAt false k δ t N0 ∧
      wuLowerCoefficient t + wuImprovementAt false k δ t N0 ≤ 10
    constructor <;> linarith
  · have hup := wuEventualImprovements_upper_le hδhi hmem
    change 0 ≤ wuUpperCoefficient t - wuImprovementAt true k δ t N0 ∧
      wuUpperCoefficient t - wuImprovementAt true k δ t N0 ≤ 11
    constructor <;> linarith

/-- The uniform absolute bound requested by the normalized prime-window
consumer. The fixed-delta threshold precedes both `N0` and `t`. -/
theorem wuEffectiveCoefficient_uniform_abs_le_eleven (upper : Bool)
    (k : ℕ) (hk : 1 ≤ k) {δ : ℝ} (hδ : 0 < δ) (hδhi : δ < 1 / 2) :
    ∀ᶠ N0 : ℕ in atTop, ∀ t ∈ Icc (1 : ℝ) 10,
      |wuEffectiveCoefficient upper k δ N0 t| ≤ 11 := by
  filter_upwards [wuEffectiveCoefficient_uniform_signed_bounds upper k hk hδ hδhi]
    with N0 hN0
  intro t ht
  have h := hN0 t ht
  apply abs_le.mpr
  cases upper <;> simp only [Bool.false_eq_true, if_false, if_true] at h <;>
    constructor <;> linarith

end Wu2008DoubleSieve
