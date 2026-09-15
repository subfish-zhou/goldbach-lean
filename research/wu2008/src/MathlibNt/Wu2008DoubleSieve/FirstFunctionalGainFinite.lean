import MathlibNt.Wu2008DoubleSieve.FirstFunctionalGainIntegrals
import MathlibNt.Wu2008DoubleSieve.OmegaSwitchedIntegral

/-!
# Actual finite-threshold admissibility for the first functional gain

Wu04, TeX 2260--2286 (Lemma 5.1). The starting inequality is the already
proved physical switched envelope, not an assumed comparison of gains.
Its coefficient in `2 * Phi` is `(1 + tau) * K / 4`, so the gain loses
`(1 + tau) * K * I / 8`. Every auxiliary parameter is fixed before the
threshold is chosen, and both actual improvements have the same threshold.
-/

namespace Wu2008DoubleSieve

open Filter Real
open scoped Topology Interval

noncomputable def firstFunctionalGainPsiSlack (δ ρ τ s t : ℝ) : ℝ :=
  wuUpperCoefficient s - wuUpperCoefficient t +
    (1 / 2) * (∫ u in (1 - 1 / s)..(1 - 1 / t),
      log (t * u - 1) / (u * (1 - u))) -
    (1 + τ) * ((1 + ρ) * (1 + ρ * exp (-eulerMascheroniConstant)) *
      (8 / (1 - 2 * δ))) / 8 * omega3XIntegralEnvelope s t

/-- The honest fixed-delta coefficient; no delta limit is implicit. -/
noncomputable def firstFunctionalGainPsi (δ s t : ℝ) : ℝ :=
  wuUpperCoefficient s - wuUpperCoefficient t +
    (1 / 2) * (∫ u in (1 - 1 / s)..(1 - 1 / t),
      log (t * u - 1) / (u * (1 - u))) -
    omega3XIntegralEnvelope s t / (1 - 2 * δ)

theorem firstFunctionalGainPsiSlack_zero (δ s t : ℝ) :
    firstFunctionalGainPsiSlack δ 0 0 s t = firstFunctionalGainPsi δ s t := by
  simp only [firstFunctionalGainPsiSlack, firstFunctionalGainPsi, add_zero,
    zero_mul, mul_one, one_mul]
  ring

/-- A genuine element of the actual finite-threshold admissible set,
uniform over all later even N and every legal source box. -/
theorem firstFunctionalGain_admissible_eventually (k : ℕ) (hk : 1 ≤ k)
    {δ ρ τ ε s t : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10)
    (hρ : 0 < ρ) (hτ : 0 < τ) (hε : 0 < ε)
    (hs : 2 ≤ s) (hs3 : s ≤ 3) (ht : 3 ≤ t) (ht5 : t ≤ 5)
    (hratio : 2 ≤ t - t / s) :
    ∀ᶠ N0 : ℕ in atTop,
      firstFunctionalGainPsiSlack δ ρ τ s t + wuImprovementAt true k δ t N0 +
        (1 / 2) * (∫ u in (1 - 1 / s)..(1 - 1 / t),
          wuImprovementAt false (k + 1) δ (t * u) N0 / (u * (1 - u))) - ε ∈
        wuAdmissibleImprovements true k δ s N0 := by
  have hδhalf : δ < 1 / 2 := by linarith
  obtain ⟨T, _, hT⟩ :=
    wu04_first_weighted_switched_envelope k hk hδ hδhi hρ hτ (mul_pos two_pos hε)
  filter_upwards [eventually_ge_atTop T,
    firstFunctionalGain_integral_eventually_split (k + 1) (by omega)
      hδ hδhalf hs hs3 ht ht5 hratio] with N0 hN0 hsplit
  intro N hN _hN4 he i Δ V hb
  have hphysical := hT N0 hN0 N hN he i Δ V hb s t hs hs3 ht ht5 hratio
  dsimp only at hphysical
  rw [hsplit] at hphysical
  change wuBoxPhi N δ (convolutionWuWindows N Δ V) s ≤
    (wuUpperCoefficient s - _) *
      boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V)
  unfold firstFunctionalGainPsiSlack
  nlinarith

theorem wuImprovementAt_firstFunctionalGain_eventually (k : ℕ) (hk : 1 ≤ k)
    {δ ρ τ ε s t : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10)
    (hρ : 0 < ρ) (hτ : 0 < τ) (hε : 0 < ε)
    (hs : 2 ≤ s) (hs3 : s ≤ 3) (ht : 3 ≤ t) (ht5 : t ≤ 5)
    (hratio : 2 ≤ t - t / s) :
    ∀ᶠ N0 : ℕ in atTop,
      firstFunctionalGainPsiSlack δ ρ τ s t + wuImprovementAt true k δ t N0 +
        (1 / 2) * (∫ u in (1 - 1 / s)..(1 - 1 / t),
          wuImprovementAt false (k + 1) δ (t * u) N0 / (u * (1 - u))) - ε ≤
        wuImprovementAt true k δ s N0 := by
  filter_upwards [firstFunctionalGain_admissible_eventually k hk hδ hδhi hρ hτ hε
    hs hs3 ht ht5 hratio] with N0 hmem
  have hsub : wuAdmissibleImprovements true k δ s N0 ⊆ wuEventualImprovements true k δ s :=
    fun _ hh => ⟨N0, hh⟩
  exact le_csSup ((wuEventualImprovements_bddAbove true k hδ (by linarith)
    (by linarith) (by linarith)).mono hsub) hmem

end Wu2008DoubleSieve
