import MathlibNt.Wu2008DoubleSieve.FirstFunctionalGainFinite

/-!
# The first actual functional-gain inequality at fixed delta

Wu04, TeX 2260--2286. First send the common threshold to infinity at
fixed depth and fixed positive auxiliary slacks. Remove the additive
epsilon and then the two density slacks, and only afterwards take the
depth limit. The surviving switched penalty is `I / (1 - 2 * delta)`.
-/

namespace Wu2008DoubleSieve

open Filter Real
open scoped Topology Interval

/-- The inner threshold limit, with the additive error removed but the
two fixed multiplicative slacks still present. -/
theorem wuImprovementAtInfinity_firstFunctionalGain_slack (k : ℕ) (hk : 1 ≤ k)
    {δ ρ τ s t : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10)
    (hρ : 0 < ρ) (hτ : 0 < τ)
    (hs : 2 ≤ s) (hs3 : s ≤ 3) (ht : 3 ≤ t) (ht5 : t ≤ 5)
    (hratio : 2 ≤ t - t / s) :
    firstFunctionalGainPsiSlack δ ρ τ s t + wuImprovementAtInfinity true k δ t +
      (1 / 2) * (∫ u in (1 - 1 / s)..(1 - 1 / t),
        wuImprovementAtInfinity false (k + 1) δ (t * u) / (u * (1 - u))) ≤
      wuImprovementAtInfinity true k δ s := by
  have hδhalf : δ < 1 / 2 := by linarith
  have hsconv := wuImprovementAt_tendsto true k hk hδ hδhalf
    (show 1 ≤ s by linarith) (show s ≤ 10 by linarith)
  have htconv := wuImprovementAt_tendsto true k hk hδ hδhalf
    (show 1 ≤ t by linarith) (show t ≤ 10 by linarith)
  have hiconv := firstFunctionalGain_integral_threshold_limit (k + 1) (by omega)
    hδ hδhalf hs (hs3.trans ht) ht ht5
  apply le_of_forall_pos_le_add
  intro ε hε
  have h := le_of_tendsto_of_tendsto
    (((htconv.const_add (firstFunctionalGainPsiSlack δ ρ τ s t)).add
      (hiconv.const_mul (1 / 2))).sub_const ε) hsconv
    (wuImprovementAt_firstFunctionalGain_eventually k hk hδ hδhi hρ hτ hε
      hs hs3 ht ht5 hratio)
  linarith

/-- Taking equal positive slacks to zero suffices: each pair has already
had its own threshold limit, so no threshold uniformity is asserted. -/
theorem firstFunctionalGainPsiSlack_tendsto (δ s t : ℝ) :
    Tendsto (fun r : ℝ => firstFunctionalGainPsiSlack δ r r s t)
      (𝓝[>] (0 : ℝ)) (𝓝 (firstFunctionalGainPsi δ s t)) := by
  have hc : Continuous (fun r : ℝ => firstFunctionalGainPsiSlack δ r r s t) := by
    unfold firstFunctionalGainPsiSlack
    fun_prop
  have h : Tendsto (fun r : ℝ => firstFunctionalGainPsiSlack δ r r s t)
      (𝓝[>] (0 : ℝ)) (𝓝 (firstFunctionalGainPsiSlack δ 0 0 s t)) :=
    hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  simpa only [firstFunctionalGainPsiSlack_zero] using h

theorem wuImprovementAtInfinity_firstFunctionalGain (k : ℕ) (hk : 1 ≤ k)
    {δ s t : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10)
    (hs : 2 ≤ s) (hs3 : s ≤ 3) (ht : 3 ≤ t) (ht5 : t ≤ 5)
    (hratio : 2 ≤ t - t / s) :
    firstFunctionalGainPsi δ s t + wuImprovementAtInfinity true k δ t +
      (1 / 2) * (∫ u in (1 - 1 / s)..(1 - 1 / t),
        wuImprovementAtInfinity false (k + 1) δ (t * u) / (u * (1 - u))) ≤
      wuImprovementAtInfinity true k δ s := by
  apply le_of_tendsto
    (((firstFunctionalGainPsiSlack_tendsto δ s t).add_const
      (wuImprovementAtInfinity true k δ t)).add_const _)
  exact eventually_nhdsWithin_of_forall fun r hr =>
    wuImprovementAtInfinity_firstFunctionalGain_slack k hk hδ hδhi hr hr
      hs hs3 ht ht5 hratio

/-- The actual final-depth first functional inequality. It has no analytic
premise beyond the displayed source parameter restrictions. -/
theorem wuImprovementLimit_firstFunctionalGain
    {δ s t : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10)
    (hs : 2 ≤ s) (hs3 : s ≤ 3) (ht : 3 ≤ t) (ht5 : t ≤ 5)
    (hratio : 2 ≤ t - t / s) :
    firstFunctionalGainPsi δ s t + wuImprovementLimit true δ t +
      (1 / 2) * (∫ u in (1 - 1 / s)..(1 - 1 / t),
        wuImprovementLimit false δ (t * u) / (u * (1 - u))) ≤
      wuImprovementLimit true δ s := by
  have hδhalf : δ < 1 / 2 := by linarith
  have hsconv := wuImprovementAtInfinity_tendsto true hδ hδhalf
    (show 1 ≤ s by linarith) (show s ≤ 10 by linarith)
  have htconv := wuImprovementAtInfinity_tendsto true hδ hδhalf
    (show 1 ≤ t by linarith) (show t ≤ 10 by linarith)
  have hiconv := (firstFunctionalGain_integral_depth_limit hδ hδhalf
    hs (hs3.trans ht) ht ht5).comp (tendsto_add_atTop_nat 1)
  exact le_of_tendsto_of_tendsto
    ((htconv.const_add (firstFunctionalGainPsi δ s t)).add (hiconv.const_mul (1 / 2)))
    hsconv (Eventually.of_forall fun k =>
      wuImprovementAtInfinity_firstFunctionalGain (k + 1) (by omega) hδ hδhi
        hs hs3 ht ht5 hratio)

end Wu2008DoubleSieve
