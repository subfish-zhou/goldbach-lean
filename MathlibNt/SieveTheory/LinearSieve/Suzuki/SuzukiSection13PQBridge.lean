import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiSection13HatLayersKappaOne

open scoped Classical BigOperators Interval
open Set Filter Topology MeasureTheory intervalIntegral

namespace MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne

set_option maxHeartbeats 800000

/-- Suzuki (13.8): the antisymmetric combination of the two hat solutions. -/
def section13Phat (H : Section13HatLayers) (s : ℝ) : ℝ :=
  H.T .plus s - H.T .minus s

/-- Suzuki (13.8): the symmetric, positive combination of the two hat solutions. -/
def section13Qhat (H : Section13HatLayers) (s : ℝ) : ℝ :=
  H.T .plus s + H.T .minus s

/-- The unweighted form of (T3). -/
theorem section13Hat_hasDerivAt
    {H : Section13HatLayers} (hH : Section13HatContract H 2)
    (sign : ErrorSign) {s : ℝ} (hs : 2 + sign.epsilon < s) :
    HasDerivAt (H.T sign)
      (-(2 * H.T sign s + H.T sign.opposite (s - 1)) / s) s := by
  have hs0 : s ≠ 0 := by
    cases sign <;> simp [ErrorSign.epsilon] at hs <;> linarith
  have hw := hH.dde sign s hs
  have hsquare : HasDerivAt (fun x : ℝ => x ^ 2) (2 * s) s := by
    simpa using (hasDerivAt_pow 2 s)
  have hquot := hw.div hsquare (pow_ne_zero 2 hs0)
  have hfun : H.T sign =ᶠ[𝓝 s] weightedHat H sign / (fun x : ℝ => x ^ 2) := by
    filter_upwards [eventually_ne_nhds hs0] with x hx
    simp [weightedHat, hx]
  have hT := hquot.congr_of_eventuallyEq hfun
  apply hT.congr_deriv
  change
    ((-s * H.T sign.opposite (s - 1)) * s ^ 2 -
      (s ^ 2 * H.T sign s) * (2 * s)) / (s ^ 2) ^ 2 =
    -(2 * H.T sign s + H.T sign.opposite (s - 1)) / s
  field_simp [hs0]
  ring

/-- The symmetric combination satisfies `DDE(2,1,2)`. -/
theorem section13Qhat_dde
    {H : Section13HatLayers} (hH : Section13HatContract H 2)
    {s : ℝ} (hs : 3 < s) :
    HasDerivAt (section13Qhat H)
      (-(2 * section13Qhat H s + section13Qhat H (s - 1)) / s) s := by
  have hp := section13Hat_hasDerivAt hH .plus (by
    show 2 + ErrorSign.epsilon .plus < s
    norm_num [ErrorSign.epsilon]
    exact hs)
  have hm := section13Hat_hasDerivAt hH .minus (by simp [ErrorSign.epsilon]; linarith)
  change HasDerivAt (fun x => H.T .plus x + H.T .minus x) _ s
  apply (hp.add hm).congr_deriv
  dsimp [section13Qhat]
  ring

/-- The antisymmetric combination satisfies the companion signed DDE. -/
theorem section13Phat_dde
    {H : Section13HatLayers} (hH : Section13HatContract H 2)
    {s : ℝ} (hs : 3 < s) :
    HasDerivAt (section13Phat H)
      (-(2 * section13Phat H s - section13Phat H (s - 1)) / s) s := by
  have hp := section13Hat_hasDerivAt hH .plus (by
    show 2 + ErrorSign.epsilon .plus < s
    norm_num [ErrorSign.epsilon]
    exact hs)
  have hm := section13Hat_hasDerivAt hH .minus (by simp [ErrorSign.epsilon]; linarith)
  change HasDerivAt (fun x => H.T .plus x - H.T .minus x) _ s
  apply (hp.sub hm).congr_deriv
  dsimp [section13Phat]
  ring

/-- Continuity of `Q̂` on its natural positive domain. -/
theorem section13Qhat_continuousOn
    {H : Section13HatLayers} (hH : Section13HatContract H 2) :
    ContinuousOn (section13Qhat H) (Ioi 0) := by
  change ContinuousOn (fun s => H.T .plus s + H.T .minus s) (Ioi 0)
  exact (hH.continuous .plus).add (hH.continuous .minus)

/-- Strict positivity of `Q̂`. -/
theorem section13Qhat_pos
    {H : Section13HatLayers} (hH : Section13HatContract H 2)
    {s : ℝ} (hs : 0 < s) : 0 < section13Qhat H s := by
  exact add_pos (hH.positive .plus s hs) (hH.positive .minus s hs)


/-- The exact order-theoretic last step in the Lemma 10.17 bridge.  The hard
input is only a strict contraction of `P̂` relative to `Q̂`; no final
`T̂± ≍ Q̂` conclusion is hidden in a structure field. -/
theorem section13_comparison_of_P_abs_le
    {H : Section13HatLayers} {ρ s : ℝ} (_hρ0 : 0 ≤ ρ) (_hρ1 : ρ < 1)
    (hP : |section13Phat H s| ≤ ρ * section13Qhat H s) :
    ((1 - ρ) / 2) * section13Qhat H s ≤ H.T .plus s ∧
      H.T .plus s ≤ ((1 + ρ) / 2) * section13Qhat H s ∧
    ((1 - ρ) / 2) * section13Qhat H s ≤ H.T .minus s ∧
      H.T .minus s ≤ ((1 + ρ) / 2) * section13Qhat H s := by
  have habs := (abs_le).mp hP
  have hlo : -(ρ * section13Qhat H s) ≤ section13Phat H s := habs.1
  have hhi : section13Phat H s ≤ ρ * section13Qhat H s := habs.2
  have hplus : H.T .plus s = (section13Qhat H s + section13Phat H s) / 2 := by
    simp [section13Qhat, section13Phat]
  have hminus : H.T .minus s = (section13Qhat H s - section13Phat H s) / 2 := by
    simp [section13Qhat, section13Phat]
  rw [hplus, hminus]
  constructor
  · ring_nf at ⊢
    nlinarith
  constructor
  · ring_nf at ⊢
    nlinarith
  constructor
  · ring_nf at ⊢
    nlinarith
  · ring_nf at ⊢
    nlinarith

end MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne
