import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiMovingSigmaClaim146SourceAssembly

open scoped Classical BigOperators Interval
open Set Filter Topology MeasureTheory intervalIntegral

namespace MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne

set_option maxHeartbeats 400000

/-!
# Proposition 13.1(iii): quantitative hat-tail decay

`Section13HatContract` records the DDE, initial values, positivity, and only the
qualitative limit `weightedHat → 0`.  The missing publication interface is a
*quantitative modulus* for the adjacent tail ratio.  The upstream contract below
records the source-strength `(M log (eM))⁻²` estimate at `M`; monotonicity from
the DDE then compares `M` with every `s ≤ M`.  Thus this is not the downstream
consumer contract (which has already forgotten the logarithmic gain).
-/

/-- Minimal source-level asymptotic datum: the stronger adjacent-value estimate
of Proposition 13.1(iii), retaining its logarithmic gain.  It is independent of
`D`, `d`, `Δ`, `sourceSigma`, `lambda`, and the Claim 14.6 integral. -/
def Section13HatAsymptoticContract (H : Section13HatLayers) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (sign : ErrorSign) (M : ℝ), 4 ≤ M →
    weightedHat H sign (M + 2) ≤
      (C / (M * Real.log (Real.exp 1 * M)) ^ 2) *
        weightedHat H sign M

/-- The DDE makes the weighted hat layer antitone even when the left endpoint is
exactly the delay threshold.  The production strict-endpoint lemma cannot be
applied directly there, but its derivative proof works on the interior. -/
theorem weightedHat_antitoneOn_Icc_closed
    {H : Section13HatLayers} (hH : Section13HatContract H 2)
    (sign : ErrorSign) {s M : ℝ}
    (hs : 2 + sign.epsilon ≤ s) :
    AntitoneOn (weightedHat H sign) (Icc s M) := by
  have heps : 0 ≤ sign.epsilon := by
    cases sign <;> simp [ErrorSign.epsilon]
  have hs0 : 0 < s := by linarith
  apply antitoneOn_of_deriv_nonpos (convex_Icc s M)
  · exact (continuousOn_id.pow 2).mul
      ((hH.continuous sign).mono (by
        intro x hx
        exact hs0.trans_le hx.1))
  · intro x hx
    have hx' : x ∈ Ioo s M := by simpa only [interior_Icc] using hx
    exact (hH.dde sign x (lt_of_le_of_lt hs hx'.1)).differentiableAt.differentiableWithinAt
  · intro x hx
    have hx' : x ∈ Ioo s M := by simpa only [interior_Icc] using hx
    rw [(hH.dde sign x (lt_of_le_of_lt hs hx'.1)).deriv]
    have hx0 : 0 ≤ x := (hs0.trans hx'.1).le
    have hs2 : 2 ≤ s := by linarith
    have hxm1 : 0 < x - 1 := by linarith [hs2, hx'.1]
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hx0)
      (le_of_lt (hH.positive sign.opposite (x - 1) hxm1))

private lemma log_e_mul_ge_one {M : ℝ} (hM : 4 ≤ M) :
    1 ≤ Real.log (Real.exp 1 * M) := by
  have hM1 : 1 ≤ M := by linarith
  have hMne : M ≠ 0 := by linarith
  rw [Real.log_mul (Real.exp_ne_zero 1) hMne, Real.log_exp]
  linarith [Real.log_nonneg hM1]

/-- Source-strength Proposition 13.1(iii): the adjacent asymptotic estimate plus
DDE monotonicity gives the full ratio estimate for every source point `s ≤ M`. -/
theorem proposition131_source_strength_tail_decay
    {H : Section13HatLayers} (hH : Section13HatContract H 2)
    (hAsymp : Section13HatAsymptoticContract H) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (sign : ErrorSign) (M s : ℝ),
      4 ≤ M → 2 + sign.epsilon ≤ s → s ≤ M →
      weightedHat H sign (M + 2) ≤
        (C / (M * Real.log (Real.exp 1 * M)) ^ 2) *
          weightedHat H sign s := by
  obtain ⟨C, hC, hAdjacent⟩ := hAsymp
  refine ⟨C, hC, ?_⟩
  intro sign M s hM hs hsM
  have hmono : weightedHat H sign M ≤ weightedHat H sign s :=
    weightedHat_antitoneOn_Icc_closed hH sign hs
      (show s ∈ Icc s M by exact ⟨le_rfl, hsM⟩)
      (show M ∈ Icc s M by exact ⟨hsM, le_rfl⟩) hsM
  have hMpos : 0 < M := by linarith
  have hlog : 0 < Real.log (Real.exp 1 * M) :=
    lt_of_lt_of_le zero_lt_one (log_e_mul_ge_one hM)
  have hcoef : 0 ≤ C /
      (M * Real.log (Real.exp 1 * M)) ^ 2 :=
    div_nonneg hC (sq_nonneg _)
  exact (hAdjacent sign M hM).trans
    (mul_le_mul_of_nonneg_left hmono hcoef)

/-- Forgetting the logarithmic gain yields exactly the moving proof's
`Proposition131TailDecayContract`. -/
theorem section13HatAsymptoticContract_implies_proposition131TailDecay
    {H : Section13HatLayers} (hH : Section13HatContract H 2)
    (hAsymp : Section13HatAsymptoticContract H) :
    Proposition131TailDecayContract H := by
  obtain ⟨C, hC, hstrong⟩ :=
    proposition131_source_strength_tail_decay hH hAsymp
  refine ⟨C, hC, ?_⟩
  intro sign M s hM hs hsM
  have hMpos : 0 < M := by linarith
  have hL : 1 ≤ Real.log (Real.exp 1 * M) := log_e_mul_ge_one hM
  have hML : M ≤ M * Real.log (Real.exp 1 * M) := by
    nlinarith
  have hsq : M ^ 2 ≤ (M * Real.log (Real.exp 1 * M)) ^ 2 :=
    (sq_le_sq₀ hMpos.le (mul_nonneg hMpos.le (zero_le_one.trans hL))).2 hML
  have hcoef : C / (M * Real.log (Real.exp 1 * M)) ^ 2 ≤ C / M ^ 2 :=
    div_le_div_of_nonneg_left hC (sq_pos_of_pos hMpos) hsq
  have hWs : 0 ≤ weightedHat H sign s := by
    have hs0 : 0 < s := by
      have heps : 0 ≤ sign.epsilon := by
        cases sign <;> simp [ErrorSign.epsilon]
      linarith
    exact (mul_pos (sq_pos_of_pos hs0) (hH.positive sign s hs0)).le
  exact (hstrong sign M s hM hs hsM).trans
    (mul_le_mul_of_nonneg_right hcoef hWs)


end MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne
