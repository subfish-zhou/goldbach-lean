import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiClaim146ShortInterval
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiCaseIISourceSigmaGeometryEventually

open Set Filter Topology

namespace MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne

open MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne

set_option maxHeartbeats 800000

/-!
# Moving-source closure audit for Claims 14.6(i) and (ii)

The fixed-`σ` theorem has quantifiers `∀ σ, ∃ D₀(σ), ∀ D ≥ D₀(σ)` and therefore
cannot be specialized diagonally to `σ = sourceSigma D d`.  The results below
state and prove the strongest source-faithful uniform reductions available from
the production API.

For (i), the exact derivative bracket is exposed.  For (ii), the residual is a
uniform moving-tail/DDE margin `ρ D`, including the short-interval inequality;
this is exactly what `claim14_6_ii_of_log_bound` consumes.
-/

/-- Exact pointwise derivative domination sufficient for Claim 14.6(i) on one
interval.  Unlike the fixed-`σ` compactness proof, this statement is suitable
for a moving upper endpoint: no threshold depending on that endpoint is chosen. -/
theorem claim14_6_i_of_explicit_derivative_domination
    {H : Section13HatLayers} {β D d σ : ℝ}
    (hH : Section13HatContract H β)
    (hlog : 0 < Real.log D)
    (hdom : ∀ (sign : ErrorSign) (ε t : ℝ),
      (ε = 0 ∨ ε = 1) → β + sign.epsilon < t → t < σ →
      weightedHat H sign t * perturbationSlope D d ε t ≤
        t * H.T sign.opposite (t - 1)) :
    Claim14_6_MonotoneLambdaPremise H D d σ := by
  unfold Claim14_6_MonotoneLambdaPremise
  rw [hH.betaHat_eq]
  intro sign ε hε
  have hε0 : 0 ≤ ε := by rcases hε with rfl | rfl <;> norm_num
  have hleft : 1 < β + sign.epsilon := by
    have he : 0 ≤ sign.epsilon := by cases sign <;> simp [ErrorSign.epsilon]
    linarith [hH.beta_gt_one]
  apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
  · have hp : ContinuousOn (perturbation D d ε)
        (Icc (β + sign.epsilon) σ) := by
      intro t ht
      have ht0 : 0 < t := (zero_lt_one.trans hleft).trans_le ht.1
      exact (hasDerivAt_perturbation (d := d) hlog
        (add_pos_of_pos_of_nonneg ht0 hε0)).continuousAt.continuousWithinAt
    have hw : ContinuousOn (weightedHat H sign)
        (Icc (β + sign.epsilon) σ) :=
      (continuousOn_id.pow 2).mul ((hH.continuous sign).mono (by
        intro t ht
        exact (zero_lt_one.trans hleft).trans_le ht.1))
    have hfun : lambda H sign D d ε =
        fun x => perturbation D d ε x * weightedHat H sign x := by
      funext x
      exact lambda_eq_perturb_mul_weightedHat H sign D d ε x
    rw [hfun]
    exact hp.mul hw
  · intro t ht
    have htI : t ∈ Icc (β + sign.epsilon) σ := interior_subset ht
    have htstrict : β + sign.epsilon < t := by
      rw [interior_Icc] at ht
      exact ht.1
    have ht0 : 0 < t := (zero_lt_one.trans hleft).trans htstrict
    exact (hasDerivAt_lambda_of_contract hH sign hlog
      (add_pos_of_pos_of_nonneg ht0 hε0) htstrict).differentiableAt.differentiableWithinAt
  · intro t ht
    have htstrict : β + sign.epsilon < t := by
      rw [interior_Icc] at ht
      exact ht.1
    have htupper : t < σ := by
      rw [interior_Icc] at ht
      exact ht.2
    have ht0 : 0 < t := (zero_lt_one.trans hleft).trans htstrict
    have hte : 0 < t + ε := add_pos_of_pos_of_nonneg ht0 hε0
    have hp0 : 0 ≤ perturbation D d ε t := by
      apply Real.rpow_nonneg
      have hu : 0 ≤ (t + ε) ^ d / Real.log D :=
        div_nonneg (Real.rpow_nonneg hte.le _) hlog.le
      linarith
    rw [(hasDerivAt_lambda_of_contract hH sign hlog hte htstrict).deriv]
    change perturbation D d ε t *
      (weightedHat H sign t * perturbationSlope D d ε t -
        t * H.T sign.opposite (t - 1)) ≤ 0
    exact mul_nonpos_of_nonneg_of_nonpos hp0 (sub_nonpos.mpr
      (hdom sign ε t hε htstrict htupper))

/-- Uniform moving-source closure of Claim 14.6(i) from its explicit derivative
condition.  `sourceSigma` growth is used to put both signs' left endpoints below
the moving endpoint. -/
theorem eventually_claim14_6_i_at_sourceSigma_of_derivative_domination
    {H : Section13HatLayers} {β d : ℝ}
    (hH : Section13HatContract H β) (hd1 : 1 < d)
    (hdom : ∃ Da : ℝ, 1 < Da ∧ ∀ D : ℝ, Da ≤ D →
      ∀ (sign : ErrorSign) (ε t : ℝ),
        (ε = 0 ∨ ε = 1) → β + sign.epsilon < t →
        t < sourceSigma D d →
        weightedHat H sign t * perturbationSlope D d ε t ≤
          t * H.T sign.opposite (t - 1)) :
    ∃ D0 : ℝ, 1 < D0 ∧ ∀ D : ℝ, D0 ≤ D →
      3 ≤ sourceSigma D d ∧
      Claim14_6_MonotoneLambdaPremise H D d (sourceSigma D d) := by
  obtain ⟨Da, hDa, hdom⟩ := hdom
  obtain ⟨D3, hD3, hthree⟩ :=
    exists_sourceSigma_three_threshold d (zero_lt_one.trans hd1)
  let D0 := max Da D3
  refine ⟨D0, hDa.trans_le (le_max_left _ _), ?_⟩
  intro D hD
  have hDaD : Da ≤ D := (le_max_left _ _).trans hD
  have hD3D : D3 ≤ D := (le_max_right _ _).trans hD
  have hD1 : 1 < D := hDa.trans_le hDaD
  have hσ3 : 3 ≤ sourceSigma D d := hthree D hD3D
  exact ⟨hσ3, claim14_6_i_of_explicit_derivative_domination hH
    (Real.log_pos hD1) (hdom D hDaD)⟩

/-- WITHDRAWN / source-incompatible for moving `sourceSigma`.
The second and fourth fields force asymptotically incompatible lower and upper
bounds on `ρ D` (see `CLAIM146_I_II_SOURCE_AUDIT.md`).  Retained only so older
conditional lemmas continue to elaborate; do not use in the production chain. -/
def MovingClaim14_6TailCertificate
    (H : Section13HatLayers) (β d Δ : ℝ) : Prop :=
  ∃ D0 : ℝ, 1 < D0 ∧ ∃ ρ : ℝ → ℝ, ∀ D : ℝ, D0 ≤ D →
    0 < ρ D ∧
    (1 + sourceSigma D d * d) * (sourceSigma D d + 1) ^ d ≤
      ρ D * Real.log D ∧
    (∀ (sign : ErrorSign) (t : ℝ), β + sign.epsilon < t →
      t ≤ sourceSigma D d →
      ρ D * weightedHat H sign t ≤ t * H.T sign.opposite (t - 1)) ∧
    ρ D * (sourceSigma D d * (sourceSigma D d - 1)) ≤ 1 + Δ

/-- Moving-source Claims 14.6(i)/(ii) close uniformly from the exact tail/DDE
certificate above.  This theorem is source-faithful: all dependence on the
moving endpoint remains inside one `∀ D ≥ D0` statement. -/
theorem eventually_claim14_6_i_ii_at_sourceSigma_of_tailCertificate
    {H : Section13HatLayers} {β d Δ : ℝ}
    (hH : Section13HatContract H β) (hd1 : 1 < d)
    (hΔ : -1 ≤ Δ) (hβ2 : β = 2)
    (hcert : MovingClaim14_6TailCertificate H β d Δ) :
    ∃ D0 : ℝ, 1 < D0 ∧ ∀ D : ℝ, D0 ≤ D →
      Claim14_6_MonotoneLambdaPremise H D d (sourceSigma D d) ∧
      Claim14_6_MonotoneQPremise H D d Δ (sourceSigma D d) := by
  rcases hcert with ⟨Da, hDa, ρ, hcert⟩
  obtain ⟨D3, hD3, hthree⟩ :=
    exists_sourceSigma_three_threshold d (zero_lt_one.trans hd1)
  let D0 := max Da D3
  refine ⟨D0, hDa.trans_le (le_max_left _ _), ?_⟩
  intro D hD
  have hDaD : Da ≤ D := (le_max_left _ _).trans hD
  have hD3D : D3 ≤ D := (le_max_right _ _).trans hD
  have hD1 : 1 < D := hDa.trans_le hDaD
  have hσ3 : 3 ≤ sourceSigma D d := hthree D hD3D
  have hσ : ∀ sign : ErrorSign, β + sign.epsilon ≤ sourceSigma D d := by
    intro sign
    subst β
    cases sign <;> simp [ErrorSign.epsilon] <;> linarith
  rcases hcert D hDaD with ⟨hρ, hlarge, hdelay, hshort⟩
  have hi := claim14_6_i_of_log_bound hH (zero_le_one.trans hd1.le) hσ hρ
    (Real.log_pos hD1) hlarge hdelay
  have hii := claim14_6_ii_of_log_bound hH (zero_le_one.trans hd1.le) hΔ hσ hρ
    (Real.log_pos hD1) hlarge hdelay hshort
  constructor
  · simpa [Claim14_6_MonotoneLambdaPremise, hH.betaHat_eq] using hi
  · exact hii


end MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne
