import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiSection13HatLayersKappaOne
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiFiniteContinuousLayersKappaOne
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144Equation1410

/-!
# Claim 14.6(i) to the production error envelope

The production definitions do not identify `lambda H sign D d 0 s` directly
with `errorEnvelope H N D d s`: at `κ = 1`, `lambda` has one additional factor
of `s`.  This file records the exact normalization and derives the endpoint
transport needed from Claim 14.6(i).
-/

open Set

namespace MathlibNt.SieveTheory.SwitchingPrinciple
namespace SuzukiLemma144KappaOne

open SuzukiFiniteContinuousLayers

/-- Exact production normalization at `κ = 1`. -/
theorem errorEnvelope_eq_lambda_div_internal
    (H : Section13HatLayers) {N : ℕ} {D d s : ℝ} (hs : 0 < s) :
    errorEnvelope H N D d s =
      lambda H (ErrorSign.ofDepth N) D d 0 s / s := by
  simp only [lambda, errorEnvelope, Section13HatLayers.kappaHat]
  norm_num [Real.rpow_one]
  field_simp [ne_of_gt hs]

/-- Equivalent orientation: `lambda` is `s` times the error envelope, rather
than literally the error envelope. -/
theorem lambda_eq_s_mul_errorEnvelope
    (H : Section13HatLayers) {N : ℕ} {D d s : ℝ} (hs : 0 < s) :
    lambda H (ErrorSign.ofDepth N) D d 0 s =
      s * errorEnvelope H N D d s := by
  rw [errorEnvelope_eq_lambda_div_internal H hs]
  field_simp [ne_of_gt hs]

/-- Claim 14.6(i) makes the production error envelope antitone on the matching
parity interval. -/
theorem errorEnvelope_antitoneOn_of_claim14_6_internal
    {H : Section13HatLayers} {β D d σ : ℝ} (N : ℕ)
    (hH : Section13HatContract H β) (hD : 1 < D)
    (hi : Claim14_6_MonotoneLambdaPremise H D d σ) :
    AntitoneOn (errorEnvelope H N D d)
      (Icc (H.betaHat + (ErrorSign.ofDepth N).epsilon) σ) := by
  let sign := ErrorSign.ofDepth N
  have heps : 0 ≤ sign.epsilon := by
    cases sign <;> simp [ErrorSign.epsilon]
  have hleft : 0 < H.betaHat + sign.epsilon := by
    rw [hH.betaHat_eq]
    linarith [hH.beta_gt_one]
  intro x hx y hy hxy
  have hx0 : 0 < x := hleft.trans_le hx.1
  have hy0 : 0 < y := hleft.trans_le hy.1
  have hlam : lambda H sign D d 0 y ≤ lambda H sign D d 0 x :=
    hi sign 0 (Or.inl rfl) hx hy hxy
  have hlamx0 : 0 ≤ lambda H sign D d 0 x :=
    lambda_nonneg H sign hD (by norm_num) hx0.le
      (hH.positive sign x hx0).le
  change errorEnvelope H N D d y ≤ errorEnvelope H N D d x
  rw [errorEnvelope_eq_lambda_div_internal H hy0,
    errorEnvelope_eq_lambda_div_internal H hx0]
  exact (div_le_div_of_nonneg_right hlam hy0.le).trans
    (div_le_div_of_nonneg_left hlamx0 hx0 hxy)

/-- Pointwise endpoint transport `E(σ) ≤ E(s)` under the Claim 14.6(i)
domain hypotheses. -/
theorem errorEnvelope_endpoint_le_of_claim14_6
    {H : Section13HatLayers} {β D d σ s : ℝ} {N : ℕ}
    (hH : Section13HatContract H β) (hD : 1 < D)
    (hi : Claim14_6_MonotoneLambdaPremise H D d σ)
    (hs : s ∈ Icc (H.betaHat + (ErrorSign.ofDepth N).epsilon) σ) :
    errorEnvelope H N D d σ ≤ errorEnvelope H N D d s := by
  have hanti := errorEnvelope_antitoneOn_of_claim14_6_internal N hH hD hi
  exact hanti hs ⟨hs.1.trans hs.2, le_rfl⟩ hs.2


end SuzukiLemma144KappaOne
end MathlibNt.SieveTheory.SwitchingPrinciple
