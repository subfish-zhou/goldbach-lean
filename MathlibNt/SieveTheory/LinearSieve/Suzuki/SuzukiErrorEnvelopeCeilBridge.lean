import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144Equation1410

/-!
# Claim 14.6(i) bridge for the ceiling-coordinate error envelope

At `κ = 1`, the production error envelope satisfies
`E_N(D,s) = Λ₀^{sign(N)}(s) / s`.  Thus, on a positive interval,
nonnegativity and antitonicity of `Λ₀` imply antitonicity of `E_N`.
The final theorem supplies this fact to the `hError` slot of the natural-ceiling
coordinate bridge from `SuzukiLemma144Equation1410`.
-/

open Set

namespace MathlibNt.SieveTheory.SwitchingPrinciple
namespace SuzukiLemma144KappaOne

open SuzukiLemma144Equation1410

/-- At `κ = 1`, the production error envelope is `Λ₀/s` at the parity sign
selected by the depth. -/
theorem errorEnvelope_eq_lambda_div
    (H : Section13HatLayers) {N : ℕ} {D d s : ℝ} (hs : 0 < s) :
    errorEnvelope H N D d s =
      lambda H (ErrorSign.ofDepth N) D d 0 s / s := by
  simp only [lambda, errorEnvelope, Section13HatLayers.kappaHat]
  norm_num [Real.rpow_one]
  field_simp [ne_of_gt hs]

/-- Claim 14.6(i), together with the Section-13 positivity package, makes the
production error envelope antitone on the matching parity interval.  The proof
uses `E = Λ₀/s`: both `Λ₀` and `1/s` decrease on a positive interval, while
`Λ₀` is nonnegative. -/
theorem errorEnvelope_antitoneOn_of_claim14_6
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
  rw [errorEnvelope_eq_lambda_div H hy0, errorEnvelope_eq_lambda_div H hx0]
  exact (div_le_div_of_nonneg_right hlam hy0.le).trans
    (div_le_div_of_nonneg_left hlamx0 hx0 hxy)


end SuzukiLemma144KappaOne
end MathlibNt.SieveTheory.SwitchingPrinciple
