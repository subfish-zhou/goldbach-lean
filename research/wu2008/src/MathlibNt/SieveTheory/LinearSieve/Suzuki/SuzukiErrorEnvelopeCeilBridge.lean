import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiSection13HatLayersKappaOne
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiFiniteContinuousLayersKappaOne
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

/-- Production instantiation of the natural-ceiling source-coordinate bridge.
For each recursive natural argument `⌈D/p⌉`, Claim 14.6(i) is assumed on its
matching parity domain.  When both the inherited and recursive coordinates lie
in that domain, the preceding antitonicity theorem discharges `hError`.

The elementary hypotheses `2 ≤ p` and `2p ≤ D` provide both the ordering of the
two coordinates and `1 < ⌈D/p⌉`, the positivity condition needed by the
production `errorEnvelope` normalization. -/
theorem naturalCeilContract_to_sourceCoordinate_errorEnvelope_of_claim14_6
    (support : Finset ℕ) (T : ℕ → ℕ → ℕ → ℝ) (V : ℕ → ℝ)
    (H : Section13HatLayers) (β C K Δ d : ℝ) (N D : ℕ) (σ τ : ℝ)
    (hH : Section13HatContract H β)
    (hV : ∀ p ∈ sigmaOneCarrier support D σ τ, 0 ≤ V p)
    (hC : 0 ≤ C)
    (hlog : ∀ p ∈ sigmaOneCarrier support D σ τ,
      0 ≤ Real.log ((D ⌈/⌉ p : ℕ) : ℝ))
    (hSource : ∀ p ∈ sigmaOneCarrier support D σ τ,
      SuzukiFiniteContinuousLayers.finiteSourceLayer 1 β (N - 1)
          (recursiveCoordinate D p) ≤
        SuzukiFiniteContinuousLayers.finiteSourceLayer 1 β (N - 1)
          (inheritedCoordinate D p))
    (hCeil : ∀ p ∈ sigmaOneCarrier support D σ τ, 2 ≤ p ∧ 2 * p ≤ D)
    (hClaim : ∀ p ∈ sigmaOneCarrier support D σ τ,
      Claim14_6_MonotoneLambdaPremise H ((D ⌈/⌉ p : ℕ) : ℝ) d σ)
    (hDomain : ∀ p ∈ sigmaOneCarrier support D σ τ,
      inheritedCoordinate D p ∈
          Icc (H.betaHat + (ErrorSign.ofDepth (N - 1)).epsilon) σ ∧
      recursiveCoordinate D p ∈
          Icc (H.betaHat + (ErrorSign.ofDepth (N - 1)).epsilon) σ)
    (hIH : NaturalCeilPointwiseInductionContract support T V
      (fun n D' s => errorEnvelope H n (D' : ℝ) d s)
      β C K Δ N D σ τ) :
    PointwiseInductionContract support T V
      (fun n D' s => errorEnvelope H n (D' : ℝ) d s)
      β C K Δ N D σ τ := by
  apply naturalCeilContract_to_sourceCoordinate support T V
    (fun n D' s => errorEnvelope H n (D' : ℝ) d s)
    β C K Δ N D σ τ hV hC hlog hSource
  · intro p hp
    have hp2 : 2 ≤ p := (hCeil p hp).1
    have hpR : (0 : ℝ) < (p : ℝ) := by
      exact_mod_cast (show 0 < p by omega)
    have hdiv2 : (2 : ℝ) ≤ (D : ℝ) / (p : ℝ) := by
      rw [le_div_iff₀ hpR]
      exact_mod_cast (hCeil p hp).2
    have hceil2 : (2 : ℝ) ≤ ((D ⌈/⌉ p : ℕ) : ℝ) := by
      calc
        (2 : ℝ) ≤ (D : ℝ) / (p : ℝ) := hdiv2
        _ ≤ ((D ⌈/⌉ p : ℕ) : ℝ) := by
          rw [div_le_iff₀ hpR]
          exact_mod_cast
            (ceilDiv_mul_bounds (D := D) (p := p) (by omega : 0 < p)).1
    have hanti := errorEnvelope_antitoneOn_of_claim14_6 (N - 1) hH
      (lt_of_lt_of_le (by norm_num) hceil2) (hClaim p hp)
    exact hanti (hDomain p hp).1 (hDomain p hp).2
      (coordinate_bounds (hCeil p hp).1 (hCeil p hp).2).1
  · exact hIH

/-- Fully discharged production ceiling bridge.  In addition to Claim 14.6(i)
for the error envelope, Proposition 9.3 supplies the source-layer comparison
from the same explicit ceiling bounds and the two parity-domain memberships.
Thus callers provide the genuine natural-ceiling induction contract, with no
pre-packaged `hSource` or `hError` inequality. -/
theorem naturalCeilContract_to_sourceCoordinate_errorEnvelope_of_claim14_6_and_parityDomain
    (support : Finset ℕ) (T : ℕ → ℕ → ℕ → ℝ) (V : ℕ → ℝ)
    (H : Section13HatLayers) (β C K Δ d : ℝ) (N D : ℕ) (σ τ : ℝ)
    (hH : Section13HatContract H β)
    (hV : ∀ p ∈ sigmaOneCarrier support D σ τ, 0 ≤ V p)
    (hC : 0 ≤ C)
    (hlog : ∀ p ∈ sigmaOneCarrier support D σ τ,
      0 ≤ Real.log ((D ⌈/⌉ p : ℕ) : ℝ))
    (hCeil : ∀ p ∈ sigmaOneCarrier support D σ τ, 2 ≤ p ∧ 2 * p ≤ D)
    (hSourceDomain : ∀ p ∈ sigmaOneCarrier support D σ τ,
      inheritedCoordinate D p ∈ SuzukiFiniteContinuousLayers.KappaOneModel.parityDomain β (N - 1) ∧
      recursiveCoordinate D p ∈ SuzukiFiniteContinuousLayers.KappaOneModel.parityDomain β (N - 1))
    (hClaim : ∀ p ∈ sigmaOneCarrier support D σ τ,
      Claim14_6_MonotoneLambdaPremise H ((D ⌈/⌉ p : ℕ) : ℝ) d σ)
    (hErrorDomain : ∀ p ∈ sigmaOneCarrier support D σ τ,
      inheritedCoordinate D p ∈
          Icc (H.betaHat + (ErrorSign.ofDepth (N - 1)).epsilon) σ ∧
      recursiveCoordinate D p ∈
          Icc (H.betaHat + (ErrorSign.ofDepth (N - 1)).epsilon) σ)
    (hIH : NaturalCeilPointwiseInductionContract support T V
      (fun n D' s => errorEnvelope H n (D' : ℝ) d s)
      β C K Δ N D σ τ) :
    PointwiseInductionContract support T V
      (fun n D' s => errorEnvelope H n (D' : ℝ) d s)
      β C K Δ N D σ τ := by
  apply naturalCeilContract_to_sourceCoordinate_errorEnvelope_of_claim14_6
    support T V H β C K Δ d N D σ τ hH hV hC hlog
  · intro p hp
    exact finiteSourceLayer_recursive_le_inherited hH.beta_gt_one (N - 1) D p
      (hCeil p hp).1 (hCeil p hp).2
      (hSourceDomain p hp).1 (hSourceDomain p hp).2
  · exact hCeil
  · exact hClaim
  · exact hErrorDomain
  · exact hIH

end SuzukiLemma144KappaOne
end MathlibNt.SieveTheory.SwitchingPrinciple
