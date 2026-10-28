import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma87DimensionOne
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma133WeightedTail
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiClaim146Integral
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiClaim146ShortInterval

open scoped Classical BigOperators
open MeasureTheory Set

namespace MathlibNt.SieveTheory.SwitchingPrinciple
namespace SuzukiLemma144KappaOne

set_option maxHeartbeats 800000

/-! ## Source-faithful statement of Claim 14.5 (κ = 1) -/

/-- The finite Euler product `V(x)` on the production support, repeated here
because the older base-case temporary module cannot be jointly imported with
the current Lemma-8.7 umbrella without a declaration collision. -/
noncomputable def claim14_5VProduct (S : BoundingSieve) (x : ℝ) : ℝ :=
  ∏ p ∈ S.prodPrimes.primeFactors.filter (fun p : ℕ => (p : ℝ) < x),
    (1 - S.nu p)

/-- The explicit quantity on the right of Claim 14.5 after replacing the
source `≪` by a named multiplicative constant.  At κ=1 this uses the literal
`E_N`, represented by `errorEnvelope`, and the finite Euler product `V(D)`.
The source has `exp (sqrt K)/(σ log D)` and a further `(log D)^(-Δ)`. -/
noncomputable def claim14_5Scale
    (S : BoundingSieve) (H : Section13HatLayers) (N : ℕ)
    (D d Δ σ K s : ℝ) : ℝ :=
  claim14_5VProduct S D * (Real.exp (Real.sqrt K) / (Real.log D * σ)) *
    errorEnvelope H N D d s * (Real.log D) ^ (-Δ)

/-- Exact non-asymptotic interface for Claim 14.5. `Tdisc N D z` is the
(real-parameter) discrete parity sum from the paper; no such object currently
exists in the production API, whose source-faithful discrete model has natural
cutoffs.  `C145` records precisely the implicit absolute constant in `≪`. -/
def Claim14_5Bound
    (Tdisc : ℕ → ℝ → ℝ → ℝ) (S : BoundingSieve) (H : Section13HatLayers)
    (N : ℕ) (D z d Δ σ K s C145 : ℝ) : Prop :=
  Tdisc N D z ≤ C145 * claim14_5Scale S H N D d Δ σ K s

/-- The exact range in which Suzuki invokes Claim 14.5. -/
def Claim14_5Regime (β D σ C1 K ΘK s : ℝ) : Prop :=
  β ≤ s ∧ (Real.log D ≤ C1 * K ^ ΘK ∨ σ ≤ s)


/-! ## Lemma 8.7 connected to Claim 14.6 -/

/-- Global continuous clamp of `q_D`; it agrees with `q_D` on `[τ,∞)` and
allows direct use of the global-continuity interface of Lemma 8.7. -/
noncomputable def qDClamp
    (H : Section13HatLayers) (sign : ErrorSign)
    (D d Δ τ t : ℝ) : ℝ :=
  qD H sign D d Δ (max τ t)

@[simp] theorem qDClamp_eq_of_le
    (H : Section13HatLayers) (sign : ErrorSign) (D d Δ : ℝ)
    {τ t : ℝ} (hτt : τ ≤ t) :
    qDClamp H sign D d Δ τ t = qD H sign D d Δ t := by
  simp [qDClamp, max_eq_right hτt]


/-- At κ=1, the normalized endpoint `s⁻¹ Λ₀` is literally the current
source-correct error envelope `E_N`. -/
theorem one_div_mul_lambda_eq_errorEnvelope
    (H : Section13HatLayers) {N : ℕ} {D d s : ℝ} (hs : 0 < s) :
    (1 / s) * lambda H (ErrorSign.ofDepth N) D d 0 s =
      errorEnvelope H N D d s := by
  simp only [lambda, errorEnvelope, Section13HatLayers.kappaHat]
  norm_num [Real.rpow_one]
  field_simp [ne_of_gt hs]


end SuzukiLemma144KappaOne
end MathlibNt.SieveTheory.SwitchingPrinciple
