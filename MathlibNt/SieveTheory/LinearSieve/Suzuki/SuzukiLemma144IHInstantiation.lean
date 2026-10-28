import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144Equation1410
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma87FiniteSourceRecursion

open scoped Classical BigOperators
open Finset Set

namespace MathlibNt.SieveTheory.SwitchingPrinciple
namespace SuzukiLemma144Equation1410

open SuzukiFiniteContinuousLayers
open SuzukiFiniteContinuousLayers.KappaOneModel


/-- The earliest outer-geometry edge not supplied by the current (14.10)
carrier API.  It is deliberately frozen separately: this is exactly what is
needed to retain a prescribed global-IH cutoff after division by every carrier
prime, and is not itself an induction hypothesis or endpoint estimate. -/
def CarrierQuotientThresholdGeometry
    (support : Finset ℕ) (D Dmin : ℕ) (σ τ : ℝ) : Prop :=
  ∀ p ∈ sigmaOneCarrier support D σ τ, Dmin * p ≤ D

/-- A quotient-scale lower bound simultaneously verifies the induction
threshold and that the natural recursive cutoff is at least two. -/
theorem ceilDiv_ge_threshold_of_scale
    {D p Dmin : ℕ} (hp : 0 < p) (hscale : Dmin * p ≤ D) :
    Dmin ≤ D ⌈/⌉ p := by
  have hfloor : Dmin ≤ D / p := by
    rw [Nat.le_div_iff_mul_le hp]
    simpa [Nat.mul_comm] using hscale
  have hdivceil : D / p ≤ D ⌈/⌉ p := by
    rw [Nat.ceilDiv_eq_add_pred_div]
    apply Nat.div_le_div_right
    omega
  exact hfloor.trans hdivceil

/-- The recursive logarithmic coordinate really parametrizes the natural
endpoint `p` by a real power.  Thus it is admissible for the global IH rather
than merely an unrelated pointwise coordinate. -/
theorem recursiveCoordinate_power_identity
    {D p : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ D ⌈/⌉ p) :
    (((D ⌈/⌉ p : ℕ) : ℝ) ^ (1 / recursiveCoordinate D p) = (p : ℝ)) := by
  have hpR : (0 : ℝ) < (p : ℝ) := by positivity
  have hqR : (0 : ℝ) < ((D ⌈/⌉ p : ℕ) : ℝ) := by positivity
  have hlogp : Real.log (p : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by exact_mod_cast (show 1 < p by omega)))
  have hlogq : Real.log ((D ⌈/⌉ p : ℕ) : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by exact_mod_cast (show 1 < D ⌈/⌉ p by omega)))
  rw [Real.rpow_def_of_pos hqR, recursiveCoordinate]
  field_simp [hlogp, hlogq]
  rw [Real.exp_log hpR]

/-- Suzuki's parity domains are upward closed. -/
theorem parityDomain_mono {β : ℝ} {n : ℕ} {x y : ℝ}
    (hx : x ∈ KappaOneModel.parityDomain β n) (hxy : x ≤ y) :
    y ∈ KappaOneModel.parityDomain β n := by
  exact MathlibNt.SieveTheory.SwitchingPrinciple.parityDomain_upperClosed hx hxy


end SuzukiLemma144Equation1410
end MathlibNt.SieveTheory.SwitchingPrinciple
