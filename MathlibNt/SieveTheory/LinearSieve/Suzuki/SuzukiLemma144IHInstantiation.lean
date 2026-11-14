module

public import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144Equation1410
public import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma87FiniteSourceRecursion

@[expose] public section

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

/-- A square cutoff bounds the quotient threshold on every carrier with `2 ≤ τ`. -/
theorem carrierQuotientThresholdGeometry_of_square_le
    {support : Finset ℕ} {D Dmin : ℕ} {σ τ : ℝ}
    (hDmin : 2 ≤ Dmin) (hD : Dmin ^ 2 ≤ D) (hτ : 2 ≤ τ) :
    CarrierQuotientThresholdGeometry support D Dmin σ τ := by
  intro p hp
  have hroot := (Finset.mem_filter.mp hp).2.2
  have hD1 : (1 : ℝ) ≤ D := by
    exact_mod_cast (show 1 ≤ D by nlinarith)
  have hpRoot : (p : ℝ) < Real.sqrt D := by
    rw [Real.sqrt_eq_rpow]
    refine hroot.trans_le (Real.rpow_le_rpow_of_exponent_le hD1 ?_)
    exact one_div_le_one_div_of_le (by norm_num) hτ
  have hpSquare : p ^ 2 ≤ D := by
    exact_mod_cast ((Real.lt_sqrt (Nat.cast_nonneg p)).mp hpRoot).le
  calc
    Dmin * p ≤ max Dmin p * max Dmin p :=
      Nat.mul_le_mul (le_max_left _ _) (le_max_right _ _)
    _ = (max Dmin p) ^ 2 := (pow_two _).symm
    _ ≤ D := by
      rcases le_total Dmin p with h | h
      · simpa only [max_eq_right h] using hpSquare
      · simpa only [max_eq_left h] using hD

/-- A quotient-scale lower bound simultaneously verifies the induction
threshold and that the natural recursive cutoff is at least two. -/
theorem ceilDiv_ge_threshold_of_scale
    {D p Dmin : ℕ} (hp : 0 < p) (hscale : Dmin * p ≤ D) :
    Dmin ≤ D ⌈/⌉ p := by
  have hfloor : Dmin ≤ D / p := by
    rw [Nat.le_div_iff_mul_le hp]
    simpa [Nat.mul_comm] using hscale
  exact hfloor.trans (floorDiv_le_ceilDiv (a := p) (b := D))

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
