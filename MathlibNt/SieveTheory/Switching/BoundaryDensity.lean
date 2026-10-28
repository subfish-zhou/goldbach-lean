import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

/-!
# Rosser boundary densities and dyadic tails

Dyadic log-ratio cells control far alternating pairs. Mesh corrections, atomic
bounds, and factorial density estimates majorize finite Rosser boundary chains.

All declarations retain the `MathlibNt.SieveTheory.SwitchingPrinciple` namespace.
-/

open scoped ArithmeticFunction.Moebius
open scoped ArithmeticFunction.zeta

set_option maxHeartbeats 6000000

namespace MathlibNt.SieveTheory.SwitchingPrinciple

open Real Finset

open scoped Classical
open scoped Asymptotics

namespace Internal
end Internal

open Internal


/-- A sieve ratio strictly larger than one places every integer below the
sifting cutoff strictly below the natural Rosser level `⌊Δ⌋ + 1`. -/
theorem lt_floor_add_one_of_le_of_log_ratio
    {p : ℕ} {z Δ s : ℝ} (hz : 2 ≤ z) (hΔ : 0 < Δ)
    (hp : (p : ℝ) ≤ z) (hs : s = Real.log Δ / Real.log z)
    (hslo : 3 / 2 ≤ s) :
    p < Nat.floor Δ + 1 := by
  have hzpos : 0 < z := by linarith
  have hlogz : 0 < Real.log z := Real.log_pos (by linarith)
  have hs1 : 1 < s := by linarith
  have hlogeq : Real.log Δ = s * Real.log z := by
    rw [hs]
    field_simp
  have hloglt : Real.log z < Real.log Δ := by
    rw [hlogeq]
    nlinarith
  have hzΔ : z < Δ :=
    (Real.strictMonoOn_log.lt_iff_lt hzpos hΔ).mp hloglt
  have hpΔ : (p : ℝ) < Δ := hp.trans_lt hzΔ
  have hΔfloor : Δ < (Nat.floor Δ + 1 : ℕ) :=
    by simpa using Nat.lt_floor_add_one Δ
  exact_mod_cast hpΔ.trans hΔfloor


end MathlibNt.SieveTheory.SwitchingPrinciple
