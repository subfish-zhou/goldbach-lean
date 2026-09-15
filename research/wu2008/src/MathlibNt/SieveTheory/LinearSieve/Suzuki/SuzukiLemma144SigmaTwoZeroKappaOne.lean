import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144SigmaTwoDichotomy
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiNatCeilPowerCarrier

open scoped Classical BigOperators Interval
open Finset MeasureTheory Set

namespace MathlibNt.SieveTheory

open LinearSieve SwitchingPrinciple

set_option maxHeartbeats 1600000

/-!
# Direct elimination of `Σ₂` in the genuine `κ = 1`, Case-I range

For `D ≥ 4`, the corrected branch in the definition of `τ` is at most `2`.
Thus `2 ≤ s` forces `τ = s`.  Since `z` is the natural ceiling of the same
strict real cutoff, the integer carrier of `Σ₂` is empty.
-/

/-- In the Case-I range `D ≥ 4`, Suzuki's corrected branch is at most `2`. -/
theorem lemma144_correctedBranch_le_two
    {D : ℕ} (hD : 4 ≤ D) :
    (1 - Real.log 2 / Real.log (D : ℝ))⁻¹ ≤ (2 : ℝ) := by
  have hD1 : (1 : ℝ) < D := by exact_mod_cast (show 1 < D by omega)
  have hlogD : 0 < Real.log (D : ℝ) := Real.log_pos hD1
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlog4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    ring
  have hmono : Real.log (4 : ℝ) ≤ Real.log (D : ℝ) := by
    exact Real.strictMonoOn_log.monotoneOn
      (by norm_num : (4 : ℝ) ∈ Set.Ioi 0)
      (by
        change (0 : ℝ) < D
        exact_mod_cast (show 0 < D by omega))
      (by exact_mod_cast hD)
  have hratio : Real.log 2 / Real.log (D : ℝ) ≤ (1 / 2 : ℝ) := by
    rw [div_le_iff₀ hlogD]
    rw [hlog4] at hmono
    nlinarith
  have hden : (1 / 2 : ℝ) ≤ 1 - Real.log 2 / Real.log (D : ℝ) := by
    linarith
  have hden0 : 0 < 1 - Real.log 2 / Real.log (D : ℝ) := by
    linarith
  have hinv0 : 0 ≤ (1 - Real.log 2 / Real.log (D : ℝ))⁻¹ :=
    inv_nonneg.mpr hden0.le
  have hmul := mul_le_mul_of_nonneg_right hden hinv0
  have hcancel :
      (1 - Real.log 2 / Real.log (D : ℝ)) *
          (1 - Real.log 2 / Real.log (D : ℝ))⁻¹ = 1 := by
    exact mul_inv_cancel₀ (ne_of_gt hden0)
  rw [hcancel] at hmul
  linarith

/-- In the genuine `κ = 1`, `β = 2`, Case-I range, the literal real splitting
parameter is `s`; the corrected branch cannot dominate. -/
theorem lemma144_realTau_eq_s_of_caseI
    {D : ℕ} {s : ℝ} (hD : 4 ≤ D) (hs : 2 ≤ s) :
    lemma144RealTau D s = s := by
  unfold lemma144RealTau
  exact max_eq_left ((lemma144_correctedBranch_le_two hD).trans hs)

/-- With the source natural ceiling, the strict upper carrier and the real
power cutoff define the same strict inequality on natural numbers. -/
theorem lemma144_nat_lt_z_iff_lt_root
    {D z p : ℕ} {s : ℝ} (hD : 4 ≤ D)
    (hz : z = ⌈(D : ℝ) ^ (1 / s)⌉₊) :
    p < z ↔ (p : ℝ) < (D : ℝ) ^ (1 / s) := by
  apply nat_lt_natCeil_iff_lt_real
  · exact natCast_rpow_one_div_pos (by omega) s
  · exact hz

/-- Direct Case-I elimination of the actual `Σ₂`: no `lower_eq_half` input and
no estimate for `Σ₂` are used. -/
theorem lemma144_sigmaTwo_eq_zero_of_kappaOne_caseI
    (S : BoundingSieve) {N D z : ℕ} {s : ℝ}
    (hD : 4 ≤ D) (hs : 2 ≤ s)
    (hz : z = ⌈(D : ℝ) ^ (1 / s)⌉₊) :
    suzukiSigmaTwo S N D z
      ((D : ℝ) ^ (1 / lemma144RealTau D s)) = 0 := by
  classical
  have htau : lemma144RealTau D s = s :=
    lemma144_realTau_eq_s_of_caseI hD hs
  unfold suzukiSigmaTwo
  apply Finset.sum_eq_zero
  intro p hp
  have hp' := Finset.mem_filter.mp hp
  have hpz : p < z := (Finset.mem_filter.mp hp'.1).2
  have hproot : (p : ℝ) < (D : ℝ) ^ (1 / s) :=
    (lemma144_nat_lt_z_iff_lt_root hD hz).1 hpz
  have hrootp : (D : ℝ) ^ (1 / s) ≤ (p : ℝ) := by
    simpa [htau] using hp'.2
  exact False.elim ((not_le_of_gt hproot) hrootp)


end MathlibNt.SieveTheory
