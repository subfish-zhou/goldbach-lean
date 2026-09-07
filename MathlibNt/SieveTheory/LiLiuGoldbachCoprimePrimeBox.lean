import MathlibNt.SieveTheory.LiuPrimePairLogKernel
import MathlibNt.SieveTheory.LiuPanPrimePowerCharacters
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Coprime prime mass on fixed half-open intervals; endpoints precede the limit. -/
namespace MathlibNt.SieveTheory.LiuWeight
open Filter Finset
open scoped Topology BigOperators
open PrimeReciprocalLogScale PrimeReciprocalLogRectangle

noncomputable def primeLogIntervalPrimes (N : ℕ) (a b : ℝ) : Finset ℕ :=
  (range (rpowFloor N b + 1)).filter fun p =>
    p.Prime ∧ (N : ℝ) ^ a < (p : ℝ) ∧ (p : ℝ) ≤ (N : ℝ) ^ b

theorem mem_primeLogIntervalPrimes {N p : ℕ} {a b : ℝ} :
    p ∈ primeLogIntervalPrimes N a b ↔
      p.Prime ∧ (N : ℝ) ^ a < (p : ℝ) ∧ (p : ℝ) ≤ (N : ℝ) ^ b := by
  classical
  simp only [primeLogIntervalPrimes, mem_filter, mem_range]
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨Nat.lt_succ_iff.mpr (Nat.le_floor h.2.2), h⟩

noncomputable def coprimePrimeLogIntervalPrimes (N : ℕ) (a b : ℝ) : Finset ℕ :=
  (primeLogIntervalPrimes N a b).filter fun p => ¬ p ∣ N

noncomputable def coprimePrimeReciprocalLogInterval (N : ℕ) (a b : ℝ) : ℝ :=
  ∑ p ∈ coprimePrimeLogIntervalPrimes N a b, 1 / (p : ℝ)

noncomputable def badPrimeReciprocalLogInterval (N : ℕ) (a b : ℝ) : ℝ :=
  ∑ p ∈ (primeLogIntervalPrimes N a b).filter (fun p => p ∣ N), 1 / (p : ℝ)

theorem coprimePrimeReciprocalLogInterval_eq_sub (N : ℕ) (a b : ℝ) :
    coprimePrimeReciprocalLogInterval N a b =
      primeReciprocalLogInterval N a b - badPrimeReciprocalLogInterval N a b := by
  classical
  have h := sum_filter_add_sum_filter_not (primeLogIntervalPrimes N a b)
    (fun p => p ∣ N) (fun p => 1 / (p : ℝ))
  change badPrimeReciprocalLogInterval N a b +
    coprimePrimeReciprocalLogInterval N a b = primeReciprocalLogInterval N a b at h
  linarith

theorem badPrimeReciprocalLogInterval_nonneg (N : ℕ) (a b : ℝ) :
    0 ≤ badPrimeReciprocalLogInterval N a b := by
  unfold badPrimeReciprocalLogInterval
  exact sum_nonneg fun p _ => by positivity

theorem badPrimeReciprocalLogInterval_le {N : ℕ} (hN : 2 ≤ N) (a b : ℝ) :
    badPrimeReciprocalLogInterval N a b ≤
      Real.log (N : ℝ) / (Real.log 2 * (N : ℝ) ^ a) := by
  classical
  let S := (primeLogIntervalPrimes N a b).filter (fun p => p ∣ N)
  have hpow : 0 < (N : ℝ) ^ a := Real.rpow_pos_of_pos (by positivity) _
  have hsub : S ⊆ N.primeFactors := by
    intro p hp
    obtain ⟨hp, hd⟩ := mem_filter.mp hp
    exact Nat.mem_primeFactors.mpr ⟨(mem_primeLogIntervalPrimes.mp hp).1, hd, by omega⟩
  have hc : (S.card : ℝ) ≤ Real.log (N : ℝ) / Real.log 2 :=
    (show (S.card : ℝ) ≤ (N.primeFactors.card : ℝ) by
      exact_mod_cast card_le_card hsub).trans (primeFactors_card_cast_le_log hN)
  calc
    badPrimeReciprocalLogInterval N a b ≤ ∑ _p ∈ S, 1 / (N : ℝ) ^ a := by
      apply sum_le_sum
      intro p hp
      exact one_div_le_one_div_of_le hpow
        (mem_primeLogIntervalPrimes.mp (mem_filter.mp hp).1).2.1.le
    _ = (S.card : ℝ) * (1 / (N : ℝ) ^ a) := by simp
    _ ≤ (Real.log (N : ℝ) / Real.log 2) * (1 / (N : ℝ) ^ a) :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    _ = Real.log (N : ℝ) / (Real.log 2 * (N : ℝ) ^ a) := by ring

theorem tendsto_coprimePrimeLossBound {a : ℝ} (ha : 0 < a) :
    Tendsto (fun N : ℕ => Real.log (N : ℝ) / (Real.log 2 * (N : ℝ) ^ a))
      atTop (nhds 0) := by
  have h := ((isLittleO_log_rpow_atTop ha).tendsto_div_nhds_zero.comp
    tendsto_natCast_atTop_atTop).div_const (Real.log 2)
  simpa only [Function.comp_apply, zero_div, div_div, mul_comm] using h

theorem tendsto_badPrimeReciprocalLogInterval {a : ℝ} (ha : 0 < a) (b : ℝ) :
    Tendsto (fun N : ℕ => badPrimeReciprocalLogInterval N a b) atTop (nhds 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (tendsto_coprimePrimeLossBound ha) ?_ ?_
  · exact Eventually.of_forall fun N => badPrimeReciprocalLogInterval_nonneg N a b
  · filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
    exact badPrimeReciprocalLogInterval_le hN a b

theorem tendsto_coprimePrimeReciprocalLogInterval {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    Tendsto (fun N : ℕ => coprimePrimeReciprocalLogInterval N a b)
      atTop (nhds (Real.log (b / a))) := by
  simpa only [coprimePrimeReciprocalLogInterval_eq_sub, sub_zero] using
    (tendsto_primeReciprocalLogInterval ha hab).sub
      (tendsto_badPrimeReciprocalLogInterval ha b)

end MathlibNt.SieveTheory.LiuWeight
