module

public import MathlibNt.AnalyticNumberTheory.LargeSieve.PanQuotientBounds
public import MathlibNt.AnalyticNumberTheory.LargeSieve.PanWangDingLowMovingPrefix

/-! Preserve the frozen SW prefix maximum when transporting to `N / a`.
No new Siegel--Walfisz input is assumed. -/

@[expose] public section

namespace Wu2004MeanValue
open Filter Finset
open AnalyticNumberTheory.LargeSieve
open AnalyticNumberTheory.LargeSieve.PanLow
open scoped Topology
open PanQuotientBounds
noncomputable section

/-- Real logarithmic exponents, with every prefix below the common scale.
The constants precede the modulus, character, and independently chosen prefix. -/
theorem low_primePrefix_max (b s : ℝ) :
    ∃ J : ℝ, 0 < J ∧ ∃ M : ℕ, ∀ N ≥ M,
      ∀ q : ℕ, 2 ≤ q → (q : ℝ) ≤ Real.log (N : ℝ) ^ b →
      ∀ χ : PrimitiveCharacter q, ∀ y ≤ N,
        ‖primePrefix χ.1 y‖ ≤ J * (N : ℝ) / Real.log (N : ℝ) ^ s := by
  obtain ⟨J, hJ, M, hSW⟩ := primePrefix_siegelWalfisz_real_exponents b s
  exact ⟨J, hJ, M, fun N hN q hq hqb χ =>
    hSW N hN q hq hqb χ (primitiveCharacter_ne_one_of_two_le hq χ)⟩

/-- The genuine maximal quotient estimate: `y` need not equal `N / a`.
It can subsequently be chosen separately for every modulus, character and `a`. -/
theorem low_primePrefix_nat_div_max (b s : ℝ) (hb : 0 ≤ b) (hs : 0 < s) :
    ∃ J : ℝ, 0 < J ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ a : ℕ, 1 ≤ a → (a : ℝ) ≤ (N : ℝ) ^ (2 / 3 : ℝ) →
      ∀ q : ℕ, 2 ≤ q → (q : ℝ) ≤ Real.log (N : ℝ) ^ b →
      ∀ χ : PrimitiveCharacter q, ∀ y ≤ N / a,
        ‖primePrefix χ.1 y‖ ≤
          (J * (N : ℝ) / Real.log (N : ℝ) ^ s) / (a : ℝ) := by
  obtain ⟨J, hJ, M, hSW⟩ := low_primePrefix_max (b + 1) s
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (eventually_quotient_parameters b M)
  refine ⟨J * (4 : ℝ) ^ s, by positivity, N₀, ?_⟩
  intro N hN a ha haN q hq hqb χ y hy
  obtain ⟨hM, hLN, hLt, hlogs, hpay⟩ := hN₀ N hN a ha haN
  have hconductor := log_rpow_le_quotient_log_rpow_succ hLN.le hLt
    (by norm_num) hb hlogs hpay
  have hS := hSW (N / a) hM q hq (hqb.trans hconductor) χ y hy
  have hsize : (↑(N / a : ℕ) : ℝ) * a ≤ N := by
    exact_mod_cast Nat.div_mul_le_self N a
  exact hS.trans (by
    simpa only [mul_assoc] using
      div_log_rpow_le_of_quotient (by omega : 0 < a) hJ.le
        (by norm_num : (0 : ℝ) < 4) hs.le hLN hLt hlogs hsize)

end
end Wu2004MeanValue
