module

public import MathlibNt.AnalyticNumberTheory.LargeSieve.PanWangDingLowPrimePrefix
public import MathlibNt.AnalyticNumberTheory.LargeSieve.PanQuotientBounds

/-! Uniform transport to the natural quotient in Pan's low-conductor endpoint. -/
@[expose] public section

namespace AnalyticNumberTheory.LargeSieve.PanLow
open Filter
open scoped Topology
open PanQuotientBounds
noncomputable section

/-- The constants and cutoff are chosen before every `a`, modulus and character.
The endpoint is the literal natural quotient; the carrier is the real `N^(2/3)` range. -/
theorem primePrefix_siegelWalfisz_nat_div (b s : ℝ) (hb : 0 ≤ b) (hs : 0 < s) :
    ∃ K : ℝ, 0 < K ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ a : ℕ, 1 ≤ a → (a : ℝ) ≤ (N : ℝ) ^ (2 / 3 : ℝ) →
      ∀ q : ℕ, 2 ≤ q → (q : ℝ) ≤ Real.log (N : ℝ) ^ b →
      ∀ χ : PrimitiveCharacter q, χ.1 ≠ 1 →
        ‖primePrefix χ.1 (N / a)‖ ≤
          (K * (N : ℝ) / Real.log (N : ℝ) ^ s) / (a : ℝ) := by
  obtain ⟨J, hJ, M, hSW⟩ := primePrefix_siegelWalfisz_endpoint (b + 1) s
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (eventually_quotient_parameters b M)
  refine ⟨J * (4 : ℝ) ^ s, by positivity, N₀, ?_⟩
  intro N hN a ha haN q hq hqb χ hχ
  obtain ⟨hM, hLN, hLt, hlogs, hpay⟩ := hN₀ N hN a ha haN
  have hconductor := log_rpow_le_quotient_log_rpow_succ hLN.le hLt
    (by norm_num) hb hlogs hpay
  have hS := hSW (N / a) hM q hq (hqb.trans hconductor) χ hχ
  have hsize : (↑(N / a : ℕ) : ℝ) * a ≤ N := by
    exact_mod_cast Nat.div_mul_le_self N a
  exact hS.trans (by
    simpa only [mul_assoc] using
      div_log_rpow_le_of_quotient (by omega : 0 < a) hJ.le
        (by norm_num : (0 : ℝ) < 4) hs.le hLN hLt hlogs hsize)

end
end AnalyticNumberTheory.LargeSieve.PanLow
