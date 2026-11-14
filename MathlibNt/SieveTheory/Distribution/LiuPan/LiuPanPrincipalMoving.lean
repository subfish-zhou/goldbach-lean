module

public import MathlibNt.SieveTheory.Distribution.LiuPan.LiuPanPrincipalPNT
public import MathlibNt.AnalyticNumberTheory.LargeSieve.PanQuotientBounds

/-! Uniform elementary quotient transport through PanQuotientBounds;
no nonprincipal-character theorem is consumed. -/
@[expose] public section

namespace AnalyticNumberTheory.LargeSieve.PanPrincipal
open Filter MathlibNt.SieveTheory.LiuWeight
open scoped Topology
open PanQuotientBounds
noncomputable section

/-- Uniform PNT at the literal real quotient. The threshold precedes every a.
The proof uses only the q=1 Standard BV extraction above, never nonprincipal SW. -/
theorem primeCount_li_moving_prefix (s : ℝ) (hs : 0 < s) :
    ∃ K : ℝ, 0 < K ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ a : ℕ, 1 ≤ a → (a : ℝ) ≤ (N : ℝ) ^ (2 / 3 : ℝ) →
        |primeCount (N / a) - liuLogarithmicIntegral (2 / Real.log 2) ((N : ℝ) / a)| ≤
          (K * (N : ℝ) / Real.log (N : ℝ) ^ s) / (a : ℝ) := by
  obtain ⟨J, hJ, M, hPNT⟩ := primeCount_li_real_div_pnt s hs
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (eventually_quotient_parameters 0 M)
  refine ⟨J * (4 : ℝ) ^ s, by positivity, N₀, ?_⟩
  intro N hN a ha haN
  obtain ⟨hM, hLN, hLt, hlogs, _hpay⟩ := hN₀ N hN a ha haN
  have hS := hPNT N a (by omega) hM
  have hsize : (↑(N / a : ℕ) : ℝ) * a ≤ N := by
    exact_mod_cast Nat.div_mul_le_self N a
  exact hS.trans (by
    simpa only [mul_assoc] using
      div_log_rpow_le_of_quotient (by omega : 0 < a) hJ.le
        (by norm_num : (0 : ℝ) < 4) hs.le hLN hLt hlogs hsize)

end
end AnalyticNumberTheory.LargeSieve.PanPrincipal
