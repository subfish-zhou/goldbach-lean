import MathlibNt.SieveTheory.Distribution.LiuPan.LiuPanPrincipalPNT
import MathlibNt.AnalyticNumberTheory.LargeSieve.PanQuotientBounds

/-! Uniform elementary quotient transport through PanQuotientBounds;
no nonprincipal-character theorem is consumed. -/
namespace AnalyticNumberTheory.LargeSieve.PanPrincipal
open Filter MathlibNt.SieveTheory.LiuWeight
open scoped Topology
noncomputable section

private theorem eventually_nat_div_quarter :
    ∀ᶠ N : ℕ in atTop, ∀ a : ℕ, 1 ≤ a →
      (a : ℝ) ≤ (N : ℝ) ^ (2 / 3 : ℝ) →
      (N : ℝ) ^ (1 / 4 : ℝ) ≤ (N / a : ℕ) := by
  exact PanQuotientBounds.eventually_nat_div_quarter

private theorem eventually_quotient_parameters (b : ℝ) (M : ℕ) :
    ∀ᶠ N : ℕ in atTop, ∀ a : ℕ, 1 ≤ a →
      (a : ℝ) ≤ (N : ℝ) ^ (2 / 3 : ℝ) →
      M ≤ N / a ∧ 0 < Real.log (N : ℝ) ∧
      0 < Real.log (N / a : ℕ) ∧
      Real.log (N : ℝ) ≤ 4 * Real.log (N / a : ℕ) ∧
      (4 : ℝ) ^ b ≤ Real.log (N / a : ℕ) := by
  exact PanQuotientBounds.eventually_quotient_parameters b M

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
  have hsaving : Real.log (N : ℝ) ^ s ≤
      (4 : ℝ) ^ s * Real.log (N / a : ℕ) ^ s := by
    calc
      _ ≤ (4 * Real.log (N / a : ℕ)) ^ s := Real.rpow_le_rpow hLN.le hlogs hs.le
      _ = _ := Real.mul_rpow (by norm_num) hLt.le
  have ha0 : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by omega)
  have hupper : (N / a : ℕ) * (a : ℝ) ≤ N := by
    exact_mod_cast Nat.div_mul_le_self N a
  have hdenN := Real.rpow_pos_of_pos hLN s
  have hdent := Real.rpow_pos_of_pos hLt s
  refine hS.trans ?_
  apply (le_div_iff₀ ha0).2
  apply (le_div_iff₀ hdenN).2
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div]
  apply (div_le_iff₀ hdent).2
  calc
    _ ≤ J * ((N / a : ℕ) * (a : ℝ)) *
        ((4 : ℝ) ^ s * Real.log (N / a : ℕ) ^ s) := by
      have h := mul_le_mul_of_nonneg_left hsaving
        (show 0 ≤ J * ((N / a : ℕ) * (a : ℝ)) by positivity)
      simpa only [mul_assoc] using h
    _ ≤ J * (N : ℝ) * ((4 : ℝ) ^ s * Real.log (N / a : ℕ) ^ s) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hupper hJ.le) (by positivity)
    _ = _ := by ring

end
end AnalyticNumberTheory.LargeSieve.PanPrincipal