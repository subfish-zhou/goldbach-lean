import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryDirectJoinedTerms
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryDirectNormalizationRoots

noncomputable section
open Classical Finset
namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

/-- The first beta scale is bounded using its own original support member. -/
theorem directPayZero_n_le
    {H : ℕ → ℕ → ℕ} {N Q : Finset ℕ}
    (hN : ∀ n ∈ N, 0 < n) (hQ : ∀ q ∈ Q, 0 < q)
    {a : ℤ} {P : WOriginalTuple → Prop} {R S ξ T : ℝ} {b : ℕ}
    {K : WExtractedKey} {j : Fin 5 → ℕ} {positive : Bool}
    {t : WExtractedTuple × ℤ}
    (ht : t ∈ wAnalyticDyadicBlock
      (wExtractedKeyFiber H N Q a P R S ξ b K) j positive)
    (hNT : ∀ n ∈ N, (n : ℝ) ≤ 2 * T) :
    (2 : ℝ) ^ j 2 ≤ 2 * T :=
  (wAnalyticDyadicBlock_bounds hN hQ ht 2).1.trans
    (direct_outer_n_le hN hQ (mem_filter.mp ht).1 hNT).2

/-- Pure scalar cancellation; hypotheses are the local geometric coordinates. -/
theorem directPayZero_scalar
    {D k r s H n f T x Z R S : ℝ}
    (hD : 1 ≤ D) (hk : 0 < k) (hr : 0 < r) (hs : 0 < s)
    (hH : 0 ≤ H) (_hn : 0 ≤ n) (hf : 0 ≤ f)
    (hT : 0 < T) (hx : 0 < x) (hZ : 0 ≤ Z)
    (hR : 0 ≤ R) (hS : 0 ≤ S)
    (hfreq : H ≤ 32 * (D * k * r * s) * Z * T / x)
    (hnT : n ≤ 2 * T) (hfT : f ≤ 2 * T)
    (hkRS : k ≤ R * S) (hrR : r ≤ R) :
    ((D * k * r * s)⁻¹) ^ 2 * (8 * k * r * T) *
      (k * (r * n * H * f * s)) / (T ^ 2) ^ 2 ≤
      1024 * Z * (R ^ 2 * S / x) := by
  have hD0 : 0 < D := by linarith
  have hbase : ((D * k * r * s)⁻¹) ^ 2 * (8 * k * r * T) *
      (k * (r * n * H * f * s)) / (T ^ 2) ^ 2 ≤
      ((D * k * r * s)⁻¹) ^ 2 * (8 * k * r * T) *
      (k * (r * (2*T) * (32 * (D*k*r*s)*Z*T/x) * (2*T) * s)) /
        (T ^ 2) ^ 2 := by
    gcongr
  have heq : ((D * k * r * s)⁻¹) ^ 2 * (8 * k * r * T) *
      (k * (r * (2*T) * (32 * (D*k*r*s)*Z*T/x) * (2*T) * s)) /
        (T ^ 2) ^ 2 = 1024 * Z * (k * r / (D * x)) := by
    field_simp
    ring
  rw [heq] at hbase
  apply hbase.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply (div_le_div_iff₀ (by positivity) hx).2
  have hkr : k * r ≤ R ^ 2 * S := by
    calc
      k * r ≤ (R*S)*R := mul_le_mul hkRS hrR hr.le (mul_nonneg hR hS)
      _ = _ := by ring
  have hd : R ^ 2 * S ≤ (R ^ 2 * S) * D := le_mul_of_one_le_right (by positivity) hD
  nlinarith [mul_le_mul_of_nonneg_right (hkr.trans hd) hx.le]

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
