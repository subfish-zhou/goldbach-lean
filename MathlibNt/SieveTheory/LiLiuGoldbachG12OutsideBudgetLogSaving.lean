import MathlibNt.SieveTheory.LiLiuGoldbachG12OutsideBudgetTransport

noncomputable section
open Classical Finset Filter
open scoped BigOperators Topology
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
open MathlibNt.SieveTheory.LiLiuPrereqWF

namespace G12OutsideBudget

/-- A fixed positive power absorbs the entire numerical transport constant. -/
theorem scalar_log_saving (B : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n : ℝ in atTop, 2 ≤ n ∧
      80 * (1 + Real.log n)^2 / n^δ ≤ 1 / (Real.log n)^B := by
  have h := (isLittleO_log_rpow_rpow_atTop (B+2 : ℕ) hδ).bound
    (by norm_num : (0 : ℝ) < 1/320)
  filter_upwards [h, eventually_ge_atTop (max 2 (Real.exp 1))] with n hn hn0
  have hn2 : 2 ≤ n := (le_max_left _ _).trans hn0
  have hnpos : 0 < n := by linarith
  have hl1 : 1 ≤ Real.log n :=
    (Real.le_log_iff_exp_le hnpos).mpr ((le_max_right _ _).trans hn0)
  have hlpos : 0 < Real.log n := by linarith
  have hb : (Real.log n)^(B+2) ≤ (1/320 : ℝ)*n^δ := by
    simpa only [Real.norm_eq_abs, Real.rpow_natCast,
      abs_of_nonneg (pow_nonneg hlpos.le _),
      abs_of_nonneg (Real.rpow_nonneg hnpos.le _)] using hn
  refine ⟨hn2,?_⟩
  apply (div_le_iff₀ (Real.rpow_pos_of_pos hnpos δ)).mpr
  rw [show 1 / (Real.log n)^B * n^δ = n^δ / (Real.log n)^B by ring]
  apply (le_div_iff₀ (pow_pos hlpos B)).mpr
  have hs : (1 + Real.log n)^2 ≤ 4 * (Real.log n)^2 := by nlinarith
  have hm := mul_le_mul_of_nonneg_right hs (pow_nonneg hlpos.le B)
  rw [pow_add] at hb
  calc
    (80 * (1 + Real.log n)^2) * (Real.log n)^B ≤
        320 * ((Real.log n)^B * (Real.log n)^2) := by nlinarith
    _ ≤ n^δ := by linarith

/-- The external denominator has a fixed positive power at every Q >= N^sigma. -/
theorem denominator_lower {n Q η σ : ℝ} (hn : 0 ≤ n) (hη : 0 < η)
    (hηsmall : η < 1/8) (hQ : n^σ ≤ Q) :
    n^(σ*((1+η+η^9)⁻¹*η^2)) ≤ (externalInternalLevel Q η)^(η^2) := by
  have hc : 0 < 1+η+η^9 := by linarith [(external_dilation_bounds hη hηsmall).1]
  have h := Real.rpow_le_rpow (Real.rpow_nonneg hn _) hQ
    (mul_nonneg (inv_nonneg.mpr hc.le) (sq_nonneg η))
  rw [← Real.rpow_mul hn] at h
  have hQ0 : 0 ≤ Q := (Real.rpow_nonneg hn _).trans hQ
  simpa only [externalInternalLevel, ← Real.rpow_mul hQ0] using h


end G12OutsideBudget
