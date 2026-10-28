import MathlibNt.SieveTheory.LiLiuGoldbachG12AuthorWeightedSource
import MathlibNt.SieveTheory.LiLiuGoldbachG12PrimeKernelIntegralBound
import MathlibNt.SieveTheory.LiLiuGoldbachG12BuchstabMajorant


open scoped Topology
open Filter
noncomputable section
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- The normalized exceptional divisor mass vanishes independently of epsilon. -/
theorem goldbachG12AuthorBad_normalized_paid (δ : ℝ) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N ≥ N₀,
      Real.log (N : ℝ)/N * (67200*N/(N : ℝ)^(4/53 : ℝ)) ≤ δ := by
  have ht : Tendsto (fun N : ℕ => (67200 : ℝ) *
      (Real.log (N : ℝ)/(N : ℝ)^(4/53 : ℝ))) atTop (𝓝 0) := by
    have hbase : Tendsto (fun x : ℝ => Real.log x / x ^ (4/53 : ℝ)) atTop (𝓝 0) :=
      (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 4/53)).tendsto_div_nhds_zero
    have h := (hbase.comp (tendsto_natCast_atTop_atTop :
      Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop)).const_mul (67200 : ℝ)
    simpa only [mul_zero, Function.comp_def] using h
  obtain ⟨K,hK⟩ := eventually_atTop.mp (ht.eventually (gt_mem_nhds hδ))
  refine ⟨max 4 K,le_max_left _ _,?_⟩
  intro N hN
  have hNp : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  calc
    _ = (67200 : ℝ)*(Real.log (N : ℝ)/(N : ℝ)^(4/53 : ℝ)) := by field_simp
    _ ≤ δ := (hK N (by omega)).le


end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
