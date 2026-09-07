import MathlibNt.SieveTheory.LiLiuGoldbachB10IntegralScalar

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- Actual B10SiftedCount at the unchanged legal cutoff, retaining (1-ε).
This statement concerns neither an original G10 count nor a corrected G10 count. -/
theorem goldbachB10SiftedCount_540996_upper (δ : ℝ) (hδ : 0 < δ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
        let Δ := (N : ℝ) ^ ((1 : ℝ) / 2) / Real.log (N : ℝ) ^ (B + 1)
        let Z := Δ ^ ((1 : ℝ) / 2)
        (goldbachB10SiftedCount N ε ((N : ℝ) ^ goldbachB10Beta) ((N : ℝ) ^ goldbachB10Gamma) Z : ℝ) ≤
          ((540996/100000 : ℝ) * (1 - ε) + δ) *
            (MathlibNt.SieveTheory.SingularSeries.liuSingularSeries N * (N : ℝ) / Real.log (N : ℝ) ^ 2) := by
  obtain ⟨B, hB, hu⟩ := goldbachB10SiftedCount_I10_upper δ hδ
  refine ⟨B, hB, ?_⟩
  intro ε hε hεlt
  obtain ⟨N₀, hN₀, hcount⟩ := hu ε hε hεlt
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN hEven
  have hscale : 0 ≤ MathlibNt.SieveTheory.SingularSeries.liuSingularSeries N * (N : ℝ) /
      Real.log (N : ℝ)^2 :=
    div_nonneg (mul_nonneg (MathlibNt.SieveTheory.SingularSeries.liuSingularSeries_pos N).le
      (Nat.cast_nonneg N)) (sq_nonneg _)
  have hcoef : 8*(1-ε)*goldbachB10I10 ≤ (540996/100000 : ℝ)*(1-ε) := by
    have h := mul_le_mul_of_nonneg_right goldbachB10I10_eight_mul_le_540996
      (show 0 ≤ 1-ε by linarith)
    nlinarith
  exact (hcount N hN hEven).trans
    (mul_le_mul_of_nonneg_right (add_le_add hcoef (le_refl δ)) hscale)

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig