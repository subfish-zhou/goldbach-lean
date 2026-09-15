import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryExtractedScale

noncomputable section
namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

theorem wAnalytic_phase_budget_kscale
    {v : WGCDData} {q r N₁ N₂ : ℕ} (hv : v.Valid q r N₁ N₂)
    {Cscale M T x u : ℝ} (hC : 1 ≤ Cscale) (hM : 0 ≤ M) (hT : 0 < T)
    (hNT : T ≤ (N₁ : ℝ)) (hx : x = 4 * M * T) {a : ℤ}
    (ha : |(a : ℝ)| ≤ Cscale*x) (hu : |u| ≤ 3 * M) (h : ℤ) :
    |(h : ℝ)| * (|u| / (v.D * v.k₁ * v.k₂ : ℕ) +
      |(a : ℝ)| / (v.n₁ * v.k₁ * v.k₂ * v.D' : ℕ)) ≤
        (3+4*Cscale) * M * |(h : ℝ)| / (q.lcm r : ℝ) := by
  have hN₁ : (0 : ℝ) < N₁ := hT.trans_le hNT
  have hl : (0 : ℝ) < q.lcm r := by
    rw [hv.lcm_eq]
    exact_mod_cast Nat.mul_pos (Nat.mul_pos hv.D_pos hv.k₁_pos) hv.k₂_pos
  have ha' : |(a : ℝ)| ≤ 4 * Cscale * M * (N₁ : ℝ) :=
    by
    calc
      _ ≤ Cscale*x := ha
      _ = 4*Cscale*M*T := by rw [hx]; ring
      _ ≤ 4*Cscale*M*(N₁ : ℝ) := mul_le_mul_of_nonneg_left hNT (by positivity)
  rw [hv.slow_denominator, ← hv.lcm_eq, Nat.cast_mul]
  have hb : |(a : ℝ)| / ((N₁ : ℝ) * (q.lcm r : ℝ)) ≤
      4 * Cscale * M / (q.lcm r : ℝ) := by
    apply (div_le_div_iff₀ (mul_pos hN₁ hl) hl).mpr
    nlinarith [mul_le_mul_of_nonneg_right ha' hl.le]
  have hb' := add_le_add (div_le_div_of_nonneg_right hu hl.le) hb
  calc
    _ ≤ |(h : ℝ)| * (3 * M / (q.lcm r : ℝ) + 4 * Cscale * M / (q.lcm r : ℝ)) :=
      mul_le_mul_of_nonneg_left hb' (abs_nonneg _)
    _ = _ := by ring


end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
