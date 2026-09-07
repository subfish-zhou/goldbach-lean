import MathlibNt.SieveTheory.LiLiuGoldbachB10Congruence

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- The actual product support of C10, with no fixed gap imposed below gamma=1/3. -/
theorem goldbachC10Prod_le_rpow_half_and_lt_two_thirds
    {N : ℕ} {b γ : ℝ} {rs : ℕ × ℕ}
    (hN : 2 ≤ N) (hγ : γ < (1 : ℝ) / 3)
    (hrs : rs ∈ goldbachC10Pairs N b ((N : ℝ) ^ γ)) :
    (goldbachC10Prod rs : ℝ) ≤ (N : ℝ) ^ ((1 + γ) / 2) ∧
      (N : ℝ) ^ ((1 + γ) / 2) < (N : ℝ) ^ ((2 : ℝ) / 3) := by
  rcases mem_goldbachC10Pairs_iff.mp hrs with ⟨_, _, _, _, hrc, _, hprod⟩
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hN0 : (0 : ℝ) < N := by linarith
  have hprodR : (rs.1 : ℝ) * (rs.2 : ℝ) ^ 2 ≤ N := by exact_mod_cast hprod
  have hsq : (goldbachC10Prod rs : ℝ) ^ 2 ≤ (N : ℝ) * (N : ℝ) ^ γ := by
    calc
      (goldbachC10Prod rs : ℝ) ^ 2 =
          (rs.1 : ℝ) * ((rs.1 : ℝ) * (rs.2 : ℝ) ^ 2) := by
        simp only [goldbachC10Prod, Nat.cast_mul]
        ring
      _ ≤ (N : ℝ) ^ γ * N :=
        mul_le_mul hrc hprodR (by positivity) (by positivity)
      _ = _ := by ring
  have hpower : ((N : ℝ) ^ ((1 + γ) / 2)) ^ 2 = (N : ℝ) * (N : ℝ) ^ γ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
    norm_num only [Nat.cast_ofNat]
    rw [show (1 + γ) / 2 * (2 : ℝ) = 1 + γ by ring,
      Real.rpow_add hN0, Real.rpow_one]
  constructor
  · have hp : 0 ≤ (N : ℝ) ^ ((1 + γ) / 2) := Real.rpow_nonneg hN0.le _
    have hm : 0 ≤ (goldbachC10Prod rs : ℝ) := by positivity
    nlinarith
  · exact Real.rpow_lt_rpow_of_exponent_lt hN1 (by linarith)

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig