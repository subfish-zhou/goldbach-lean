import MathlibNt.SieveTheory.LiLiuGoldbachBasicToSieve

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- Above the cube boundary the literal S4 pair carrier is empty, including
its closed endpoint: equality would force a specified prime to divide N. -/
theorem goldbachS4Pairs_eq_empty_of_cube_bound (N : ℕ) (u : ℝ)
    (hu : 0 ≤ u) (hcut : (N : ℝ) ≤ u ^ 3) :
    goldbachS4Pairs N u = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro rs hrs
  rcases Finset.mem_filter.mp hrs with ⟨_, hr, hs, hcop, hur, hrs, hprod⟩
  have hrsR : (rs.1 : ℝ) ≤ (rs.2 : ℝ) := by exact_mod_cast hrs
  have hrCube : (rs.1 : ℝ) ^ 3 ≤ N := by
    calc
      (rs.1 : ℝ) ^ 3 = (rs.1 : ℝ) * (rs.1 : ℝ) ^ 2 := by ring
      _ ≤ (rs.1 : ℝ) * (rs.2 : ℝ) ^ 2 := by gcongr
      _ ≤ N := by exact_mod_cast hprod
  have hNcube : (N : ℝ) ≤ (rs.1 : ℝ) ^ 3 :=
    hcut.trans (by gcongr)
  have hEq : N = rs.1 ^ 3 := by exact_mod_cast le_antisymm hNcube hrCube
  have hrN : rs.1 ∣ N := by
    rw [hEq]
    exact ⟨rs.1 ^ 2, by ring⟩
  exact (prime_not_dvd_of_coprime hcop hr (dvd_mul_right rs.1 rs.2)) hrN

/-- The actual S4 count vanishes at the real cube-root cutoff. -/
theorem goldbachS4_cube_cutoff_eq_zero (A : Finset ℕ) (N : ℕ) :
    goldbachS4 A N ((N : ℝ) ^ ((1 : ℝ) / 3)) = 0 := by
  have hc : ((N : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 = N := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ N)]
    norm_num
  unfold goldbachS4
  rw [goldbachS4Pairs_eq_empty_of_cube_bound N _
    (Real.rpow_nonneg (by positivity) _) hc.ge]
  exact Finset.sum_empty

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig