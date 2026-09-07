import MathlibNt.SieveTheory.LiLiuGoldbachB10KernelUpper
import MathlibNt.SieveTheory.LiLiuGoldbachB10LogMass

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

theorem goldbachB10MainLogProductSum_eq_actualTriangleMass (N : ℕ) :
    goldbachB10MainLogProductSum N ((N : ℝ) ^ goldbachB10Beta) ((N : ℝ) ^ goldbachB10Gamma) =
      goldbachB10ActualTriangleMass N := by
  rw [goldbachB10MainLogProductSum_eq_pair_sum]
  rfl

theorem goldbachB10I10_nonneg : 0 ≤ goldbachB10I10 := by
  by_contra h
  have hi : goldbachB10I10 < 0 := lt_of_not_ge h
  obtain ⟨N, hN, hw⟩ := goldbachB10ActualTriangleMass_le_I10_eventually
    (show 0 < -goldbachB10I10 / 2 by linarith)
  have hp := goldbachB10MainLogProductSum_nonneg (b := (N : ℝ) ^ goldbachB10Beta) hN
    (show goldbachB10Gamma < (1 : ℝ) / 3 by norm_num [goldbachB10Gamma])
  rw [goldbachB10MainLogProductSum_eq_actualTriangleMass] at hp
  have hb := hw N le_rfl
  linarith

/-- The actual floor Li mass has the printed double integral as a one-sided main term. -/
theorem goldbachB10MainMass_le_I10_eventually (ε η : ℝ)
    (hε : 0 < ε) (hεlt : ε < 1) (hη : 0 < η) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      goldbachB10MainMass N ε ((N : ℝ) ^ goldbachB10Beta) ((N : ℝ) ^ goldbachB10Gamma) ≤
        ((1 - ε) * goldbachB10I10 + η) * ((N : ℝ) / Real.log (N : ℝ)) := by
  let e : ℝ := min 1 (η / (goldbachB10I10 + 3))
  have hi := goldbachB10I10_nonneg
  have he : 0 < e := lt_min zero_lt_one (by positivity)
  have he1 : e ≤ 1 := min_le_left _ _
  have heη : e * (goldbachB10I10 + 3) ≤ η :=
    (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
  obtain ⟨Nm, hNm, hm⟩ := goldbachB10MainMass_le_logProductSum ε goldbachB10Gamma e e
    hε hεlt (by norm_num [goldbachB10Gamma]) he he
  obtain ⟨Nk, _hNk, hk⟩ := goldbachB10ActualTriangleMass_le_I10_eventually he
  refine ⟨max Nm Nk, hNm.trans (le_max_left _ _), ?_⟩
  intro N hN
  have hNm' := (le_max_left Nm Nk).trans hN
  have hN2 := hNm.trans hNm'
  have hscale : 0 ≤ (N : ℝ) / Real.log (N : ℝ) := by
    apply div_nonneg (by positivity) (Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega)))
  have hmN := hm N hNm' goldbachB10Beta (by norm_num [goldbachB10Beta])
  have hkN := hk N ((le_max_right Nm Nk).trans hN)
  rw [goldbachB10MainLogProductSum_eq_actualTriangleMass] at hmN
  have hesq : e ^ 2 ≤ e := by nlinarith [mul_le_mul_of_nonneg_left he1 he.le]
  have hcoef : (1 - ε + e) * (goldbachB10I10 + e) + e ≤ (1 - ε) * goldbachB10I10 + η := by
    nlinarith [mul_nonneg hε.le he.le]
  calc
    _ ≤ ((1 - ε + e) * goldbachB10ActualTriangleMass N + e) * ((N : ℝ) / Real.log (N : ℝ)) := hmN
    _ ≤ ((1 - ε + e) * (goldbachB10I10 + e) + e) * ((N : ℝ) / Real.log (N : ℝ)) :=
      mul_le_mul_of_nonneg_right (add_le_add
        (mul_le_mul_of_nonneg_left hkN (by positivity)) le_rfl) hscale
    _ ≤ _ := mul_le_mul_of_nonneg_right hcoef hscale

/-- Actual B10 count at a legal chosen cutoff, bounded by the printed integral.
This theorem does not assume or certify any decimal approximation to the integral. -/
theorem goldbachB10SiftedCount_I10_upper (δ : ℝ) (hδ : 0 < δ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
        let Δ := (N : ℝ) ^ ((1 : ℝ) / 2) / Real.log (N : ℝ) ^ (B + 1)
        let Z := Δ ^ ((1 : ℝ) / 2)
        (goldbachB10SiftedCount N ε ((N : ℝ) ^ goldbachB10Beta) ((N : ℝ) ^ goldbachB10Gamma) Z : ℝ) ≤
          (8 * (1 - ε) * goldbachB10I10 + δ) *
            (MathlibNt.SieveTheory.SingularSeries.liuSingularSeries N * (N : ℝ) / Real.log (N : ℝ) ^ 2) := by
  let e : ℝ := min 1 (δ / (goldbachB10I10 + 10))
  have hi := goldbachB10I10_nonneg
  have he : 0 < e := lt_min zero_lt_one (by positivity)
  have he1 : e ≤ 1 := min_le_left _ _
  have heδ : e * (goldbachB10I10 + 10) ≤ δ :=
    (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
  obtain ⟨B, hB, hu⟩ := goldbachB10SiftedCount_kernel_upper e he
  obtain ⟨Nk, _hNk, hk⟩ := goldbachB10ActualTriangleMass_le_I10_eventually he
  refine ⟨B, hB, ?_⟩
  intro ε hε hεlt
  obtain ⟨Nu, hNu, hu'⟩ := hu ε goldbachB10Gamma hε hεlt (by norm_num [goldbachB10Gamma])
  refine ⟨max Nu Nk, hNu.trans (le_max_left _ _), ?_⟩
  intro N hN hEven
  have hNu' := (le_max_left Nu Nk).trans hN
  have hscale : 0 ≤ MathlibNt.SieveTheory.SingularSeries.liuSingularSeries N * (N : ℝ) /
      Real.log (N : ℝ) ^ 2 := by
    have hi := (MathlibNt.SieveTheory.SingularSeries.liuSingularSeries_pos N).le
    positivity
  have huN := hu' N hNu' hEven goldbachB10Beta (by norm_num [goldbachB10Beta])
  rw [goldbachB10MainLogProductSum_eq_actualTriangleMass] at huN
  have hkN := hk N ((le_max_right Nu Nk).trans hN)
  have hesq : e ^ 2 ≤ e := by nlinarith [mul_le_mul_of_nonneg_left he1 he.le]
  have hc : (8 * (1 - ε) + e) * (goldbachB10I10 + e) + e ≤
      8 * (1 - ε) * goldbachB10I10 + δ := by
    nlinarith [mul_nonneg hε.le he.le]
  refine huN.trans (mul_le_mul_of_nonneg_right ?_ hscale)
  exact (add_le_add (mul_le_mul_of_nonneg_left hkN (by positivity)) le_rfl).trans hc

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig