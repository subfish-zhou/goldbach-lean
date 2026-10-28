import MathlibNt.SieveTheory.LiLiuGoldbachB10NormalizedUpper
import MathlibNt.SieveTheory.LiLiuGoldbachB10MainLogSum
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


end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig