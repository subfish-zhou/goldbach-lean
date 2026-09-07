import MathlibNt.SieveTheory.LiLiuGoldbachB10NormalizedUpper
import MathlibNt.SieveTheory.LiLiuGoldbachB10MainLogSum

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- Physical join of the normalized sieve and the actual Li-to-kernel mass bound.
Only the actual weighted prime-pair sum remains; no integral limit is assumed. -/
theorem goldbachB10SiftedCount_kernel_upper (δ : ℝ) (hδ : 0 < δ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ ε γ : ℝ, 0 < ε → ε < 1 → γ < (1 : ℝ) / 3 →
      ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
        ∀ β : ℝ, (1 : ℝ) / 18 < β →
        let Δ := (N : ℝ) ^ ((1 : ℝ) / 2) / Real.log (N : ℝ) ^ (B + 1)
        let Z := Δ ^ ((1 : ℝ) / 2)
        let K := goldbachB10MainLogProductSum N ((N : ℝ) ^ β) ((N : ℝ) ^ γ)
        (goldbachB10SiftedCount N ε ((N : ℝ) ^ β) ((N : ℝ) ^ γ) Z : ℝ) ≤
          ((8 * (1 - ε) + δ) * K + δ) *
            (MathlibNt.SieveTheory.SingularSeries.liuSingularSeries N * (N : ℝ) /
              Real.log (N : ℝ) ^ 2) := by
  let ρ : ℝ := min (δ / 10) 1
  have hρ : 0 < ρ := lt_min (by positivity) zero_lt_one
  have hρ1 : ρ ≤ 1 := min_le_right _ _
  have hρδ : 10 * ρ ≤ δ := by have := min_le_left (δ / 10) (1 : ℝ); dsimp [ρ]; linarith
  obtain ⟨B, hB, hn⟩ := goldbachB10SiftedCount_normalized_upper ρ hρ
  refine ⟨B, hB, ?_⟩
  intro ε γ hε hεlt hγ
  obtain ⟨Nn, hNn, hn'⟩ := hn ε γ hε hεlt hγ
  obtain ⟨Nm, _hNm, hm⟩ := goldbachB10MainMass_le_logProductSum ε γ ρ ρ hε hεlt hγ hρ hρ
  refine ⟨max Nn Nm, hNn.trans (le_max_left _ _), ?_⟩
  intro N hN hEven β hβ
  have hNn' : Nn ≤ N := (le_max_left _ _).trans hN
  have hNm' : Nm ≤ N := (le_max_right _ _).trans hN
  have hN4 : 4 ≤ N := hNn.trans hNn'
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  let K := goldbachB10MainLogProductSum N ((N : ℝ) ^ β) ((N : ℝ) ^ γ)
  let X := goldbachB10MainMass N ε ((N : ℝ) ^ β) ((N : ℝ) ^ γ)
  let C := MathlibNt.SieveTheory.SingularSeries.liuSingularSeries N
  let A := C * (N : ℝ) / Real.log (N : ℝ) ^ 2
  have hC : 0 ≤ C := (MathlibNt.SieveTheory.SingularSeries.liuSingularSeries_pos N).le
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hK : 0 ≤ K := goldbachB10MainLogProductSum_nonneg (by omega : 2 ≤ N) hγ
  have hmass := hm N hNm' β hβ
  have hsq : ρ ^ 2 ≤ ρ := by nlinarith [mul_le_mul_of_nonneg_left hρ1 hρ.le]
  have hc : (8 + ρ) * (1 - ε + ρ) ≤ 8 * (1 - ε) + δ := by
    nlinarith [mul_nonneg hε.le hρ.le]
  have he : (8 + ρ) * ρ + ρ ≤ δ := by nlinarith
  have hcoef : (8 + ρ) * ((1 - ε + ρ) * K + ρ) + ρ ≤
      (8 * (1 - ε) + δ) * K + δ := by
    calc
      _ = ((8 + ρ) * (1 - ε + ρ)) * K + ((8 + ρ) * ρ + ρ) := by ring
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_right hc hK) he
  have hmain : (8 + ρ) * C * X / Real.log (N : ℝ) ≤
      (8 + ρ) * ((1 - ε + ρ) * K + ρ) * A := by
    calc
      _ ≤ (8 + ρ) * C * (((1 - ε + ρ) * K + ρ) * ((N : ℝ) / Real.log (N : ℝ))) /
          Real.log (N : ℝ) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hmass (by positivity)) hlog.le
      _ = _ := by dsimp [A]; ring
  have hnorm := hn' N hNn' hEven β hβ
  change _ ≤ ((8 * (1 - ε) + δ) * K + δ) * A
  calc
    _ ≤ (8 + ρ) * C * X / Real.log (N : ℝ) + ρ * A := by
      simpa only [C, X, A, Real.rpow_two, mul_div_assoc, mul_assoc] using hnorm
    _ ≤ (8 + ρ) * ((1 - ε + ρ) * K + ρ) * A + ρ * A := add_le_add hmain le_rfl
    _ = ((8 + ρ) * ((1 - ε + ρ) * K + ρ) + ρ) * A := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hcoef hA

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig