import MathlibNt.SieveTheory.LiLiuGoldbachS1BetaGeometry
import MathlibNt.SieveTheory.LiLiuGoldbachS1MainScale

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- Uniformity in the exponent in MainScale allows a genuine moving root cutoff.
The loss from the effective exponent is paid before selecting the N threshold. -/
theorem goldbachS1_beta_mainMass_mul_product_lower (s ε η : ℝ)
    (hs4 : 4 ≤ s) (_hslt : s < (33 / 8 : ℝ))
    (hε : 0 < ε) (hεu : ε < 1) (hη : 0 < η) (hηu : η < 1 - ε) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → ∀ hEven : Even N,
      (33 / 2 : ℝ) * Real.exp (-Real.eulerMascheroniConstant) * (1 - ε - η) *
        SingularSeries.liuSingularSeries N * (N : ℝ) / Real.log (N : ℝ) ^ 2 ≤
      (goldbachS1BoundingSieve N hEven ε (S1BetaGeometryZeta N s)).totalMass *
        AnalyticNumberTheory.Sieve.sieveProductPrimeFactors
          (goldbachS1BoundingSieve N hEven ε (S1BetaGeometryZeta N s)) := by
  let τ : ℝ := η / 2
  let t : ℝ := (4 / 33 : ℝ) * η / 2
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hτu : τ < 1 - ε := by dsimp [τ]; linarith
  have ht : 0 < t := by dsimp [t]; positivity
  have hs : 0 < s := by linarith
  obtain ⟨Nm, hNm, hm⟩ := goldbachS1_mainMass_mul_product_lower ε τ hε hεu hτ hτu
  obtain ⟨Ng, _hNg, hg⟩ := S1BetaGeometry_zeta_le_rpow_eventually s t hs4 ht
  refine ⟨max Nm Ng, hNm.trans (le_max_left _ _), ?_⟩
  intro N hN hEven
  have hNm' : Nm ≤ N := (le_max_left _ _).trans hN
  have hNg' : Ng ≤ N := (le_max_right _ _).trans hN
  have hN4 := hNm.trans hNm'
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hz1 : 1 < S1BetaGeometryZeta N s :=
    S1BetaGeometry_one_lt_zeta (S1BetaGeometry_two_le_D (by omega) hs) hs
  have hzpos : 0 < S1BetaGeometryZeta N s := by linarith
  let α : ℝ := Real.log (S1BetaGeometryZeta N s) / Real.log (N : ℝ)
  have hlower := Real.log_le_log (Real.rpow_pos_of_pos hNpos (4 / 33 : ℝ))
    (S1BetaGeometry_rpow_le_zeta (N := N) hs)
  rw [Real.log_rpow hNpos] at hlower
  have hαlower : (4 / 33 : ℝ) ≤ α := (le_div_iff₀ hlog).mpr hlower
  have hupper := Real.log_le_log hzpos (hg N hNg')
  rw [Real.log_rpow hNpos] at hupper
  have hαupper : α ≤ (4 / 33 : ℝ) + t := (div_le_iff₀ hlog).mpr hupper
  have hαpos : 0 < α := lt_of_lt_of_le (by norm_num) hαlower
  have hαmin : (1 / 18 : ℝ) ≤ α := (by norm_num : (1 / 18 : ℝ) ≤ 4 / 33).trans hαlower
  have hcancel : Real.log (N : ℝ) * α = Real.log (S1BetaGeometryZeta N s) := by
    dsimp [α]
    field_simp [hlog.ne']
  have hpow : (N : ℝ) ^ α = S1BetaGeometryZeta N s := by
    rw [Real.rpow_def_of_pos hNpos, hcancel, Real.exp_log hzpos]
  have hbase := hm N hNm' hEven α hαmin
  rw [hpow] at hbase
  have ha : 0 ≤ 1 - ε - η := by linarith
  have hcross : (1 - ε - η) * α ≤ (1 - ε - τ) * (4 / 33 : ℝ) := by
    calc
      _ ≤ (1 - ε - η) * ((4 / 33 : ℝ) + t) := mul_le_mul_of_nonneg_left hαupper ha
      _ ≤ (1 - ε - τ) * (4 / 33 : ℝ) := by
        dsimp [τ, t]
        nlinarith [mul_nonneg hε.le hη.le, sq_nonneg η]
  have hdiv : (1 - ε - η) / (4 / 33 : ℝ) ≤ (1 - ε - τ) / α :=
    (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 4 / 33) hαpos).mpr hcross
  have hc := mul_le_mul_of_nonneg_left hdiv
    (by positivity : 0 ≤ 2 * Real.exp (-Real.eulerMascheroniConstant))
  have hcoef : (33 / 2 : ℝ) * Real.exp (-Real.eulerMascheroniConstant) * (1 - ε - η) ≤
      (2 * Real.exp (-Real.eulerMascheroniConstant) / α) * (1 - ε - τ) := by
    calc
      _ = (2 * Real.exp (-Real.eulerMascheroniConstant)) *
          ((1 - ε - η) / (4 / 33 : ℝ)) := by ring
      _ ≤ (2 * Real.exp (-Real.eulerMascheroniConstant)) * ((1 - ε - τ) / α) := hc
      _ = (2 * Real.exp (-Real.eulerMascheroniConstant) / α) * (1 - ε - τ) := by ring
  have hscaled := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcoef (SingularSeries.liuSingularSeries_pos N).le)
      hNpos.le) (sq_nonneg (Real.log (N : ℝ)))
  exact hscaled.trans hbase

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig