import MathlibNt.SieveTheory.LiLiuGoldbachG67PaidLower
import MathlibNt.SieveTheory.LiuSingularSeries

open Filter

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- One extra logarithm absorbs a fixed BV constant into the actual
singular-series-normalized error, uniformly in the ambient integer. -/
theorem goldbachBV_logCube_normalized (C δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop,
      C * (N : ℝ) / Real.log (N : ℝ)^3 ≤
        δ * (SingularSeries.liuSingularSeries N * (N : ℝ) / Real.log (N : ℝ)^2) := by
  have hc := SingularSeries.liuUniversalProduct_pos
  have hl : ∀ᶠ N : ℕ in atTop,
      C / (δ * SingularSeries.liuUniversalProduct) ≤ Real.log (N : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop _)
  filter_upwards [eventually_ge_atTop (4 : ℕ), hl] with N hN hl
  have hn0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hb : C ≤ δ * SingularSeries.liuSingularSeries N * Real.log (N : ℝ) := by
    calc
      C ≤ δ * SingularSeries.liuUniversalProduct * Real.log (N : ℝ) :=
        (div_le_iff₀ (mul_pos hδ hc)).mp hl |>.trans_eq (mul_comm _ _)
      _ ≤ δ * SingularSeries.liuSingularSeries N * Real.log (N : ℝ) := by
        gcongr
        exact SingularSeries.liuUniversalProduct_le_liuSingularSeries N
  calc
    C * (N : ℝ) / Real.log (N : ℝ)^3 ≤
        (δ * SingularSeries.liuSingularSeries N * Real.log (N : ℝ)) *
          (N : ℝ) / Real.log (N : ℝ)^3 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hb hn0) (by positivity)
    _ = δ * (SingularSeries.liuSingularSeries N * (N : ℝ) / Real.log (N : ℝ)^2) := by
      field_simp

/-- Both original positive terms, with arbitrary relative BV error. The
signed finite main sums are retained; no density or integral estimate is assumed. -/
theorem goldbachG67_lowerRosser_normalized :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ δ : ℝ, 0 < δ →
      ∀ ε : ℝ, 0 < ε → ε < 2/15 →
        ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
          (goldbachPairLowerMain N ε B
            (goldbachG6Pairs N ((N : ℝ)^(4/53 : ℝ)) ((N : ℝ)^(4/33 : ℝ))) -
              δ * (SingularSeries.liuSingularSeries N * (N : ℝ) / Real.log (N : ℝ)^2) ≤
            (goldbachWeightG6 (goldbachDifferenceCarrier N ε) N
              ((N : ℝ)^(4/53 : ℝ)) ((N : ℝ)^(4/33 : ℝ)) : ℝ)) ∧
          (goldbachPairLowerMain N ε B
            (goldbachG7Pairs N ((N : ℝ)^(4/53 : ℝ)) ((N : ℝ)^(4/33 : ℝ))
              ((N : ℝ)^(3/11 : ℝ))) -
              δ * (SingularSeries.liuSingularSeries N * (N : ℝ) / Real.log (N : ℝ)^2) ≤
            (goldbachWeightG7 (goldbachDifferenceCarrier N ε) N
              ((N : ℝ)^(4/53 : ℝ)) ((N : ℝ)^(4/33 : ℝ)) ((N : ℝ)^(3/11 : ℝ)) : ℝ)) := by
  obtain ⟨B, hB, C, _, hp⟩ := goldbachG67_lowerRosser_paid 3 (by norm_num)
  refine ⟨B, hB, ?_⟩
  intro δ hδ ε hε hεu
  obtain ⟨Np, hNp, hn⟩ := hp ε hε hεu
  obtain ⟨Ne, he⟩ := eventually_atTop.mp (goldbachBV_logCube_normalized C δ hδ)
  refine ⟨max Np Ne, by omega, ?_⟩
  intro N hN hEven
  obtain ⟨h6, h7⟩ := hn N (by omega) hEven
  have hb := he N (by omega)
  simp only [Real.rpow_ofNat] at h6 h7
  exact ⟨(sub_le_sub_left hb _).trans h6, (sub_le_sub_left hb _).trans h7⟩

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
