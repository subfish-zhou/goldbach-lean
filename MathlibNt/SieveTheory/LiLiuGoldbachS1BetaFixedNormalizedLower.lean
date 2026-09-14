import MathlibNt.SieveTheory.LiLiuGoldbachS1BetaPaidLower
import MathlibNt.SieveTheory.LiLiuGoldbachS1BetaLowerDensity
import MathlibNt.SieveTheory.LiLiuGoldbachS1BetaMainScale
import MathlibNt.SieveTheory.LiLiuGoldbachS1Carrier
import MathlibNt.SieveTheory.LiLiuGoldbachS1MainMass
import MathlibNt.SieveTheory.Arithmetic.LiuLogScaleAbsorption
import MathlibNt.Analysis.SieveNormalization

noncomputable section

open Filter
open MathlibNt.SieveTheory.SwitchingPrinciple

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

set_option autoImplicit false

private theorem S1BetaNormalizedLower_mainConst_pos :
    0 < (33 / 2 : ℝ) * Real.exp (-Real.eulerMascheroniConstant) := by
  positivity

private theorem S1BetaNormalizedLower_goldbachS1_nonneg (N : ℕ) (ε : ℝ) :
    0 ≤
      (goldbachS1 (goldbachDifferenceCarrier N ε) N ((N : ℝ) ^ (4 / 33 : ℝ)) : ℝ) := by
  classical
  unfold goldbachS1 literalH
  exact_mod_cast Nat.zero_le
    ((goldbachDifferenceCarrier N ε).filter
      (literalHPoint N 1 ((N : ℝ) ^ (4 / 33 : ℝ)))).card

private theorem S1BetaNormalizedLower_paidErrorAbsorbEventually
    (C ρ : ℝ) (hρ : 0 < ρ) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      C * (N : ℝ) / Real.log (N : ℝ) ^ (3 : ℝ) ≤
        ρ * SingularSeries.liuSingularSeries N * (N : ℝ) /
          Real.log (N : ℝ) ^ (2 : ℝ) := by
  have hbase :
      ∀ᶠ N : ℕ in atTop,
        C * (N : ℝ) / Real.log (N : ℝ) ^ (3 : ℝ) ≤
          ρ * SingularSeries.liuSingularSeries N * (N : ℝ) /
            Real.log (N : ℝ) ^ (2 : ℝ) := by
    filter_upwards
      [MathlibNt.SieveTheory.LiuWeight.eventually_inverse_log_remainder_le_liuSingularSeries
        C ρ hρ] with N hN
    simpa [Real.rpow_natCast] using hN
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (hbase.and (eventually_ge_atTop (4 : ℕ)))
  refine ⟨N₀, (hN₀ N₀ le_rfl).2, ?_⟩
  intro N hN
  exact (hN₀ N hN).1

/-- Fixed-`s` normalized lower bound at the original beta cutoff.  The
lower-density factor is paid at fixed `s`, the actual main mass and actual
sieve product are normalized on the true singular-series scale, and the paid
Bombieri--Vinogradov remainder is absorbed into an arbitrary `δ` budget. -/
theorem goldbachS1_beta_fixed_normalized_lower
    (s δ : ℝ) (hs4 : 4 ≤ s) (hslt : s < (33 / 8 : ℝ)) (hδ : 0 < δ) :
    ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
        (((33 / 2 : ℝ) * Real.exp (-Real.eulerMascheroniConstant) * (1 - ε) *
              dimensionOneLowerLinearSieveFactor s - δ) *
            SingularSeries.liuSingularSeries N * (N : ℝ) /
            Real.log (N : ℝ) ^ (2 : ℝ) ≤
          (goldbachS1 (goldbachDifferenceCarrier N ε) N
            ((N : ℝ) ^ (4 / 33 : ℝ)) : ℝ)) := by
  intro ε hε hεu
  let a : ℝ := (33 / 2 : ℝ) * Real.exp (-Real.eulerMascheroniConstant)
  let f : ℝ := dimensionOneLowerLinearSieveFactor s
  have ha : 0 < a := by dsimp [a]; positivity
  have he : 0 < 1 - ε := sub_pos.mpr hεu
  by_cases hf : f ≤ 0
  · refine ⟨4, le_rfl, ?_⟩
    intro N hN _
    have hcoeff : a * (1 - ε) * f - δ ≤ 0 :=
      sub_nonpos.mpr (le_trans (mul_nonpos_of_nonneg_of_nonpos (by positivity) hf) hδ.le)
    have hS := (SingularSeries.liuSingularSeries_pos N).le
    exact le_trans (div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg hcoeff hS) (Nat.cast_nonneg N))
      (Real.rpow_nonneg (Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))) _))
      (Nat.cast_nonneg _)
  · have hf : 0 < f := lt_of_not_ge hf
    -- Separate density and mass losses, paying each from the same scalar slack.
    let ρ := min (f / 2) (δ / (4 * a * (1 - ε)))
    let η := min ((1 - ε) / 2) (δ / (4 * a * f))
    have hρ : 0 < ρ := lt_min (by positivity) (by positivity)
    have hη : 0 < η := lt_min (by positivity) (by positivity)
    have hρf : ρ ≤ f / 2 := min_le_left _ _
    have hηe : η ≤ (1 - ε) / 2 := min_le_left _ _
    have hηu : η < 1 - ε := by linarith
    have hρloss : ρ * (4 * a * (1 - ε)) ≤ δ :=
      (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
    have hηloss : η * (4 * a * f) ≤ δ :=
      (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
    have hcoef : a * (1 - ε) * f - δ ≤ a * (1 - ε - η) * (f - ρ) - δ / 2 := by
      nlinarith [mul_nonneg ha.le (mul_nonneg hη.le hρ.le)]
    obtain ⟨C, _, hpaid⟩ := goldbachS1_beta_lower_paid 3 (by norm_num)
    obtain ⟨Np, _, hp⟩ := hpaid s hs4 hslt ε hε hεu
    obtain ⟨Nd, _, hd⟩ := goldbachS1_beta_lowerDensity s ρ hs4 hslt hρ
    obtain ⟨Nm, _, hm⟩ := goldbachS1_beta_mainMass_mul_product_lower s ε η hs4 hslt hε hεu hη hηu
    obtain ⟨Nl, _, hl⟩ := goldbachS1_strictEndpoint_mainMass_lower ε η hε hεu hη
    have herr := LiuWeight.eventually_inverse_log_remainder_le_liuSingularSeries C (δ / 2) (by positivity)
    obtain ⟨Ne, hevent⟩ := eventually_atTop.mp herr
    refine ⟨max 4 (max Np (max Nd (max Nm (max Nl Ne)))), le_max_left _ _, ?_⟩
    intro N hN hEven
    have hN4 : 4 ≤ N := le_trans (le_max_left _ _) hN
    have hNp : Np ≤ N := by omega
    have hNd : Nd ≤ N := by omega
    have hNm : Nm ≤ N := by omega
    have hNl : Nl ≤ N := by omega
    have hNe : Ne ≤ N := by omega
    let S := goldbachS1BoundingSieve N hEven ε (S1BetaGeometryZeta N s)
    let T : ℝ := SingularSeries.liuSingularSeries N * (N : ℝ) / Real.log (N : ℝ) ^ (2 : ℕ)
    have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
    have hT : 0 ≤ T := by dsimp [T]; exact div_nonneg (mul_nonneg (SingularSeries.liuSingularSeries_pos N).le (Nat.cast_nonneg N)) (sq_nonneg _)
    have hX : 0 ≤ S.totalMass := by
      have hli := (hl N hNl).2.2
      change 0 ≤ BombieriVinogradov.trueLogarithmicIntegral (goldbachS1Endpoint N ε)
      exact le_trans (mul_nonneg (by linarith : 0 ≤ 1 - ε - η) (div_nonneg (Nat.cast_nonneg N) hlog)) hli
    have hscale : (a * (1 - ε - η)) * T ≤ S.totalMass * AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S := by
      convert hm N hNm hEven using 1; dsimp [a, T, S]; ring
    have hmain := Analysis.SieveNormalization.lower_product hX (by linarith : 0 ≤ f - ρ) hscale (hd N hNd hEven ε hε hεu)
    rw [goldbachS1BoundingSieve_mainSum_eq_totientSum] at hmain
    have hpay := hp N hNp hEven
    have herror := hevent N hNe
    norm_num [Real.rpow_natCast] at hpay ⊢
    have hfinal : (a * (1 - ε) * f - δ) * T ≤
        (goldbachS1 (goldbachDifferenceCarrier N ε) N ((N : ℝ) ^ (4 / 33 : ℝ)) : ℝ) := by
      have hcompare := mul_le_mul_of_nonneg_right hcoef hT
      dsimp [S] at hmain
      change _ ≤ BombieriVinogradov.trueLogarithmicIntegral (goldbachS1Endpoint N ε) * _ at hmain
      have herror' : C * (N : ℝ) / Real.log (N : ℝ) ^ (3 : ℕ) ≤ (δ / 2) * T := by
        convert herror using 1; dsimp [T]; ring
      nlinarith
    convert hfinal using 1; dsimp [a, f, T]; ring

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig