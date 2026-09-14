import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import MathlibNt.Analysis.SieveNormalization
import MathlibNt.SieveTheory.Arithmetic.LiuLogScaleAbsorption
import MathlibNt.SieveTheory.LiuSingularSeries
import MathlibNt.SieveTheory.LiLiuGoldbachBasicToSieve
import MathlibNt.SieveTheory.LiLiuGoldbachOnePlusOneNineFinite
import MathlibNt.SieveTheory.LiLiuGoldbachS1Carrier
import MathlibNt.SieveTheory.LiLiuGoldbachS1LowerDensitySix
import MathlibNt.SieveTheory.LiLiuGoldbachS1MainMass
import MathlibNt.SieveTheory.LiLiuGoldbachS1MainScale
import MathlibNt.SieveTheory.LiLiuGoldbachS1PaidLower

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

set_option autoImplicit false

private theorem S1AlphaNormalizedLower_exists_logBound (B : ℝ) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → B ≤ Real.log (N : ℝ) := by
  have hlog : ∀ᶠ N : ℕ in Filter.atTop, B ≤ Real.log (N : ℝ) := by
    exact (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (Filter.eventually_ge_atTop B)
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp hlog
  refine ⟨max 4 N₀, le_max_left _ _, ?_⟩
  intro N hN
  exact hN₀ N ((le_max_right _ _).trans hN)

private theorem S1AlphaNormalizedLower_log_pos {N : ℕ} (hN : 4 ≤ N) :
    0 < Real.log (N : ℝ) := by
  have h1 : (1 : ℝ) < (N : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 4) hN)
  exact Real.log_pos h1

private theorem S1AlphaNormalizedLower_goldbachS1_nonneg
    (A : Finset ℕ) (N : ℕ) (u : ℝ) :
    0 ≤ (goldbachS1 A N u : ℝ) := by
  classical
  norm_num [goldbachS1, literalH]

theorem goldbachS1_alphaFourFiftyThree_normalized_lower
    (δ ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
      ((((53 / 2 : ℝ) * Real.exp (-Real.eulerMascheroniConstant) *
            (1 - ε) * MathlibNt.SieveTheory.SwitchingPrinciple.dimensionOneLowerLinearSieveFactor 6) - δ) *
          (SingularSeries.liuSingularSeries N * (N : ℝ) / (Real.log (N : ℝ)) ^ 2)) ≤
        (goldbachS1 (goldbachDifferenceCarrier N ε) N ((N : ℝ) ^ (4 / 53 : ℝ)) : ℝ) := by
  classical
  let c : ℝ := 53 / 2 * Real.exp (-Real.eulerMascheroniConstant)
  let f := MathlibNt.SieveTheory.SwitchingPrinciple.dimensionOneLowerLinearSieveFactor 6
  have hc : 0 < c := by dsimp [c]; positivity
  have he : 0 < 1 - ε := sub_pos.mpr hε1
  by_cases hf : f ≤ 0
  · refine ⟨4, le_rfl, fun N _ _ => ?_⟩
    apply le_trans _ (S1AlphaNormalizedLower_goldbachS1_nonneg _ _ _)
    apply mul_nonpos_of_nonpos_of_nonneg
    · change c * (1 - ε) * f - δ ≤ 0
      exact sub_nonpos.mpr ((mul_nonpos_of_nonneg_of_nonpos (by positivity) hf).trans hδ.le)
    · exact div_nonneg (mul_nonneg (SingularSeries.liuSingularSeries_pos N).le
        (Nat.cast_nonneg N)) (sq_nonneg _)
  have hf : 0 < f := lt_of_not_ge hf
  obtain ⟨η, hη, hηb⟩ := exists_between (show 0 < min (1 - ε) (δ / (4 * c * f)) by positivity)
  have hηe := hηb.trans_le (min_le_left _ _)
  have hηcost := (lt_div_iff₀ (show 0 < 4 * c * f by positivity)).mp
    (hηb.trans_le (min_le_right _ _))
  obtain ⟨ρ, hρ, hρb⟩ := exists_between (show 0 < min f (δ / (4 * c * (1 - ε))) by positivity)
  have hρf := hρb.trans_le (min_le_left _ _)
  have hρcost := (lt_div_iff₀ (show 0 < 4 * c * (1 - ε) by positivity)).mp
    (hρb.trans_le (min_le_right _ _))
  have hcoef : c * (1 - ε) * f - δ / 2 ≤ c * (1 - ε - η) * (f - ρ) := by
    nlinarith only [hηcost, hρcost, mul_nonneg (mul_nonneg hc.le hη.le) hρ.le]
  obtain ⟨Nd, _, hd⟩ := goldbachS1_levelSix_lowerDensitySix ρ hρ
  obtain ⟨Ns, hNs, hs⟩ := goldbachS1_mainMass_mul_product_lower ε η hε hε1 hη hηe
  obtain ⟨Nm, _, hm⟩ := goldbachS1_strictEndpoint_mainMass_lower ε η hε hε1 hη
  obtain ⟨C, _, hpaid⟩ := goldbachS1_levelSix_lower_paid 3 (by norm_num)
  obtain ⟨Np, _, hp⟩ := hpaid ε hε hε1
  obtain ⟨Nr, hr⟩ := Filter.eventually_atTop.mp
    (LiuWeight.eventually_inverse_log_remainder_le_liuSingularSeries C (δ / 2) (half_pos hδ))
  refine ⟨max Ns (max Nd (max Nm (max Np Nr))), hNs.trans (le_max_left _ _), ?_⟩
  intro N hN hEven
  have hNsN : Ns ≤ N := (le_max_left _ _).trans hN
  have hNdN : Nd ≤ N := by omega
  have hNmN : Nm ≤ N := by omega
  have hNpN : Np ≤ N := by omega
  have hNrN : Nr ≤ N := by omega
  let S := goldbachS1BoundingSieve N hEven ε ((N : ℝ) ^ (4 / 53 : ℝ))
  let t := SingularSeries.liuSingularSeries N * (N : ℝ) / Real.log (N : ℝ) ^ 2
  have ht : 0 ≤ t := div_nonneg (mul_nonneg (SingularSeries.liuSingularSeries_pos N).le
    (Nat.cast_nonneg N)) (sq_nonneg _)
  have hX : 0 ≤ S.totalMass := le_trans
    (mul_nonneg (sub_nonneg.mpr hηe.le) (div_nonneg (Nat.cast_nonneg N)
      (S1AlphaNormalizedLower_log_pos (hNs.trans hNsN)).le)) (hm N hNmN).2.2
  have hscale : (c * (1 - ε - η)) * t ≤ S.totalMass *
      AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S := by
    convert hs N hNsN hEven (4 / 53) (by norm_num) using 1
    dsimp [c, t, S]
    ring
  have hmain := MathlibNt.Analysis.SieveNormalization.lower_product hX
    (sub_nonneg.mpr hρf.le) hscale (hd N hNdN hEven ε hε hε1)
  rw [goldbachS1BoundingSieve_mainSum_eq_totientSum] at hmain
  have hpaidN := hp N hNpN hEven
  have hrem : C * (N : ℝ) / Real.log (N : ℝ) ^ (3 : ℝ) ≤ δ / 2 * t := by
    have hp3 : Real.log (N : ℝ) ^ (3 : ℝ) = Real.log (N : ℝ) ^ (3 : ℕ) :=
      Real.rpow_natCast _ _
    rw [hp3]
    simpa only [t, mul_div_assoc, mul_assoc] using hr N hNrN
  have hfinal := mul_le_mul_of_nonneg_right hcoef ht
  change (c * (1 - ε) * f - δ) * t ≤ _
  change _ ≤ S.totalMass * _ at hmain
  change S.totalMass * _ - _ ≤ _ at hpaidN
  nlinarith only [hmain, hpaidN, hrem, hfinal]

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig