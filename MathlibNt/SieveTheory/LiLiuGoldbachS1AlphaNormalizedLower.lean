import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
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
  let f : ℝ := MathlibNt.SieveTheory.SwitchingPrinciple.dimensionOneLowerLinearSieveFactor 6
  let K : ℝ := 2 * Real.exp (-Real.eulerMascheroniConstant) / (4 / 53 : ℝ)
  have hK : 0 < K := by positivity
  have hKeval : K = (53 / 2 : ℝ) * Real.exp (-Real.eulerMascheroniConstant) := by
    dsimp [K]
    field_simp
    ring
  by_cases hf : f ≤ 0
  · refine ⟨4, by norm_num, ?_⟩
    intro N hN _hEven
    let scale : ℝ :=
      (N : ℝ) * SingularSeries.liuSingularSeries N / (Real.log (N : ℝ)) ^ 2
    have hscale_nonneg : 0 ≤ scale := by
      dsimp [scale]
      exact div_nonneg
        (mul_nonneg (Nat.cast_nonneg N) (SingularSeries.liuSingularSeries_pos N).le)
        (sq_nonneg _)
    have hcoeff_nonpos : K * (1 - ε) * f - δ ≤ 0 := by
      have h1ε_nonneg : 0 ≤ 1 - ε := by linarith
      have hbase_nonneg : 0 ≤ K * (1 - ε) := mul_nonneg hK.le h1ε_nonneg
      have hmain_nonpos : K * (1 - ε) * f ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hbase_nonneg hf
      linarith
    have hleft : (K * (1 - ε) * f - δ) * scale ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hcoeff_nonpos hscale_nonneg
    simpa [hKeval, f, scale, mul_assoc, mul_left_comm, mul_comm] using
      hleft.trans <| S1AlphaNormalizedLower_goldbachS1_nonneg _ _ _
  · have hfpos : 0 < f := lt_of_not_ge hf
    have hf1pos : 0 < f + 1 := by linarith
    let ρ : ℝ := min (f / 2) (δ / (4 * (K + 1)))
    let η : ℝ := min ((1 - ε) / 2) (δ / (4 * (K + 1) * (f + 1)))
    have hρ : 0 < ρ := by
      dsimp [ρ]
      exact lt_min (by positivity) (by positivity)
    have hρleHalf : ρ ≤ f / 2 := by
      dsimp [ρ]
      exact min_le_left _ _
    have hρltf : ρ < f := by nlinarith
    have hρle : ρ ≤ f := hρltf.le
    have hfr_nonneg : 0 ≤ f - ρ := sub_nonneg.mpr hρle
    have hη : 0 < η := by
      dsimp [η]
      exact lt_min (by positivity) (by positivity)
    have hηleHalf : η ≤ (1 - ε) / 2 := by
      dsimp [η]
      exact min_le_left _ _
    have hηlt : η < 1 - ε := by nlinarith
    obtain ⟨Nρ, _hNρ2, hDensity⟩ := goldbachS1_levelSix_lowerDensitySix ρ hρ
    obtain ⟨Nη, _hNη4, hMainScale⟩ :=
      goldbachS1_mainMass_mul_product_lower ε η hε hε1 hη hηlt
    obtain ⟨Nmass, _hNmass2, hMass⟩ :=
      goldbachS1_strictEndpoint_mainMass_lower ε η hε hε1 hη
    obtain ⟨Cpaid, _hCpaid, hPaidε⟩ := goldbachS1_levelSix_lower_paid 3 (by norm_num)
    obtain ⟨Npaid, _hNpaid2, hPaid⟩ := hPaidε ε hε hε1
    let u : ℝ := SingularSeries.liuUniversalProduct
    have hu : 0 < u := SingularSeries.liuUniversalProduct_pos
    let B : ℝ := Cpaid / ((δ / 2) * u)
    obtain ⟨Nlog, _hNlog4, hLog⟩ := S1AlphaNormalizedLower_exists_logBound B
    refine ⟨max 4 (max Nρ (max Nη (max Nmass (max Npaid Nlog)))), by norm_num, ?_⟩
    intro N hN hEven
    let z : ℝ := (N : ℝ) ^ (4 / 53 : ℝ)
    let S : BoundingSieve := goldbachS1BoundingSieve N hEven ε z
    let W : ℕ → ℝ :=
      LinearSieve.lowerRosserWeight (goldbachS1ProdPrimes N z) (S1LevelSixD N)
    let scale : ℝ :=
      (N : ℝ) * SingularSeries.liuSingularSeries N / (Real.log (N : ℝ)) ^ 2
    let err : ℝ := Cpaid * (N : ℝ) / (Real.log (N : ℝ)) ^ 3
    have hN4 : 4 ≤ N := (le_max_left _ _).trans hN
    have hrest : max Nρ (max Nη (max Nmass (max Npaid Nlog))) ≤ N :=
      (le_max_right _ _).trans hN
    have hNρle : Nρ ≤ N := (le_max_left _ _).trans hrest
    have hrest1 : max Nη (max Nmass (max Npaid Nlog)) ≤ N :=
      (le_max_right _ _).trans hrest
    have hNηle : Nη ≤ N := (le_max_left _ _).trans hrest1
    have hrest2 : max Nmass (max Npaid Nlog) ≤ N :=
      (le_max_right _ _).trans hrest1
    have hNmassle : Nmass ≤ N := (le_max_left _ _).trans hrest2
    have hrest3 : max Npaid Nlog ≤ N := (le_max_right _ _).trans hrest2
    have hNpaidle : Npaid ≤ N := (le_max_left _ _).trans hrest3
    have hNlogle : Nlog ≤ N := (le_max_right _ _).trans hrest3
    have hlogPos : 0 < Real.log (N : ℝ) := S1AlphaNormalizedLower_log_pos hN4
    have hratio_nonneg : 0 ≤ (N : ℝ) / (Real.log (N : ℝ)) ^ 2 :=
      div_nonneg (Nat.cast_nonneg N) (sq_nonneg _)
    have hscale_nonneg : 0 ≤ scale := by
      dsimp [scale]
      exact div_nonneg
        (mul_nonneg (Nat.cast_nonneg N) (SingularSeries.liuSingularSeries_pos N).le)
        (sq_nonneg _)
    have hMassLower : (1 - ε - η) * ((N : ℝ) / Real.log (N : ℝ)) ≤ S.totalMass := by
      simpa [goldbachS1Endpoint, S, z, goldbachS1BoundingSieve] using (hMass N hNmassle).2.2
    have hMassPos : 0 < S.totalMass := by
      have hNpos : 0 < (N : ℝ) := by positivity
      have hratio_pos : 0 < (N : ℝ) / Real.log (N : ℝ) := div_pos hNpos hlogPos
      have hleft_pos : 0 < (1 - ε - η) * ((N : ℝ) / Real.log (N : ℝ)) := by
        apply mul_pos <;> linarith [hlogPos]
      exact lt_of_lt_of_le hleft_pos hMassLower
    have hMassNonneg : 0 ≤ S.totalMass := hMassPos.le
    have hrawScale := hMainScale N hNηle hEven (4 / 53 : ℝ) (by norm_num)
    have hMainScaleN :
        ((K * (1 - ε - η)) * scale) ≤
          S.totalMass * AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S := by
      have hshape :
          ((K * (1 - ε - η)) * scale) =
            (N : ℝ) * ((1 - ε - η) * (K * SingularSeries.liuSingularSeries N)) /
              (Real.log (N : ℝ)) ^ 2 := by
        dsimp [K, scale]
        field_simp [hlogPos.ne']
      rw [hshape]
      simpa [S, z, K, mul_assoc, mul_left_comm, mul_comm] using hrawScale
    have hDensityN :
        (f - ρ) * AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S ≤ S.mainSum W := by
      simpa [f, S, z, W] using hDensity N hNρle hEven ε hε hε1
    have hDensityScaled :
        S.totalMass * ((f - ρ) * AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S) ≤
          S.totalMass * S.mainSum W :=
      mul_le_mul_of_nonneg_left hDensityN hMassNonneg
    have hMainRaw : (K * (1 - ε - η) * (f - ρ)) * scale ≤ S.totalMass * S.mainSum W := by
      have htmp :
          ((K * (1 - ε - η)) * scale) * (f - ρ) ≤
            (S.totalMass * AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S) * (f - ρ) :=
        mul_le_mul_of_nonneg_right hMainScaleN hfr_nonneg
      calc
        (K * (1 - ε - η) * (f - ρ)) * scale
            = ((K * (1 - ε - η)) * scale) * (f - ρ) := by ring
        _ ≤ (S.totalMass * AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S) * (f - ρ) := htmp
        _ = S.totalMass * ((f - ρ) * AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S) := by ring
        _ ≤ S.totalMass * S.mainSum W := hDensityScaled
    have hKle : K ≤ K + 1 := by linarith
    have hρbd : ρ ≤ δ / (4 * (K + 1)) := by
      dsimp [ρ]
      exact min_le_right _ _
    have hρstep : (K + 1) * ρ ≤ δ / 4 := by
      calc
        (K + 1) * ρ ≤ (K + 1) * (δ / (4 * (K + 1))) :=
          mul_le_mul_of_nonneg_left hρbd (by positivity)
        _ = δ / 4 := by field_simp
    have hρcore : K * ρ ≤ δ / 4 := by
      have hmul : K * ρ ≤ (K + 1) * ρ := mul_le_mul_of_nonneg_right hKle hρ.le
      exact hmul.trans hρstep
    have hρpart : K * ((1 - ε) * ρ) ≤ δ / 4 := by
      have h1εle : 1 - ε ≤ 1 := by linarith
      have htmp : (1 - ε) * ρ ≤ ρ := by nlinarith [h1εle, hρ.le]
      exact (mul_le_mul_of_nonneg_left htmp hK.le).trans hρcore
    have hηbd : η ≤ δ / (4 * (K + 1) * (f + 1)) := by
      dsimp [η]
      exact min_le_right _ _
    have hηstep : (K + 1) * η * (f + 1) ≤ δ / 4 := by
      calc
        (K + 1) * η * (f + 1)
            = ((K + 1) * (f + 1)) * η := by ring
        _ ≤ ((K + 1) * (f + 1)) * (δ / (4 * (K + 1) * (f + 1))) :=
          mul_le_mul_of_nonneg_left hηbd (by positivity)
        _ = δ / 4 := by field_simp
    have hηcore : K * η * (f + 1) ≤ δ / 4 := by
      have hfac_nonneg : 0 ≤ η * (f + 1) := by positivity
      have hmul : K * (η * (f + 1)) ≤ (K + 1) * (η * (f + 1)) :=
        mul_le_mul_of_nonneg_right hKle hfac_nonneg
      calc
        K * η * (f + 1) = K * (η * (f + 1)) := by ring
        _ ≤ (K + 1) * (η * (f + 1)) := hmul
        _ = (K + 1) * η * (f + 1) := by ring
        _ ≤ δ / 4 := hηstep
    have hηpart : K * (η * (f - ρ)) ≤ δ / 4 := by
      have htmp : η * (f - ρ) ≤ η * (f + 1) := by
        apply mul_le_mul_of_nonneg_left
        · nlinarith
        · exact hη.le
      exact (mul_le_mul_of_nonneg_left htmp hK.le).trans (by simpa [mul_assoc] using hηcore)
    have hParamApprox : K * (1 - ε) * f - δ / 2 ≤ K * (1 - ε - η) * (f - ρ) := by
      have hsum : K * ((1 - ε) * ρ) + K * (η * (f - ρ)) ≤ δ / 2 := by
        calc
          K * ((1 - ε) * ρ) + K * (η * (f - ρ)) ≤ δ / 4 + δ / 4 := add_le_add hρpart hηpart
          _ = δ / 2 := by ring
      have hdecomp :
          K * (1 - ε - η) * (f - ρ) =
            K * (1 - ε) * f - (K * ((1 - ε) * ρ) + K * (η * (f - ρ))) := by
        ring
      rw [hdecomp]
      exact sub_le_sub_left hsum (K * (1 - ε) * f)
    have hHalfMain : (K * (1 - ε) * f - δ / 2) * scale ≤ S.totalMass * S.mainSum W := by
      exact (mul_le_mul_of_nonneg_right hParamApprox hscale_nonneg).trans hMainRaw
    have hu_le : u ≤ SingularSeries.liuSingularSeries N :=
      SingularSeries.liuUniversalProduct_le_liuSingularSeries N
    have hBlog : B ≤ Real.log (N : ℝ) := hLog N hNlogle
    have hdu : 0 < (δ / 2) * u := by positivity
    have hBmul : ((δ / 2) * u) * B = Cpaid := by
      dsimp [B]
      field_simp [hdu.ne']
    have hBmul' : u * ((δ / 2) * B) = Cpaid := by
      calc
        u * ((δ / 2) * B) = ((δ / 2) * u) * B := by ring
        _ = Cpaid := hBmul
    have hbudget : Cpaid ≤ ((δ / 2) * u) * Real.log (N : ℝ) := by
      have hmul := mul_le_mul_of_nonneg_left hBlog hdu.le
      simpa [hBmul', mul_assoc, mul_left_comm, mul_comm] using hmul
    have hbudgetDiv : Cpaid / Real.log (N : ℝ) ≤ (δ / 2) * u := by
      exact (div_le_iff₀ hlogPos).2 (by simpa [mul_assoc, mul_left_comm, mul_comm] using hbudget)
    have hErrUniversal :
        Cpaid * (N : ℝ) / (Real.log (N : ℝ)) ^ 3 ≤
          (δ / 2) * u * (N : ℝ) / (Real.log (N : ℝ)) ^ 2 := by
      have hmul := mul_le_mul_of_nonneg_right hbudgetDiv hratio_nonneg
      have hEqL :
          (Cpaid / Real.log (N : ℝ)) * ((N : ℝ) / (Real.log (N : ℝ)) ^ 2) =
            Cpaid * (N : ℝ) / (Real.log (N : ℝ)) ^ 3 := by
        field_simp [hlogPos.ne']
      calc
        Cpaid * (N : ℝ) / (Real.log (N : ℝ)) ^ 3
            = (Cpaid / Real.log (N : ℝ)) * ((N : ℝ) / (Real.log (N : ℝ)) ^ 2) := by rw [hEqL]
        _ ≤ ((δ / 2) * u) * ((N : ℝ) / (Real.log (N : ℝ)) ^ 2) := hmul
        _ = (δ / 2) * u * (N : ℝ) / (Real.log (N : ℝ)) ^ 2 := by ring
    have hδhalf_nonneg : 0 ≤ δ / 2 := by positivity
    have hSeriesBudget : err ≤ (δ / 2) * scale := by
      have huScaled : (δ / 2) * u ≤ (δ / 2) * SingularSeries.liuSingularSeries N :=
        mul_le_mul_of_nonneg_left hu_le hδhalf_nonneg
      have hmul := mul_le_mul_of_nonneg_right huScaled hratio_nonneg
      calc
        err ≤ (δ / 2) * u * (N : ℝ) / (Real.log (N : ℝ)) ^ 2 := hErrUniversal
        _ = ((δ / 2) * u) * ((N : ℝ) / (Real.log (N : ℝ)) ^ 2) := by ring
        _ ≤ ((δ / 2) * SingularSeries.liuSingularSeries N) * ((N : ℝ) / (Real.log (N : ℝ)) ^ 2) := hmul
        _ = (δ / 2) * scale := by dsimp [scale]; ring
    have hbridge :
        S.mainSum W =
          ∑ d ∈ (goldbachS1ProdPrimes N z).divisors, W d / Nat.totient d :=
      goldbachS1BoundingSieve_mainSum_eq_totientSum hEven ε z W
    have hPaidMain :
        S.totalMass * S.mainSum W - err ≤
          (goldbachS1 (goldbachDifferenceCarrier N ε) N z : ℝ) := by
      rw [hbridge]
      simpa [S, W, z, err, goldbachS1BoundingSieve] using hPaid N hNpaidle hEven
    have hHalfSub :
        (K * (1 - ε) * f - δ / 2) * scale - err ≤
          (goldbachS1 (goldbachDifferenceCarrier N ε) N z : ℝ) := by
      exact (sub_le_sub_right hHalfMain err).trans hPaidMain
    have hTargetStep :
        (K * (1 - ε) * f - δ) * scale ≤
          (K * (1 - ε) * f - δ / 2) * scale - err := by
      have htmp :
          (K * (1 - ε) * f - δ / 2) * scale - (δ / 2) * scale ≤
            (K * (1 - ε) * f - δ / 2) * scale - err := by
        linarith [hSeriesBudget]
      calc
        (K * (1 - ε) * f - δ) * scale
            = (K * (1 - ε) * f - δ / 2) * scale - (δ / 2) * scale := by ring
        _ ≤ (K * (1 - ε) * f - δ / 2) * scale - err := htmp
    simpa [hKeval, f, scale, z, mul_assoc, mul_left_comm, mul_comm] using hTargetStep.trans hHalfSub

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig