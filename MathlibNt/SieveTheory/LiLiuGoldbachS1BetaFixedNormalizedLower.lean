import MathlibNt.SieveTheory.LiLiuGoldbachS1BetaPaidLower
import MathlibNt.SieveTheory.LiLiuGoldbachS1BetaLowerDensity
import MathlibNt.SieveTheory.LiLiuGoldbachS1BetaMainScale
import MathlibNt.SieveTheory.LiLiuGoldbachS1Carrier
import MathlibNt.SieveTheory.LiLiuGoldbachS1MainMass
import MathlibNt.SieveTheory.LiuSelbergCorrectedChenBridge

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
  let A : ℝ := (33 / 2 : ℝ) * Real.exp (-Real.eulerMascheroniConstant)
  let F : ℝ := dimensionOneLowerLinearSieveFactor s
  have hA : 0 < A := by
    dsimp [A]
    exact S1BetaNormalizedLower_mainConst_pos
  obtain ⟨C, hC, hpaidAll⟩ := goldbachS1_beta_lower_paid (3 : ℝ) (by norm_num)
  intro ε hε hεu
  have hε1 : 0 < 1 - ε := by linarith
  by_cases hFnonpos : F ≤ 0
  · refine ⟨4, le_rfl, ?_⟩
    intro N hN _hEven
    let T : ℝ :=
      SingularSeries.liuSingularSeries N * (N : ℝ) / Real.log (N : ℝ) ^ (2 : ℝ)
    have hTnonneg : 0 ≤ T := by
      dsimp [T]
      have hlogSq : 0 < Real.log (N : ℝ) ^ (2 : ℝ) := by
        have hlog : 0 < Real.log (N : ℝ) := by
          exact Real.log_pos (by exact_mod_cast (show 1 < N by omega))
        exact Real.rpow_pos_of_pos hlog 2
      exact div_nonneg
        (mul_nonneg (SingularSeries.liuSingularSeries_pos N).le (Nat.cast_nonneg N))
        hlogSq.le
    have hcoef : A * (1 - ε) * F - δ ≤ 0 := by
      have hprod : A * (1 - ε) * F ≤ 0 := by
        have hscale : 0 ≤ A * (1 - ε) := by positivity
        exact mul_nonpos_of_nonneg_of_nonpos hscale hFnonpos
      linarith
    have hleft : (A * (1 - ε) * F - δ) * T ≤ 0 := by
      exact mul_nonpos_of_nonpos_of_nonneg hcoef hTnonneg
    have hright :
        0 ≤
          (goldbachS1 (goldbachDifferenceCarrier N ε) N
            ((N : ℝ) ^ (4 / 33 : ℝ)) : ℝ) :=
      S1BetaNormalizedLower_goldbachS1_nonneg N ε
    simpa [A, F, T, mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv] using
      hleft.trans hright
  · have hF : 0 < F := lt_of_not_ge hFnonpos
    let η : ℝ := min ((1 - ε) / 2) (δ / (6 * A * F))
    let ρ : ℝ := min (F / 2) (δ / (6 * A))
    let ξ : ℝ := δ / 3
    have hη : 0 < η := by
      dsimp [η]
      apply lt_min
      · positivity
      · positivity
    have hηu : η < 1 - ε := by
      have hhalf : (1 - ε) / 2 < 1 - ε := by linarith
      exact lt_of_le_of_lt (by dsimp [η]; exact min_le_left _ _) hhalf
    have hρ : 0 < ρ := by
      dsimp [ρ]
      apply lt_min
      · positivity
      · positivity
    have hρlt : ρ < F := by
      have hhalf : F / 2 < F := by nlinarith
      exact lt_of_le_of_lt (by dsimp [ρ]; exact min_le_left _ _) hhalf
    have hFrho : 0 ≤ F - ρ := sub_nonneg.mpr hρlt.le
    have hξ : 0 < ξ := by
      dsimp [ξ]
      positivity
    have hηBound : A * η * F ≤ δ / 6 := by
      have hηle : η ≤ δ / (6 * A * F) := by
        dsimp [η]
        exact min_le_right _ _
      have hAFnonneg : 0 ≤ A * F := (mul_pos hA hF).le
      have hmain :
          (A * F) * η ≤ (A * F) * (δ / (6 * A * F)) :=
        mul_le_mul_of_nonneg_left hηle hAFnonneg
      calc
        A * η * F = (A * F) * η := by ring
        _ ≤ (A * F) * (δ / (6 * A * F)) := hmain
        _ = δ / 6 := by
          field_simp [hA.ne', hF.ne']
    have hρBound : A * ρ ≤ δ / 6 := by
      have hρle : ρ ≤ δ / (6 * A) := by
        dsimp [ρ]
        exact min_le_right _ _
      have hAnonneg : 0 ≤ A := hA.le
      have hmain : A * ρ ≤ A * (δ / (6 * A)) :=
        mul_le_mul_of_nonneg_left hρle hAnonneg
      calc
        A * ρ ≤ A * (δ / (6 * A)) := hmain
        _ = δ / 6 := by
          field_simp [hA.ne']
    have hρScaled : A * (1 - ε - η) * ρ ≤ δ / 6 := by
      have hfactor : 0 ≤ 1 - ε - η := by linarith
      have hone : 1 - ε - η ≤ 1 := by linarith
      calc
        A * (1 - ε - η) * ρ = (1 - ε - η) * (A * ρ) := by ring
        _ ≤ 1 * (A * ρ) := by
            gcongr
        _ = A * ρ := by ring
        _ ≤ δ / 6 := hρBound
    obtain ⟨Nmass, hNmass, hmass⟩ :=
      goldbachS1_beta_mainMass_mul_product_lower s ε η hs4 hslt hε hεu hη hηu
    obtain ⟨Ndens, hNdens, hdens⟩ := goldbachS1_beta_lowerDensity s ρ hs4 hslt hρ
    obtain ⟨Npaid, hNpaid, hpaid⟩ := hpaidAll s hs4 hslt ε hε hεu
    obtain ⟨Nerr, hNerr, herr⟩ := S1BetaNormalizedLower_paidErrorAbsorbEventually C ξ hξ
    obtain ⟨NX, hNX, hX⟩ :=
      goldbachS1_strictEndpoint_mainMass_lower ε ((1 - ε) / 2) hε hεu (by linarith)
    refine ⟨max 4 (max Nmass (max Ndens (max Npaid (max Nerr NX)))), le_max_left _ _, ?_⟩
    intro N hN hEven
    let S : BoundingSieve := goldbachS1BoundingSieve N hEven ε (S1BetaGeometryZeta N s)
    let μ : ℕ → ℝ :=
      LinearSieve.lowerRosserWeight
        (goldbachS1ProdPrimes N (S1BetaGeometryZeta N s))
        (S1BetaGeometryD N s)
    let X : ℝ := S.totalMass
    let V : ℝ := AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S
    let M : ℝ := S.mainSum μ
    let T : ℝ := SingularSeries.liuSingularSeries N * (N : ℝ) / Real.log (N : ℝ) ^ (2 : ℝ)
    let RHS : ℝ :=
      (goldbachS1 (goldbachDifferenceCarrier N ε) N
        ((N : ℝ) ^ (4 / 33 : ℝ)) : ℝ)
    have hNrest : max Nmass (max Ndens (max Npaid (max Nerr NX))) ≤ N :=
      (le_max_right _ _).trans hN
    have hNmass' : Nmass ≤ N := (le_max_left _ _).trans hNrest
    have hNrest' : max Ndens (max Npaid (max Nerr NX)) ≤ N :=
      (le_max_right _ _).trans hNrest
    have hNdens' : Ndens ≤ N := (le_max_left _ _).trans hNrest'
    have hNrest'' : max Npaid (max Nerr NX) ≤ N :=
      (le_max_right _ _).trans hNrest'
    have hNpaid' : Npaid ≤ N := (le_max_left _ _).trans hNrest''
    have hNrest''' : max Nerr NX ≤ N := (le_max_right _ _).trans hNrest''
    have hNerr' : Nerr ≤ N := (le_max_left _ _).trans hNrest'''
    have hNX' : NX ≤ N := (le_max_right _ _).trans hNrest'''
    have hN4 : 4 ≤ N := (le_max_left _ _).trans hN
    have hNpos : 0 < (N : ℝ) := by
      exact_mod_cast (show 0 < N by omega)
    have hlogN : 0 < Real.log (N : ℝ) := by
      exact Real.log_pos (by exact_mod_cast (show 1 < N by omega))
    have hXlower : ((1 - ε) / 2) * ((N : ℝ) / Real.log (N : ℝ)) ≤ X := by
      have hXlowerRaw : (1 - ε - (1 - ε) / 2) * ((N : ℝ) / Real.log (N : ℝ)) ≤ X := by
        dsimp [X, S]
        simpa [goldbachS1BoundingSieve, goldbachS1Endpoint] using (hX N hNX').2.2
      nlinarith
    have hXpos : 0 < X := by
      have hpos : 0 < ((1 - ε) / 2) * ((N : ℝ) / Real.log (N : ℝ)) := by
        have hratio : 0 < (N : ℝ) / Real.log (N : ℝ) := div_pos hNpos hlogN
        have hhalf : 0 < (1 - ε) / 2 := by linarith
        exact mul_pos hhalf hratio
      exact lt_of_lt_of_le hpos hXlower
    have hXnonneg : 0 ≤ X := hXpos.le
    have hTnonneg : 0 ≤ T := by
      dsimp [T]
      have hlogSq : 0 < Real.log (N : ℝ) ^ (2 : ℝ) := Real.rpow_pos_of_pos hlogN 2
      exact div_nonneg
        (mul_nonneg (SingularSeries.liuSingularSeries_pos N).le (Nat.cast_nonneg N))
        hlogSq.le
    have hmassN :
        A * (1 - ε - η) * T ≤ X * V := by
      simpa [A, S, X, V, T, mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv] using
        hmass N hNmass' hEven
    have hdensN : (F - ρ) * V ≤ M := by
      simpa [F, S, V, M, μ] using hdens N hNdens' hEven ε hε hεu
    have hscale :
        A * (1 - ε - η) * (F - ρ) * T ≤ X * M := by
      calc
        A * (1 - ε - η) * (F - ρ) * T = (F - ρ) * (A * (1 - ε - η) * T) := by
          ring
        _ ≤ (F - ρ) * (X * V) := mul_le_mul_of_nonneg_left hmassN hFrho
        _ = X * ((F - ρ) * V) := by ring
        _ ≤ X * M := mul_le_mul_of_nonneg_left hdensN hXnonneg
    have hmainSum :
        M =
          ∑ d ∈ (goldbachS1ProdPrimes N (S1BetaGeometryZeta N s)).divisors,
            μ d / Nat.totient d := by
      have hmainSumRaw := goldbachS1BoundingSieve_mainSum_eq_totientSum
        (N := N) (hEven := hEven) (ε := ε) (z := S1BetaGeometryZeta N s)
        (μ := LinearSieve.lowerRosserWeight
          (goldbachS1ProdPrimes N (S1BetaGeometryZeta N s))
          (S1BetaGeometryD N s))
      simpa [M, S, μ] using hmainSumRaw
    have hpaidN :
        X * M - C * (N : ℝ) / Real.log (N : ℝ) ^ (3 : ℝ) ≤ RHS := by
      have hpaidRaw := hpaid N hNpaid' hEven
      rw [← hmainSum] at hpaidRaw
      simpa [X, S, RHS, goldbachS1BoundingSieve] using hpaidRaw
    have hpaidCombined :
        (A * (1 - ε - η) * (F - ρ) - ξ) * T ≤ RHS := by
      have hsub :
          (A * (1 - ε - η) * (F - ρ) - ξ) * T ≤
            X * M - C * (N : ℝ) / Real.log (N : ℝ) ^ (3 : ℝ) := by
        have hleft' :
            A * (1 - ε - η) * (F - ρ) * T - ξ * T ≤ X * M - ξ * T :=
          sub_le_sub_right hscale _
        have hright' :
            X * M - ξ * T ≤ X * M - C * (N : ℝ) / Real.log (N : ℝ) ^ (3 : ℝ) := by
          have hErr :
              C * (N : ℝ) / Real.log (N : ℝ) ^ (3 : ℝ) ≤ ξ * T := by
            simpa [T, mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv] using herr N hNerr'
          have hneg :
              -(ξ * T) ≤ -(C * (N : ℝ) / Real.log (N : ℝ) ^ (3 : ℝ)) :=
            neg_le_neg hErr
          simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
            add_le_add_left hneg (X * M)
        have htmp :
            A * (1 - ε - η) * (F - ρ) * T - ξ * T ≤
              X * M - C * (N : ℝ) / Real.log (N : ℝ) ^ (3 : ℝ) :=
          hleft'.trans hright'
        convert htmp using 1
        ring
      exact hsub.trans hpaidN
    have hcoef :
        A * (1 - ε) * F - δ ≤ A * (1 - ε - η) * (F - ρ) - ξ := by
      dsimp [ξ]
      nlinarith [hηBound, hρScaled]
    have hmain :
        (A * (1 - ε) * F - δ) * T ≤ RHS := by
      exact (mul_le_mul_of_nonneg_right hcoef hTnonneg).trans hpaidCombined
    convert hmain using 1
    ring

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig