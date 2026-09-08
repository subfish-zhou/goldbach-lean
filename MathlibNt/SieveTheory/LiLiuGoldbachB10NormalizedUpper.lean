import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import MathlibNt.Analysis.LogScaleAbsorption
import MathlibNt.SieveTheory.LiLiuGoldbachB10MainWeight
import MathlibNt.SieveTheory.LiLiuGoldbachB10PaidUpper
import MathlibNt.SieveTheory.LiLiuGoldbachB10SieveProduct
import MathlibNt.SieveTheory.LiuSingularSeries
import MathlibNt.SieveTheory.SwitchingPrinciple

noncomputable section

open Filter

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

private theorem B10NormalizedUpper_eight_mul_one_add_cube_le
    {τ δ : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) (hτδ : 56 * τ ≤ δ) :
    8 * (1 + τ) ^ 3 ≤ 8 + δ := by
  have hτ2 : τ ^ 2 ≤ τ := by
    nlinarith [sq_nonneg (τ - 1)]
  have hτ3 : τ ^ 3 ≤ τ := by
    have hmul := mul_le_mul_of_nonneg_left hτ2 hτ0
    nlinarith
  have hmain : 24 * τ + 24 * τ ^ 2 + 8 * τ ^ 3 ≤ 56 * τ := by
    nlinarith
  calc
    8 * (1 + τ) ^ 3 = 8 + (24 * τ + 24 * τ ^ 2 + 8 * τ ^ 3) := by ring
    _ ≤ 8 + 56 * τ := by gcongr
    _ ≤ 8 + δ := by linarith

private theorem B10NormalizedUpper_tendsto_logLog_div_log :
    Tendsto (fun N : ℕ => Real.log (Real.log (N : ℝ)) / Real.log (N : ℝ))
      atTop (nhds 0) := by
  have hreal : Tendsto (fun x : ℝ => Real.log x / x) atTop (nhds 0) := by
    simpa [Real.rpow_one] using
      (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1)).tendsto_div_nhds_zero
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  change Tendsto
    (((fun x : ℝ => Real.log x / x) ∘ fun N : ℕ => Real.log (N : ℝ)))
    atTop (nhds 0)
  exact hreal.comp hlog

private theorem B10NormalizedUpper_Z_large_eventually
    (B K : ℝ) (_hB : 0 ≤ B) (hK : 0 < K) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      let Δ := (N : ℝ) ^ ((1 : ℝ) / 2) / Real.log (N : ℝ) ^ (B + 1)
      let Z := Δ ^ ((1 : ℝ) / 2)
      K ≤ Z := by
  have hsmall :=
    (isLittleO_log_rpow_rpow_atTop (B + 1) (by norm_num : (0 : ℝ) < 1 / 2)).bound
      (show (0 : ℝ) < 1 / K ^ 2 by positivity)
  have hsmall' : ∀ᶠ x : ℝ in atTop,
      Real.log x ^ (B + 1) ≤ (1 / K ^ 2) * x ^ ((1 : ℝ) / 2) := by
    filter_upwards [hsmall, eventually_ge_atTop (1 : ℝ)] with x hx hx1
    have hlogx : 0 ≤ Real.log x := Real.log_nonneg hx1
    have hx0 : 0 ≤ x := by linarith
    simpa only [Real.norm_of_nonneg (Real.rpow_nonneg hlogx _),
      Real.norm_of_nonneg (Real.rpow_nonneg hx0 _)] using hx
  have hnat : ∀ᶠ N : ℕ in atTop,
      Real.log (N : ℝ) ^ (B + 1) ≤
        (1 / K ^ 2) * (N : ℝ) ^ ((1 : ℝ) / 2) :=
    tendsto_natCast_atTop_atTop.eventually hsmall'
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp hnat
  refine ⟨max 4 N₁, le_max_left _ _, ?_⟩
  intro N hN
  let Δ : ℝ := (N : ℝ) ^ ((1 : ℝ) / 2) / Real.log (N : ℝ) ^ (B + 1)
  let Z : ℝ := Δ ^ ((1 : ℝ) / 2)
  have hN₁' : N₁ ≤ N := (le_max_right _ _).trans hN
  have hN4 : 4 ≤ N := (le_max_left _ _).trans hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlogNpos : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hpowPos : 0 < Real.log (N : ℝ) ^ (B + 1) := Real.rpow_pos_of_pos hlogNpos _
  have hsmallN :
      Real.log (N : ℝ) ^ (B + 1) ≤
        (1 / K ^ 2) * (N : ℝ) ^ ((1 : ℝ) / 2) := hN₁ N hN₁'
  have hmul : K ^ 2 * Real.log (N : ℝ) ^ (B + 1) ≤ (N : ℝ) ^ ((1 : ℝ) / 2) := by
    have htmp := mul_le_mul_of_nonneg_left hsmallN (sq_nonneg K)
    simpa [mul_assoc, hK.ne'] using htmp
  have hΔK : K ^ 2 ≤ Δ := by
    dsimp [Δ]
    exact (le_div_iff₀ hpowPos).2 hmul
  have hΔnonneg : 0 ≤ Δ := by
    dsimp [Δ]
    positivity
  dsimp [Z]
  rw [← Real.sqrt_eq_rpow]
  have hsqrt := Real.sqrt_le_sqrt hΔK
  simpa [Δ, Real.sqrt_sq_eq_abs, abs_of_nonneg hK.le] using hsqrt

private theorem B10NormalizedUpper_logN_div_logZ_le_eventually
    (B τ : ℝ) (hB : 0 ≤ B) (hτ : 0 < τ) (hτ1 : τ ≤ 1) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      let Δ := (N : ℝ) ^ ((1 : ℝ) / 2) / Real.log (N : ℝ) ^ (B + 1)
      let Z := Δ ^ ((1 : ℝ) / 2)
      0 < Real.log Z ∧ Real.log (N : ℝ) / Real.log Z ≤ 4 * (1 + τ) := by
  have hB1 : 0 < B + 1 := by linarith
  let κ : ℝ := τ / (4 * (B + 1))
  have hκ : 0 < κ := by
    dsimp [κ]
    positivity
  have hsmall :
      ∀ᶠ N : ℕ in atTop,
        Real.log (Real.log (N : ℝ)) / Real.log (N : ℝ) ∈ Metric.ball (0 : ℝ) κ :=
    B10NormalizedUpper_tendsto_logLog_div_log.eventually (Metric.ball_mem_nhds 0 hκ)
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp hsmall
  refine ⟨max 4 N₁, le_max_left _ _, ?_⟩
  intro N hN
  let Δ : ℝ := (N : ℝ) ^ ((1 : ℝ) / 2) / Real.log (N : ℝ) ^ (B + 1)
  let Z : ℝ := Δ ^ ((1 : ℝ) / 2)
  have hN₁' : N₁ ≤ N := (le_max_right _ _).trans hN
  have hN4 : 4 ≤ N := (le_max_left _ _).trans hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlogNpos : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hratioAbs : |Real.log (Real.log (N : ℝ)) / Real.log (N : ℝ)| < κ := by
    simpa [Real.dist_eq, abs_div] using hN₁ N hN₁'
  have hΔratio :
      Real.log Δ / Real.log (N : ℝ) =
        (1 / 2 : ℝ) - (B + 1) * (Real.log (Real.log (N : ℝ)) / Real.log (N : ℝ)) := by
    dsimp [Δ]
    rw [Real.log_div
      (by positivity : (N : ℝ) ^ ((1 : ℝ) / 2) ≠ 0)
      (ne_of_gt (Real.rpow_pos_of_pos hlogNpos _)),
      Real.log_rpow hNpos, Real.log_rpow hlogNpos]
    field_simp [hlogNpos.ne']
  have hsmallTerm :
      (B + 1) * (Real.log (Real.log (N : ℝ)) / Real.log (N : ℝ)) ≤ τ / 4 := by
    calc
      (B + 1) * (Real.log (Real.log (N : ℝ)) / Real.log (N : ℝ))
        ≤ (B + 1) * |Real.log (Real.log (N : ℝ)) / Real.log (N : ℝ)| := by
            gcongr
            exact le_abs_self _
      _ ≤ (B + 1) * κ := by
            exact mul_le_mul_of_nonneg_left hratioAbs.le hB1.le
      _ = τ / 4 := by
            dsimp [κ]
            field_simp [hB1.ne']
  have hΔlower : (1 / 2 : ℝ) - τ / 4 ≤ Real.log Δ / Real.log (N : ℝ) := by
    rw [hΔratio]
    linarith
  have hquarterPos : 0 < (1 / 4 : ℝ) - τ / 8 := by
    nlinarith
  have hΔposRatio : 0 < Real.log Δ / Real.log (N : ℝ) := by
    exact lt_of_lt_of_le (by nlinarith) hΔlower
  have hlogΔpos : 0 < Real.log Δ := by
    have hEq : Real.log Δ = (Real.log Δ / Real.log (N : ℝ)) * Real.log (N : ℝ) := by
      field_simp [hlogNpos.ne']
    rw [hEq]
    positivity
  have hΔnonneg : 0 ≤ Δ := by
    dsimp [Δ]
    positivity
  have hlogZ :
      Real.log Z = Real.log Δ / 2 := by
    dsimp [Z]
    rw [← Real.sqrt_eq_rpow, Real.log_sqrt hΔnonneg]
  have hlogZpos : 0 < Real.log Z := by
    rw [hlogZ]
    positivity
  have hZratio :
      Real.log Z / Real.log (N : ℝ) = (Real.log Δ / Real.log (N : ℝ)) / 2 := by
    rw [hlogZ]
    field_simp [hlogNpos.ne']
  have hZlower : (1 / 4 : ℝ) - τ / 8 ≤ Real.log Z / Real.log (N : ℝ) := by
    rw [hZratio]
    nlinarith
  have hrecip :
      1 / (Real.log Z / Real.log (N : ℝ)) ≤ 4 * (1 + τ) := by
    calc
      1 / (Real.log Z / Real.log (N : ℝ))
        ≤ 1 / ((1 / 4 : ℝ) - τ / 8) :=
          one_div_le_one_div_of_le hquarterPos hZlower
      _ = 4 / (1 - τ / 2) := by
          have hEq : ((1 / 4 : ℝ) - τ / 8) = (1 - τ / 2) / 4 := by ring
          have hne₂ : 1 - τ / 2 ≠ 0 := by linarith
          rw [hEq]
          field_simp [hne₂]
      _ ≤ 4 * (1 + τ) := by
          have hden : 0 < 1 - τ / 2 := by nlinarith
          have hone : 1 ≤ (1 + τ) * (1 - τ / 2) := by
            nlinarith [sq_nonneg (τ - 1)]
          have haux : 1 / (1 - τ / 2) ≤ 1 + τ := by
            exact (div_le_iff₀ hden).2 hone
          simpa [div_eq_mul_inv, one_div, mul_comm, mul_left_comm, mul_assoc] using
            (mul_le_mul_of_nonneg_left haux (by norm_num : 0 ≤ (4 : ℝ)))
  have hratio :
      Real.log (N : ℝ) / Real.log Z ≤ 4 * (1 + τ) := by
    have hEq : Real.log (N : ℝ) / Real.log Z = 1 / (Real.log Z / Real.log (N : ℝ)) := by
      field_simp [hlogNpos.ne', hlogZpos.ne']
    rw [hEq]
    exact hrecip
  exact ⟨hlogZpos, hratio⟩

private theorem B10NormalizedUpper_paid_error_absorb_eventually
    (C δ : ℝ) (hC : 0 < C) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      C * (N : ℝ) / Real.log (N : ℝ) ^ (4 : ℝ) ≤
        δ * SingularSeries.liuUniversalProduct * (N : ℝ) /
          Real.log (N : ℝ) ^ (2 : ℝ) := by
  -- Normalize the positive paid coefficient to its absolute-value envelope.
  have hbase :=
    MathlibNt.Analysis.eventually_log_rpow_remainder_lt_of_lower_bound
      |C| SingularSeries.liuUniversalProduct δ 2
      SingularSeries.liuUniversalProduct_pos hδ (by norm_num)
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp hbase
  refine ⟨max 4 M, le_max_left _ _, ?_⟩
  intro N hN
  have h := (hM N ((le_max_right _ _).trans hN)
    2 SingularSeries.liuUniversalProduct le_rfl).le
  simpa only [abs_of_pos hC, show (2 : ℝ) + 2 = 4 by norm_num] using h

/-- The already-produced paid upper bound and sieve-product estimate combine to
the genuine coefficient `8 + δ` once the cutoff is normalized by
`Z = ((N^(1/2))/log(N)^(B+1))^(1/2)`. The theorem retains the real main mass
`X` and pays the full remainder into a true `δ · 𝔖_Liu(N) · N / log(N)^2`
term, with `B` chosen before `ε, γ` and `N₀` chosen before `β`. -/
theorem goldbachB10SiftedCount_normalized_upper
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ ε γ : ℝ, 0 < ε → ε < 1 → γ < (1 : ℝ) / 3 →
      ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → ∀ _hEven : Even N, ∀ β : ℝ,
        (1 : ℝ) / 18 < β →
        let Δ := (N : ℝ) ^ ((1 : ℝ) / 2) / Real.log (N : ℝ) ^ (B + 1)
        let Z := Δ ^ ((1 : ℝ) / 2)
        let X := goldbachB10MainMass N ε ((N : ℝ) ^ β) ((N : ℝ) ^ γ)
        (goldbachB10SiftedCount N ε ((N : ℝ) ^ β) ((N : ℝ) ^ γ) Z : ℝ) ≤
          (8 + δ) * SingularSeries.liuSingularSeries N * X / Real.log (N : ℝ) +
            δ * SingularSeries.liuSingularSeries N * (N : ℝ) /
              Real.log (N : ℝ) ^ (2 : ℝ) := by
  let τ : ℝ := min (δ / 56) 1
  have hτ : 0 < τ := by
    dsimp [τ]
    exact lt_min (by positivity) zero_lt_one
  have hτ0 : 0 ≤ τ := hτ.le
  have hτ1 : τ ≤ 1 := by
    dsimp [τ]
    exact min_le_right _ _
  have hτδ : 56 * τ ≤ δ := by
    dsimp [τ]
    by_cases hsmall : δ / 56 ≤ 1
    · rw [min_eq_left hsmall]
      nlinarith
    · rw [min_eq_right (le_of_lt (lt_of_not_ge hsmall))]
      nlinarith
  obtain ⟨C, hC, B, hB, hpaid⟩ := goldbachB10SiftedCount_upper_paid (4 : ℝ) (by norm_num)
  obtain ⟨Z₀, hZ₀, hsieve⟩ :=
    goldbachB10BoundingSieve_sieveProductPrimeFactors_log_le_liuSingularSeries τ hτ
  obtain ⟨z₀, hpaidεγ⟩ := hpaid (τ * Real.exp Real.eulerMascheroniConstant) (by
    exact mul_pos hτ (Real.exp_pos _))
  refine ⟨B, hB, ?_⟩
  intro ε γ hε hεlt hγ
  obtain ⟨Npaid, hNpaid2, hpaidN⟩ := hpaidεγ ε γ hε hεlt hγ
  obtain ⟨Nmass, hNmass2, hmass⟩ := goldbachB10MainMass_nonneg_eventually ε γ hε hεlt hγ
  obtain ⟨NZ, hNZ4, hZlarge⟩ :=
    B10NormalizedUpper_Z_large_eventually B (max 2 (max z₀ Z₀)) hB
      (by positivity)
  obtain ⟨Nratio, hNratio4, hratio⟩ :=
    B10NormalizedUpper_logN_div_logZ_le_eventually B τ hB hτ hτ1
  obtain ⟨Nerr, hNerr4, herr⟩ :=
    B10NormalizedUpper_paid_error_absorb_eventually C δ hC hδ
  let N₀ := max 4 (max Npaid (max Nmass (max NZ (max Nratio Nerr))))
  refine ⟨N₀, le_max_left _ _, ?_⟩
  intro N hN hEven β hβ
  let Δ : ℝ := (N : ℝ) ^ ((1 : ℝ) / 2) / Real.log (N : ℝ) ^ (B + 1)
  let Z : ℝ := Δ ^ ((1 : ℝ) / 2)
  let X : ℝ := goldbachB10MainMass N ε ((N : ℝ) ^ β) ((N : ℝ) ^ γ)
  let S :=
    goldbachB10BoundingSieve N hEven ε ((N : ℝ) ^ β) ((N : ℝ) ^ γ) Z X
  have hN4 : 4 ≤ N := by
    exact le_trans (le_max_left _ _) hN
  have hNpack : max Npaid (max Nmass (max NZ (max Nratio Nerr))) ≤ N :=
    (le_max_right _ _).trans hN
  have hNpaid' : Npaid ≤ N := (le_max_left _ _).trans hNpack
  have hNrest₁ : max Nmass (max NZ (max Nratio Nerr)) ≤ N :=
    (le_max_right _ _).trans hNpack
  have hNmass' : Nmass ≤ N := (le_max_left _ _).trans hNrest₁
  have hNrest₂ : max NZ (max Nratio Nerr) ≤ N := (le_max_right _ _).trans hNrest₁
  have hNZ' : NZ ≤ N := (le_max_left _ _).trans hNrest₂
  have hNrest₃ : max Nratio Nerr ≤ N := (le_max_right _ _).trans hNrest₂
  have hNratio' : Nratio ≤ N := (le_max_left _ _).trans hNrest₃
  have hNerr' : Nerr ≤ N := (le_max_right _ _).trans hNrest₃
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlogNpos : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hXnonneg : 0 ≤ X := by
    dsimp [X]
    exact hmass N hNmass' β hβ
  have hZbig : max 2 (max z₀ Z₀) ≤ Z := by
    simpa [Δ, Z] using hZlarge N hNZ'
  have hZ2 : 2 ≤ Z := (le_max_left _ _).trans hZbig
  have hz₀ : z₀ ≤ Z := (le_max_left _ _).trans ((le_max_right _ _).trans hZbig)
  have hZ₀ : Z₀ ≤ Z := (le_max_right _ _).trans ((le_max_right _ _).trans hZbig)
  have hratioNZ :
      Real.log (N : ℝ) / Real.log Z ≤ 4 * (1 + τ) := by
    exact (hratio N hNratio' |>.2)
  have hlogZpos : 0 < Real.log Z := by
    exact (hratio N hNratio' |>.1)
  have hΔnonneg : 0 ≤ Δ := by
    dsimp [Δ]
    positivity
  have hZsqrt : Z = Real.sqrt Δ := by
    dsimp [Z]
    rw [← Real.sqrt_eq_rpow]
  have hΔge4 : 4 ≤ Δ := by
    rw [hZsqrt] at hZ2
    nlinarith [Real.sq_sqrt hΔnonneg]
  have hlogΔpos : 0 < Real.log Δ := Real.log_pos (by linarith)
  have hsEq : (2 : ℝ) = Real.log Δ / Real.log Z := by
    rw [hZsqrt, Real.log_sqrt hΔnonneg]
    field_simp [hlogΔpos.ne']
  have hpaidBound :
      (goldbachB10SiftedCount N ε ((N : ℝ) ^ β) ((N : ℝ) ^ γ) Z : ℝ) ≤
        X * (MathlibNt.SieveTheory.SwitchingPrinciple.jurkatRichertUpperLinearSieveFactor (2 : ℝ) +
            τ * Real.exp Real.eulerMascheroniConstant) *
          AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S +
        C * (N : ℝ) / Real.log (N : ℝ) ^ (4 : ℝ) := by
    simpa [Δ, Z, X, S] using
      hpaidN N hNpaid' hEven β hβ Z (2 : ℝ) hz₀ hZ2 hsEq (by norm_num) (by norm_num)
  have hVlog :
      AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S * Real.log Z ≤
        2 * Real.exp (-Real.eulerMascheroniConstant) * (1 + τ) *
          SingularSeries.liuSingularSeries N := by
    simpa [S, X, Z] using
      hsieve N hN4 hEven ε ((N : ℝ) ^ β) ((N : ℝ) ^ γ) X Z hZ₀
  have hV :
      AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S ≤
        2 * Real.exp (-Real.eulerMascheroniConstant) * (1 + τ) *
          SingularSeries.liuSingularSeries N / Real.log Z := by
    exact (le_div_iff₀ hlogZpos).2 (by
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hVlog)
  have hF2 :
      MathlibNt.SieveTheory.SwitchingPrinciple.jurkatRichertUpperLinearSieveFactor (2 : ℝ) =
        Real.exp Real.eulerMascheroniConstant := by
    norm_num [MathlibNt.SieveTheory.SwitchingPrinciple.jurkatRichertUpperLinearSieveFactor]
  have hfactor :
      MathlibNt.SieveTheory.SwitchingPrinciple.jurkatRichertUpperLinearSieveFactor (2 : ℝ) +
          τ * Real.exp Real.eulerMascheroniConstant =
        Real.exp Real.eulerMascheroniConstant * (1 + τ) := by
    rw [hF2]
    ring
  have hInvLogZ :
      1 / Real.log Z ≤ (4 * (1 + τ)) / Real.log (N : ℝ) := by
    calc
      1 / Real.log Z = (Real.log (N : ℝ) / Real.log Z) / Real.log (N : ℝ) := by
        field_simp [hlogNpos.ne', hlogZpos.ne']
      _ ≤ (4 * (1 + τ)) / Real.log (N : ℝ) := by
        exact div_le_div_of_nonneg_right hratioNZ hlogNpos.le
  have hCoeff :
      2 * (1 + τ) ^ 2 / Real.log Z ≤ (8 + δ) / Real.log (N : ℝ) := by
    calc
      2 * (1 + τ) ^ 2 / Real.log Z = 2 * (1 + τ) ^ 2 * (1 / Real.log Z) := by
        rw [div_eq_mul_inv, one_div]
      _ ≤ 2 * (1 + τ) ^ 2 * ((4 * (1 + τ)) / Real.log (N : ℝ)) := by
        gcongr
      _ = (8 * (1 + τ) ^ 3) / Real.log (N : ℝ) := by
        ring
      _ ≤ (8 + δ) / Real.log (N : ℝ) := by
        exact div_le_div_of_nonneg_right
          (B10NormalizedUpper_eight_mul_one_add_cube_le hτ0 hτ1 hτδ) hlogNpos.le
  have hMain :
      X * (MathlibNt.SieveTheory.SwitchingPrinciple.jurkatRichertUpperLinearSieveFactor (2 : ℝ) +
          τ * Real.exp Real.eulerMascheroniConstant) *
        AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S ≤
        (8 + δ) * SingularSeries.liuSingularSeries N * X / Real.log (N : ℝ) := by
    rw [hfactor]
    have hmul :=
      mul_le_mul_of_nonneg_left hV (by positivity : 0 ≤ X * (Real.exp Real.eulerMascheroniConstant * (1 + τ)))
    calc
      X * (Real.exp Real.eulerMascheroniConstant * (1 + τ)) *
          AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S
        ≤ X * (Real.exp Real.eulerMascheroniConstant * (1 + τ)) *
            (2 * Real.exp (-Real.eulerMascheroniConstant) * (1 + τ) *
              SingularSeries.liuSingularSeries N / Real.log Z) := hmul
      _ = 2 * (1 + τ) ^ 2 * SingularSeries.liuSingularSeries N * X / Real.log Z := by
        have hexp :
            Real.exp Real.eulerMascheroniConstant *
                Real.exp (-Real.eulerMascheroniConstant) = 1 := by
          rw [← Real.exp_add]
          norm_num
        rw [div_eq_mul_inv]
        calc
          X * (Real.exp Real.eulerMascheroniConstant * (1 + τ)) *
              (2 * Real.exp (-Real.eulerMascheroniConstant) * (1 + τ) *
                SingularSeries.liuSingularSeries N * (Real.log Z)⁻¹)
            = X * ((Real.exp Real.eulerMascheroniConstant *
                Real.exp (-Real.eulerMascheroniConstant)) *
                (2 * (1 + τ) ^ 2 * SingularSeries.liuSingularSeries N * (Real.log Z)⁻¹)) := by
                  ring
          _ = 2 * (1 + τ) ^ 2 * SingularSeries.liuSingularSeries N * X / Real.log Z := by
                rw [hexp]
                ring
      _ = (SingularSeries.liuSingularSeries N * X) * (2 * (1 + τ) ^ 2 / Real.log Z) := by
        ring
      _ ≤ (SingularSeries.liuSingularSeries N * X) * ((8 + δ) / Real.log (N : ℝ)) := by
        exact mul_le_mul_of_nonneg_left hCoeff
          (mul_nonneg (SingularSeries.liuSingularSeries_pos N).le hXnonneg)
      _ = (8 + δ) * SingularSeries.liuSingularSeries N * X / Real.log (N : ℝ) := by
        ring
  have hErrU :
      C * (N : ℝ) / Real.log (N : ℝ) ^ (4 : ℝ) ≤
        δ * SingularSeries.liuUniversalProduct * (N : ℝ) /
          Real.log (N : ℝ) ^ (2 : ℝ) := herr N hNerr'
  have hErr :
      C * (N : ℝ) / Real.log (N : ℝ) ^ (4 : ℝ) ≤
        δ * SingularSeries.liuSingularSeries N * (N : ℝ) /
          Real.log (N : ℝ) ^ (2 : ℝ) := by
    have hδseries :
        δ * SingularSeries.liuUniversalProduct ≤
          δ * SingularSeries.liuSingularSeries N := by
      exact mul_le_mul_of_nonneg_left
        (SingularSeries.liuUniversalProduct_le_liuSingularSeries N) hδ.le
    have hmassNonneg : 0 ≤ (N : ℝ) / Real.log (N : ℝ) ^ (2 : ℝ) := by
      positivity
    have hErrS :
        δ * SingularSeries.liuUniversalProduct * (N : ℝ) /
            Real.log (N : ℝ) ^ (2 : ℝ) ≤
          δ * SingularSeries.liuSingularSeries N * (N : ℝ) /
            Real.log (N : ℝ) ^ (2 : ℝ) := by
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
        (mul_le_mul_of_nonneg_right hδseries hmassNonneg)
    exact hErrU.trans hErrS
  have hfinal :
      (goldbachB10SiftedCount N ε ((N : ℝ) ^ β) ((N : ℝ) ^ γ) Z : ℝ) ≤
        (8 + δ) * SingularSeries.liuSingularSeries N * X / Real.log (N : ℝ) +
          δ * SingularSeries.liuSingularSeries N * (N : ℝ) /
            Real.log (N : ℝ) ^ (2 : ℝ) := by
    exact hpaidBound.trans (add_le_add hMain hErr)
  simpa [Δ, Z, X] using hfinal

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig