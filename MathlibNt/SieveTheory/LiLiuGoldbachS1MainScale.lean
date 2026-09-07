import MathlibNt.SieveTheory.LiLiuGoldbachS1SieveProductLower
import MathlibNt.SieveTheory.LiLiuGoldbachS1Carrier
import MathlibNt.SieveTheory.LiLiuGoldbachS1MainMass

open scoped BigOperators

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

theorem goldbachS1BoundingSieve_sieveProduct_eq
    (N : ℕ) (hEven : Even N) (ε z : ℝ) :
    AnalyticNumberTheory.Sieve.sieveProductPrimeFactors (goldbachS1BoundingSieve N hEven ε z) =
      MertensTheorem.goldbachSieveProduct N (Nat.ceil z) := by
  unfold AnalyticNumberTheory.Sieve.sieveProductPrimeFactors goldbachS1BoundingSieve
  rw [goldbachS1ProdPrimes_primeFactors]
  unfold MertensTheorem.goldbachSieveProduct goldbachS1SiftingPrimes
  apply Finset.prod_congr rfl
  intro p hp
  rw [AnalyticNumberTheory.Sieve.goldbachNu_apply_prime (Finset.mem_filter.mp hp).2.1]

/-- The actual S1 mass times its actual Euler product is bounded below on the
true singular-series scale. This does not assert a lower Rosser density bound. -/
theorem goldbachS1_mainMass_mul_product_lower (ε η : ℝ)
    (hε : 0 < ε) (hεu : ε < 1) (hη : 0 < η) (hηu : η < 1 - ε) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → ∀ hEven : Even N,
      ∀ α : ℝ, (1 : ℝ) / 18 ≤ α →
        (2 * Real.exp (-Real.eulerMascheroniConstant) / α) * (1 - ε - η) *
          SingularSeries.liuSingularSeries N * (N : ℝ) / Real.log (N : ℝ) ^ 2 ≤
        (goldbachS1BoundingSieve N hEven ε ((N : ℝ) ^ α)).totalMass *
          AnalyticNumberTheory.Sieve.sieveProductPrimeFactors
            (goldbachS1BoundingSieve N hEven ε ((N : ℝ) ^ α)) := by
  let τ : ℝ := η / 2
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hτ1 : τ < 1 := by dsimp [τ]; linarith
  obtain ⟨Np, hNp, hp⟩ := goldbachS1PrimeProduct_log_ge_liuSingularSeries τ hτ hτ1
  obtain ⟨Nm, _hNm, hm⟩ := goldbachS1_strictEndpoint_mainMass_lower ε τ hε hεu hτ
  refine ⟨max Np Nm, hNp.trans (le_max_left _ _), ?_⟩
  intro N hN hEven α hα
  have hNp' : Np ≤ N := (le_max_left _ _).trans hN
  have hNm' : Nm ≤ N := (le_max_right _ _).trans hN
  have hN4 := hNp.trans hNp'
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hαpos : 0 < α := lt_of_lt_of_le (by norm_num) hα
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hC : 0 < SingularSeries.liuSingularSeries N := SingularSeries.liuSingularSeries_pos N
  let X := (goldbachS1BoundingSieve N hEven ε ((N : ℝ) ^ α)).totalMass
  let V := AnalyticNumberTheory.Sieve.sieveProductPrimeFactors
    (goldbachS1BoundingSieve N hEven ε ((N : ℝ) ^ α))
  have hmass : (1 - ε - τ) * ((N : ℝ) / Real.log (N : ℝ)) ≤ X := (hm N hNm').2.2
  have ha : 0 ≤ 1 - ε - τ := by dsimp [τ]; linarith
  have hX : 0 ≤ X := (mul_nonneg ha (div_nonneg hNpos.le hlog.le)).trans hmass
  have hvlog := hp N hNp' hEven ((N : ℝ) ^ α)
    (Real.rpow_le_rpow_of_exponent_le hN1 hα)
  rw [Real.log_rpow hNpos, ← goldbachS1BoundingSieve_sieveProduct_eq N hEven ε] at hvlog
  have hv : 2 * Real.exp (-Real.eulerMascheroniConstant) * (1 - τ) *
      SingularSeries.liuSingularSeries N / (α * Real.log (N : ℝ)) ≤ V :=
    (div_le_iff₀ (mul_pos hαpos hlog)).mpr hvlog
  have hvlower : 0 ≤ 2 * Real.exp (-Real.eulerMascheroniConstant) * (1 - τ) *
      SingularSeries.liuSingularSeries N / (α * Real.log (N : ℝ)) := by positivity
  have hmul := mul_le_mul hmass hv hvlower hX
  have hcoef : 1 - ε - η ≤ (1 - ε - τ) * (1 - τ) := by
    dsimp [τ]
    nlinarith [mul_nonneg hε.le hη.le]
  let B := (2 * Real.exp (-Real.eulerMascheroniConstant) / α) *
    SingularSeries.liuSingularSeries N * (N : ℝ) / Real.log (N : ℝ) ^ 2
  have hB : 0 ≤ B := by dsimp [B]; positivity
  change _ ≤ X * V
  calc
    _ = (1 - ε - η) * B := by dsimp [B]; ring
    _ ≤ ((1 - ε - τ) * (1 - τ)) * B := mul_le_mul_of_nonneg_right hcoef hB
    _ = ((1 - ε - τ) * ((N : ℝ) / Real.log (N : ℝ))) *
        (2 * Real.exp (-Real.eulerMascheroniConstant) * (1 - τ) *
          SingularSeries.liuSingularSeries N / (α * Real.log (N : ℝ))) := by
      dsimp [B]
      field_simp [hαpos.ne', hlog.ne']
    _ ≤ X * V := hmul

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig