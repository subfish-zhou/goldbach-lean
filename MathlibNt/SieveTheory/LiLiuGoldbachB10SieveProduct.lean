import MathlibNt.SieveTheory.LiLiuGoldbachB10FibreSieve
import MathlibNt.SieveTheory.LiuSingularSeries
import MathlibNt.SieveTheory.MertensTheorem
import MathlibNt.SieveTheory.Arithmetic.GoldbachLiuProductBridge

noncomputable section

open scoped BigOperators
open Classical Filter

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- The actual `B10` Euler product, written in the existing Mertens normalization
with the strict cutoff transported by `Nat.ceil`. -/
noncomputable def goldbachB10PrimeProduct (N : ℕ) (Z : ℝ) : ℝ :=
  MertensTheorem.goldbachSieveProduct N (Nat.ceil Z)

theorem goldbachB10PrimeProduct_eq_sieveProductPrimeFactors
    (N : ℕ) (_hEven : Even N) (ε b c Z X : ℝ) :
    goldbachB10PrimeProduct N Z =
      AnalyticNumberTheory.Sieve.sieveProductPrimeFactors
        (goldbachB10BoundingSieve N _hEven ε b c Z X) := by
  unfold goldbachB10PrimeProduct MertensTheorem.goldbachSieveProduct
  unfold AnalyticNumberTheory.Sieve.sieveProductPrimeFactors goldbachB10BoundingSieve
  rw [goldbachB10ProdPrimes_primeFactors]
  apply Finset.prod_congr rfl
  intro p hp
  have hpPrime : p.Prime := (Finset.mem_filter.mp hp).2.1
  rw [AnalyticNumberTheory.Sieve.goldbachNu_apply_prime hpPrime]

private theorem B10SieveProduct_delta_pos {η : ℝ} (hη : 0 < η) :
    0 < min (η / 7) 1 := by
  refine lt_min ?_ zero_lt_one
  positivity

private theorem B10SieveProduct_one_add_cube_le
    {δ η : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hδη : 7 * δ ≤ η) :
    (1 + δ) ^ 3 ≤ 1 + η := by
  have hδ2 : δ ^ 2 ≤ δ := by nlinarith [sq_nonneg (δ - 1)]
  have hδ3 : δ ^ 3 ≤ δ := by
    have hmul := mul_le_mul_of_nonneg_left hδ2 hδ0
    nlinarith
  have hmain : 3 * δ + 3 * δ ^ 2 + δ ^ 3 ≤ 7 * δ := by
    nlinarith
  nlinarith [hmain]

private theorem B10SieveProduct_half_le_ceil_sub_one {Z : ℝ} (hZ : 2 ≤ Z) :
    Z / 2 ≤ ((Nat.ceil Z - 1 : ℕ) : ℝ) := by
  have hceil2r : (2 : ℝ) ≤ (Nat.ceil Z : ℝ) := hZ.trans (Nat.le_ceil Z)
  have hceil2 : 2 ≤ Nat.ceil Z := by exact_mod_cast hceil2r
  have hnat : Nat.ceil Z ≤ 2 * (Nat.ceil Z - 1) := by omega
  have hcast : (Nat.ceil Z : ℝ) ≤ 2 * ((Nat.ceil Z - 1 : ℕ) : ℝ) := by
    exact_mod_cast hnat
  have hZle : Z ≤ 2 * ((Nat.ceil Z - 1 : ℕ) : ℝ) := (Nat.le_ceil Z).trans hcast
  nlinarith

private theorem B10SieveProduct_log_lower_of_two_mul_exp_le
    {A Z : ℝ} (hZ : 2 ≤ Z) (hZA : 2 * Real.exp A ≤ Z) :
    A ≤ Real.log (((Nat.ceil Z - 1 : ℕ) : ℝ)) := by
  have hhalf := B10SieveProduct_half_le_ceil_sub_one hZ
  have hExp : Real.exp A ≤ ((Nat.ceil Z - 1 : ℕ) : ℝ) := by
    have hmid : Real.exp A ≤ Z / 2 := by nlinarith
    exact hmid.trans hhalf
  have hlog := Real.log_le_log (Real.exp_pos A) hExp
  simpa [Real.log_exp] using hlog

private theorem B10SieveProduct_log_transport
    {δ Z : ℝ} (hδ : 0 < δ) (hZ : 2 ≤ Z)
    (hZA : 2 * Real.exp (Real.log 2 / δ) ≤ Z) :
    Real.log Z ≤ (1 + δ) * Real.log (((Nat.ceil Z - 1 : ℕ) : ℝ)) := by
  have hhalf := B10SieveProduct_half_le_ceil_sub_one hZ
  have harg1le : (1 : ℝ) ≤ ((Nat.ceil Z - 1 : ℕ) : ℝ) := by
    nlinarith [hhalf]
  have harg0 : 0 < ((Nat.ceil Z - 1 : ℕ) : ℝ) := by linarith
  have hZ0 : 0 < Z := by linarith
  have hZle : Z ≤ 2 * ((Nat.ceil Z - 1 : ℕ) : ℝ) := by
    nlinarith [hhalf]
  have hlog2div :
      Real.log 2 / δ ≤ Real.log (((Nat.ceil Z - 1 : ℕ) : ℝ)) :=
    B10SieveProduct_log_lower_of_two_mul_exp_le hZ hZA
  have hlog2le :
      Real.log 2 ≤ δ * Real.log (((Nat.ceil Z - 1 : ℕ) : ℝ)) := by
    have hmul := mul_le_mul_of_nonneg_left hlog2div hδ.le
    have hδne : δ ≠ 0 := ne_of_gt hδ
    simpa [hδne, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hmul
  have hlogZ :
      Real.log Z ≤ Real.log (2 * (((Nat.ceil Z - 1 : ℕ) : ℝ))) := by
    exact Real.log_le_log hZ0 hZle
  calc
    Real.log Z ≤ Real.log (2 * (((Nat.ceil Z - 1 : ℕ) : ℝ))) := hlogZ
    _ = Real.log 2 + Real.log (((Nat.ceil Z - 1 : ℕ) : ℝ)) := by
      rw [Real.log_mul (by positivity) (show (((Nat.ceil Z - 1 : ℕ) : ℝ)) ≠ 0 by positivity)]
    _ ≤ δ * Real.log (((Nat.ceil Z - 1 : ℕ) : ℝ)) +
          Real.log (((Nat.ceil Z - 1 : ℕ) : ℝ)) := by
            gcongr
    _ = (1 + δ) * Real.log (((Nat.ceil Z - 1 : ℕ) : ℝ)) := by ring

private theorem B10SieveProduct_absConst_div_log_le
    {δ C Z : ℝ} (hδ : 0 < δ) (hZ : 4 ≤ Z)
    (hZA : 2 * Real.exp (|C| / (δ * Real.exp (-Real.eulerMascheroniConstant))) ≤ Z) :
    |C| / Real.log (((Nat.ceil Z - 1 : ℕ) : ℝ)) ≤
      δ * Real.exp (-Real.eulerMascheroniConstant) := by
  have hceil4r : (4 : ℝ) ≤ (Nat.ceil Z : ℝ) := hZ.trans (Nat.le_ceil Z)
  have hceil4 : 4 ≤ Nat.ceil Z := by exact_mod_cast hceil4r
  have hlogpos : 0 < Real.log (((Nat.ceil Z - 1 : ℕ) : ℝ)) :=
    Real.log_pos (by exact_mod_cast (show 1 < Nat.ceil Z - 1 by omega))
  exact (div_le_comm₀ hlogpos (mul_pos hδ (Real.exp_pos _))).2
    (B10SieveProduct_log_lower_of_two_mul_exp_le (by linarith) hZA)

theorem goldbachB10PrimeProduct_log_le_liuSingularSeries
    (η : ℝ) (hη : 0 < η) :
    ∃ Z₀ : ℝ, 2 ≤ Z₀ ∧ ∀ (N : ℕ), 4 ≤ N → ∀ _hEven : Even N, ∀ Z : ℝ, Z₀ ≤ Z →
      goldbachB10PrimeProduct N Z * Real.log Z ≤
        2 * Real.exp (-Real.eulerMascheroniConstant) * (1 + η) *
          SingularSeries.liuSingularSeries N := by
  let δ : ℝ := min (η / 7) 1
  have hδ : 0 < δ := B10SieveProduct_delta_pos hη
  have hδ0 : 0 ≤ δ := hδ.le
  have hδ1 : δ ≤ 1 := by
    dsimp [δ]
    exact min_le_right _ _
  have hδη : 7 * δ ≤ η := by
    have hle : δ ≤ η / 7 := by
      dsimp [δ]
      exact min_le_left _ _
    nlinarith
  have hδcube : (1 + δ) ^ 3 ≤ 1 + η :=
    B10SieveProduct_one_add_cube_le hδ0 hδ1 hδη
  obtain ⟨C, hC⟩ := GoldbachLiuProductBridge.exists_log_bounds
  obtain ⟨T, hT⟩ := eventually_atTop.mp
    (SingularSeries.eventually_liuSingularSeriesTruncated_le δ hδ)
  let logThreshold : ℝ := 2 * Real.exp (Real.log 2 / δ)
  let errThreshold : ℝ :=
    2 * Real.exp (|C| / (δ * Real.exp (-Real.eulerMascheroniConstant)))
  let Z₀ : ℝ := max ((T + 1 : ℕ) : ℝ) (max 4 (max logThreshold errThreshold))
  refine ⟨Z₀, ?_, ?_⟩
  · dsimp [Z₀]
    exact le_trans (by norm_num : (2 : ℝ) ≤ 4)
      ((le_max_left 4 (max logThreshold errThreshold)).trans (le_max_right _ _))
  · intro N hN _hEven Z hZ
    have hZT : ((T + 1 : ℕ) : ℝ) ≤ Z := (le_max_left _ _).trans hZ
    have hZrest : max 4 (max logThreshold errThreshold) ≤ Z :=
      (le_max_right _ _).trans hZ
    have hZ4 : 4 ≤ Z := (le_max_left _ _).trans hZrest
    have hZlogErr : max logThreshold errThreshold ≤ Z := (le_max_right _ _).trans hZrest
    have hZlog : logThreshold ≤ Z := (le_max_left _ _).trans hZlogErr
    have hZerr : errThreshold ≤ Z := (le_max_right _ _).trans hZlogErr
    have hzNat : 3 ≤ Nat.ceil Z := by
      exact_mod_cast (show (3 : ℝ) ≤ (Nat.ceil Z : ℝ) from
        (show (3 : ℝ) ≤ Z by linarith).trans (Nat.le_ceil Z))
    have hTnat1 : T + 1 ≤ Nat.ceil Z := by
      exact_mod_cast (hZT.trans (Nat.le_ceil Z))
    have hTnat : T ≤ Nat.ceil Z - 1 := by omega
    have hliuTrunc :
        SingularSeries.liuSingularSeriesTruncated N (Nat.ceil Z - 1) ≤
          (1 + δ) * SingularSeries.liuSingularSeries N := by
      exact hT (Nat.ceil Z - 1) hTnat N (by omega)
    -- Share the exact Liu-normalized product bound with the S1 lower estimate.
    have hPrimeUpper := (hC N (Nat.ceil Z) hzNat _hEven hN).2
    have hLogTransport :
        Real.log Z ≤
          (1 + δ) * Real.log (((Nat.ceil Z - 1 : ℕ) : ℝ)) :=
      B10SieveProduct_log_transport hδ (by linarith) hZlog
    have hErrTransport :
        |C| / Real.log (((Nat.ceil Z - 1 : ℕ) : ℝ)) ≤
          δ * Real.exp (-Real.eulerMascheroniConstant) :=
      B10SieveProduct_absConst_div_log_le hδ (by linarith) hZerr
    have hTruncPos :
        0 ≤ SingularSeries.liuSingularSeriesTruncated N (Nat.ceil Z - 1) := by
      exact (SingularSeries.liuSingularSeriesTruncated_pos N (Nat.ceil Z - 1)).le
    have hVnonneg : 0 ≤ goldbachB10PrimeProduct N Z :=
      GoldbachLiuProductBridge.product_nonneg _hEven
    have hMul2 :
        goldbachB10PrimeProduct N Z * Real.log Z ≤
          2 * SingularSeries.liuSingularSeriesTruncated N (Nat.ceil Z - 1) *
            (1 + δ) *
            (Real.exp (-Real.eulerMascheroniConstant) +
              |C| / Real.log (((Nat.ceil Z - 1 : ℕ) : ℝ))) := by
      calc
        goldbachB10PrimeProduct N Z * Real.log Z
          ≤ goldbachB10PrimeProduct N Z *
              ((1 + δ) * Real.log (((Nat.ceil Z - 1 : ℕ) : ℝ))) :=
            mul_le_mul_of_nonneg_left hLogTransport hVnonneg
        _ = (goldbachB10PrimeProduct N Z * Real.log (((Nat.ceil Z - 1 : ℕ) : ℝ))) *
            (1 + δ) := by ring
        _ ≤ (2 * SingularSeries.liuSingularSeriesTruncated N (Nat.ceil Z - 1) *
            (Real.exp (-Real.eulerMascheroniConstant) +
              |C| / Real.log (((Nat.ceil Z - 1 : ℕ) : ℝ)))) * (1 + δ) :=
            mul_le_mul_of_nonneg_right hPrimeUpper (by positivity)
        _ = _ := by ring
    have hErrorFactor :
        Real.exp (-Real.eulerMascheroniConstant) +
            |C| / Real.log (((Nat.ceil Z - 1 : ℕ) : ℝ)) ≤
          Real.exp (-Real.eulerMascheroniConstant) * (1 + δ) := by
      linarith only [hErrTransport]
    have hliuNonneg := (SingularSeries.liuSingularSeries_pos N).le
    -- Pay the logarithm, Mertens error, and finite truncation by one factor
    -- `1 + δ` each, then use the chosen cubic budget.
    calc
      goldbachB10PrimeProduct N Z * Real.log Z
        ≤ 2 * SingularSeries.liuSingularSeriesTruncated N (Nat.ceil Z - 1) *
            (1 + δ) * (Real.exp (-Real.eulerMascheroniConstant) +
              |C| / Real.log (((Nat.ceil Z - 1 : ℕ) : ℝ))) := hMul2
      _ ≤ 2 * SingularSeries.liuSingularSeriesTruncated N (Nat.ceil Z - 1) *
            (1 + δ) * (Real.exp (-Real.eulerMascheroniConstant) * (1 + δ)) :=
          mul_le_mul_of_nonneg_left hErrorFactor (by positivity)
      _ = 2 * Real.exp (-Real.eulerMascheroniConstant) * (1 + δ) ^ 2 *
            SingularSeries.liuSingularSeriesTruncated N (Nat.ceil Z - 1) := by ring
      _ ≤ 2 * Real.exp (-Real.eulerMascheroniConstant) * (1 + δ) ^ 2 *
            ((1 + δ) * SingularSeries.liuSingularSeries N) :=
          mul_le_mul_of_nonneg_left hliuTrunc (by positivity)
      _ = 2 * Real.exp (-Real.eulerMascheroniConstant) * (1 + δ) ^ 3 *
            SingularSeries.liuSingularSeries N := by ring
      _ ≤ 2 * Real.exp (-Real.eulerMascheroniConstant) * (1 + η) *
            SingularSeries.liuSingularSeries N := by gcongr

theorem goldbachB10BoundingSieve_sieveProductPrimeFactors_log_le_liuSingularSeries
    (η : ℝ) (hη : 0 < η) :
    ∃ Z₀ : ℝ, 2 ≤ Z₀ ∧ ∀ (N : ℕ), 4 ≤ N → ∀ hEven : Even N,
      ∀ ε b c X Z : ℝ, Z₀ ≤ Z →
        AnalyticNumberTheory.Sieve.sieveProductPrimeFactors
            (goldbachB10BoundingSieve N hEven ε b c Z X) *
            Real.log Z ≤
          2 * Real.exp (-Real.eulerMascheroniConstant) * (1 + η) *
            SingularSeries.liuSingularSeries N := by
  obtain ⟨Z₀, hZ₀, hmain⟩ := goldbachB10PrimeProduct_log_le_liuSingularSeries η hη
  refine ⟨Z₀, hZ₀, ?_⟩
  intro N hN hEven ε b c X Z hZ
  rw [← goldbachB10PrimeProduct_eq_sieveProductPrimeFactors N hEven ε b c Z X]
  exact hmain N hN hEven Z hZ

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig