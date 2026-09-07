import MathlibNt.SieveTheory.LiLiuGoldbachB10FibreSieve
import MathlibNt.SieveTheory.LiuSingularSeries
import MathlibNt.SieveTheory.MertensTheorem

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
  have hE : 0 < Real.exp (-Real.eulerMascheroniConstant) := Real.exp_pos _
  have hL :
      |C| / (δ * Real.exp (-Real.eulerMascheroniConstant)) ≤
        Real.log (((Nat.ceil Z - 1 : ℕ) : ℝ)) :=
    B10SieveProduct_log_lower_of_two_mul_exp_le (by linarith) hZA
  have hδE : 0 < δ * Real.exp (-Real.eulerMascheroniConstant) := mul_pos hδ hE
  have hceil4r : (4 : ℝ) ≤ (Nat.ceil Z : ℝ) := hZ.trans (Nat.le_ceil Z)
  have hceil4 : 4 ≤ Nat.ceil Z := by exact_mod_cast hceil4r
  have harg1 : (1 : ℝ) < ((Nat.ceil Z - 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 1 < Nat.ceil Z - 1 by omega)
  have hlogpos : 0 < Real.log (((Nat.ceil Z - 1 : ℕ) : ℝ)) := Real.log_pos harg1
  have hmul := mul_le_mul_of_nonneg_left hL hδE.le
  have hcancel :
      (δ * Real.exp (-Real.eulerMascheroniConstant)) *
          (|C| / (δ * Real.exp (-Real.eulerMascheroniConstant))) = |C| := by
    field_simp [hδ.ne', (Real.exp_pos _).ne']
  have hbound' :
      (δ * Real.exp (-Real.eulerMascheroniConstant)) *
          (|C| / (δ * Real.exp (-Real.eulerMascheroniConstant))) ≤
      (δ * Real.exp (-Real.eulerMascheroniConstant)) *
        Real.log (((Nat.ceil Z - 1 : ℕ) : ℝ)) := hmul
  have hbound : |C| ≤
      (δ * Real.exp (-Real.eulerMascheroniConstant)) *
        Real.log (((Nat.ceil Z - 1 : ℕ) : ℝ)) := by
    simpa [hcancel] using hbound'
  exact (div_le_iff₀ hlogpos).2 <| by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hbound

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
  obtain ⟨C, hC⟩ := MertensTheorem.sieve_product_asymptotic
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
    have hzTrunc : 2 ≤ Nat.ceil Z - 1 := by omega
    have hlogArg1 : (1 : ℝ) < (((Nat.ceil Z - 1 : ℕ) : ℝ)) := by
      exact_mod_cast (show 1 < Nat.ceil Z - 1 by omega)
    have hlogArgPos : 0 < (((Nat.ceil Z - 1 : ℕ) : ℝ)) := by linarith
    have hlogPos : 0 < Real.log (((Nat.ceil Z - 1 : ℕ) : ℝ)) := Real.log_pos hlogArg1
    have hlogZPos : 0 < Real.log Z := Real.log_pos (by linarith)
    have hTnat1 : T + 1 ≤ Nat.ceil Z := by
      exact_mod_cast (hZT.trans (Nat.le_ceil Z))
    have hTnat : T ≤ Nat.ceil Z - 1 := by omega
    have hliuTrunc :
        SingularSeries.liuSingularSeriesTruncated N (Nat.ceil Z - 1) ≤
          (1 + δ) * SingularSeries.liuSingularSeries N := by
      exact hT (Nat.ceil Z - 1) hTnat N (by omega)
    have hsieveAbs :
        |goldbachB10PrimeProduct N Z -
            SingularSeries.singularSeriesTruncated N (Nat.ceil Z - 1) *
              Real.exp (-Real.eulerMascheroniConstant) /
                Real.log (((Nat.ceil Z - 1 : ℕ) : ℝ))| ≤
          |C| * SingularSeries.singularSeriesTruncated N (Nat.ceil Z - 1) /
            (Real.log (((Nat.ceil Z - 1 : ℕ) : ℝ))) ^ 2 := by
      have hbase := hC N (Nat.ceil Z) hzNat _hEven hN
      calc
        |goldbachB10PrimeProduct N Z -
            SingularSeries.singularSeriesTruncated N (Nat.ceil Z - 1) *
              Real.exp (-Real.eulerMascheroniConstant) /
                Real.log (((Nat.ceil Z - 1 : ℕ) : ℝ))|
          = |MertensTheorem.goldbachSieveProduct N (Nat.ceil Z) -
              SingularSeries.singularSeriesTruncated N (Nat.ceil Z - 1) *
                Real.exp (-Real.eulerMascheroniConstant) /
                  Real.log (((Nat.ceil Z - 1 : ℕ) : ℝ))| := by
              rfl
        _ ≤ C * SingularSeries.singularSeriesTruncated N (Nat.ceil Z - 1) /
              (Real.log (((Nat.ceil Z - 1 : ℕ) : ℝ))) ^ 2 := hbase
        _ ≤ |C| * SingularSeries.singularSeriesTruncated N (Nat.ceil Z - 1) /
              (Real.log (((Nat.ceil Z - 1 : ℕ) : ℝ))) ^ 2 := by
              have hSpos :
                  0 < SingularSeries.singularSeriesTruncated N (Nat.ceil Z - 1) :=
                SingularSeries.singularSeriesTruncated_pos N (Nat.ceil Z - 1) (by omega)
              have hterm :
                  0 ≤ SingularSeries.singularSeriesTruncated N (Nat.ceil Z - 1) /
                    (Real.log (((Nat.ceil Z - 1 : ℕ) : ℝ))) ^ 2 := by
                positivity
              have hCabs :
                  C * (SingularSeries.singularSeriesTruncated N (Nat.ceil Z - 1) /
                      (Real.log (((Nat.ceil Z - 1 : ℕ) : ℝ))) ^ 2) ≤
                    |C| * (SingularSeries.singularSeriesTruncated N (Nat.ceil Z - 1) /
                      (Real.log (((Nat.ceil Z - 1 : ℕ) : ℝ))) ^ 2) :=
                mul_le_mul_of_nonneg_right (le_abs_self C) hterm
              calc
                C * SingularSeries.singularSeriesTruncated N (Nat.ceil Z - 1) /
                    (Real.log (((Nat.ceil Z - 1 : ℕ) : ℝ))) ^ 2
                  = C * (SingularSeries.singularSeriesTruncated N (Nat.ceil Z - 1) /
                      (Real.log (((Nat.ceil Z - 1 : ℕ) : ℝ))) ^ 2) := by ring
                _ ≤ |C| * (SingularSeries.singularSeriesTruncated N (Nat.ceil Z - 1) /
                      (Real.log (((Nat.ceil Z - 1 : ℕ) : ℝ))) ^ 2) := hCabs
                _ = |C| * SingularSeries.singularSeriesTruncated N (Nat.ceil Z - 1) /
                      (Real.log (((Nat.ceil Z - 1 : ℕ) : ℝ))) ^ 2 := by ring
    have hLegacyToLiu :
        SingularSeries.singularSeriesTruncated N (Nat.ceil Z - 1) =
          2 * SingularSeries.liuSingularSeriesTruncated N (Nat.ceil Z - 1) :=
      SingularSeries.singularSeriesTruncated_eq_two_mul_liuSingularSeriesTruncated
        N (Nat.ceil Z - 1) _hEven hzTrunc
    have hPrimeUpper :
        goldbachB10PrimeProduct N Z ≤
          2 * SingularSeries.liuSingularSeriesTruncated N (Nat.ceil Z - 1) *
            (Real.exp (-Real.eulerMascheroniConstant) /
                Real.log (((Nat.ceil Z - 1 : ℕ) : ℝ)) +
              |C| / (Real.log (((Nat.ceil Z - 1 : ℕ) : ℝ))) ^ 2) := by
      have hsub :
          goldbachB10PrimeProduct N Z -
              SingularSeries.singularSeriesTruncated N (Nat.ceil Z - 1) *
                Real.exp (-Real.eulerMascheroniConstant) /
                  Real.log (((Nat.ceil Z - 1 : ℕ) : ℝ)) ≤
            |C| * SingularSeries.singularSeriesTruncated N (Nat.ceil Z - 1) /
              (Real.log (((Nat.ceil Z - 1 : ℕ) : ℝ))) ^ 2 := by
        exact (le_abs_self _).trans hsieveAbs
      have hupper :
          goldbachB10PrimeProduct N Z ≤
            SingularSeries.singularSeriesTruncated N (Nat.ceil Z - 1) *
              Real.exp (-Real.eulerMascheroniConstant) /
                Real.log (((Nat.ceil Z - 1 : ℕ) : ℝ)) +
              |C| * SingularSeries.singularSeriesTruncated N (Nat.ceil Z - 1) /
                (Real.log (((Nat.ceil Z - 1 : ℕ) : ℝ))) ^ 2 := by
        linarith
      rw [hLegacyToLiu] at hupper
      have hrew :
          2 * SingularSeries.liuSingularSeriesTruncated N (Nat.ceil Z - 1) *
              Real.exp (-Real.eulerMascheroniConstant) /
                Real.log (((Nat.ceil Z - 1 : ℕ) : ℝ)) +
            |C| * (2 * SingularSeries.liuSingularSeriesTruncated N (Nat.ceil Z - 1)) /
              (Real.log (((Nat.ceil Z - 1 : ℕ) : ℝ))) ^ 2 =
          2 * SingularSeries.liuSingularSeriesTruncated N (Nat.ceil Z - 1) *
            (Real.exp (-Real.eulerMascheroniConstant) /
                Real.log (((Nat.ceil Z - 1 : ℕ) : ℝ)) +
              |C| / (Real.log (((Nat.ceil Z - 1 : ℕ) : ℝ))) ^ 2) := by
        ring
      calc
        goldbachB10PrimeProduct N Z
          ≤ 2 * SingularSeries.liuSingularSeriesTruncated N (Nat.ceil Z - 1) *
              Real.exp (-Real.eulerMascheroniConstant) /
                Real.log (((Nat.ceil Z - 1 : ℕ) : ℝ)) +
            |C| * (2 * SingularSeries.liuSingularSeriesTruncated N (Nat.ceil Z - 1)) /
              (Real.log (((Nat.ceil Z - 1 : ℕ) : ℝ))) ^ 2 := hupper
        _ = 2 * SingularSeries.liuSingularSeriesTruncated N (Nat.ceil Z - 1) *
              (Real.exp (-Real.eulerMascheroniConstant) /
                  Real.log (((Nat.ceil Z - 1 : ℕ) : ℝ)) +
                |C| / (Real.log (((Nat.ceil Z - 1 : ℕ) : ℝ))) ^ 2) := hrew
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
    have hBracketNonneg :
        0 ≤ Real.exp (-Real.eulerMascheroniConstant) /
              Real.log (((Nat.ceil Z - 1 : ℕ) : ℝ)) +
            |C| / (Real.log (((Nat.ceil Z - 1 : ℕ) : ℝ))) ^ 2 := by
      positivity
    have hMul1 :
        goldbachB10PrimeProduct N Z * Real.log Z ≤
          2 * SingularSeries.liuSingularSeriesTruncated N (Nat.ceil Z - 1) *
            (Real.exp (-Real.eulerMascheroniConstant) /
                Real.log (((Nat.ceil Z - 1 : ℕ) : ℝ)) +
              |C| / (Real.log (((Nat.ceil Z - 1 : ℕ) : ℝ))) ^ 2) *
            ((1 + δ) * Real.log (((Nat.ceil Z - 1 : ℕ) : ℝ))) := by
      have hmul := mul_le_mul_of_nonneg_right hPrimeUpper hlogZPos.le
      exact hmul.trans <| by
        gcongr
    have hMul2 :
        goldbachB10PrimeProduct N Z * Real.log Z ≤
          2 * SingularSeries.liuSingularSeriesTruncated N (Nat.ceil Z - 1) *
            (1 + δ) *
            (Real.exp (-Real.eulerMascheroniConstant) +
              |C| / Real.log (((Nat.ceil Z - 1 : ℕ) : ℝ))) := by
      calc
        goldbachB10PrimeProduct N Z * Real.log Z
          ≤ 2 * SingularSeries.liuSingularSeriesTruncated N (Nat.ceil Z - 1) *
              (Real.exp (-Real.eulerMascheroniConstant) /
                  Real.log (((Nat.ceil Z - 1 : ℕ) : ℝ)) +
                |C| / (Real.log (((Nat.ceil Z - 1 : ℕ) : ℝ))) ^ 2) *
              ((1 + δ) * Real.log (((Nat.ceil Z - 1 : ℕ) : ℝ))) := hMul1
        _ = 2 * SingularSeries.liuSingularSeriesTruncated N (Nat.ceil Z - 1) *
              (1 + δ) *
              (Real.exp (-Real.eulerMascheroniConstant) +
                |C| / Real.log (((Nat.ceil Z - 1 : ℕ) : ℝ))) := by
              field_simp [hlogPos.ne']
    have hMul3 :
        goldbachB10PrimeProduct N Z * Real.log Z ≤
          2 * SingularSeries.liuSingularSeriesTruncated N (Nat.ceil Z - 1) *
            Real.exp (-Real.eulerMascheroniConstant) * (1 + δ) ^ 2 := by
      have hsum :
          Real.exp (-Real.eulerMascheroniConstant) +
              |C| / Real.log (((Nat.ceil Z - 1 : ℕ) : ℝ)) ≤
            Real.exp (-Real.eulerMascheroniConstant) + δ * Real.exp (-Real.eulerMascheroniConstant) := by
        linarith
      calc
        goldbachB10PrimeProduct N Z * Real.log Z
          ≤ 2 * SingularSeries.liuSingularSeriesTruncated N (Nat.ceil Z - 1) *
              (1 + δ) *
              (Real.exp (-Real.eulerMascheroniConstant) +
                |C| / Real.log (((Nat.ceil Z - 1 : ℕ) : ℝ))) := hMul2
        _ ≤ 2 * SingularSeries.liuSingularSeriesTruncated N (Nat.ceil Z - 1) *
              (1 + δ) *
              (Real.exp (-Real.eulerMascheroniConstant) +
                δ * Real.exp (-Real.eulerMascheroniConstant)) := by
              gcongr
        _ = 2 * SingularSeries.liuSingularSeriesTruncated N (Nat.ceil Z - 1) *
              Real.exp (-Real.eulerMascheroniConstant) * (1 + δ) ^ 2 := by
              ring
    have hCoeffNonneg :
        0 ≤ 2 * Real.exp (-Real.eulerMascheroniConstant) * (1 + δ) ^ 2 := by
      positivity
    have hMul4 :
        goldbachB10PrimeProduct N Z * Real.log Z ≤
          2 * Real.exp (-Real.eulerMascheroniConstant) * (1 + δ) ^ 3 *
            SingularSeries.liuSingularSeries N := by
      calc
        goldbachB10PrimeProduct N Z * Real.log Z
          ≤ 2 * SingularSeries.liuSingularSeriesTruncated N (Nat.ceil Z - 1) *
              Real.exp (-Real.eulerMascheroniConstant) * (1 + δ) ^ 2 := hMul3
        _ ≤ 2 * ((1 + δ) * SingularSeries.liuSingularSeries N) *
              Real.exp (-Real.eulerMascheroniConstant) * (1 + δ) ^ 2 := by
              gcongr
        _ = 2 * Real.exp (-Real.eulerMascheroniConstant) * (1 + δ) ^ 3 *
              SingularSeries.liuSingularSeries N := by
              ring
    have hfinalCoeff :
        2 * Real.exp (-Real.eulerMascheroniConstant) * (1 + δ) ^ 3 *
            SingularSeries.liuSingularSeries N ≤
          2 * Real.exp (-Real.eulerMascheroniConstant) * (1 + η) *
            SingularSeries.liuSingularSeries N := by
      have hliuNonneg : 0 ≤ SingularSeries.liuSingularSeries N := by
        exact (SingularSeries.liuSingularSeries_pos N).le
      have hcoef :
          2 * Real.exp (-Real.eulerMascheroniConstant) * (1 + δ) ^ 3 ≤
            2 * Real.exp (-Real.eulerMascheroniConstant) * (1 + η) := by
        gcongr
      exact mul_le_mul_of_nonneg_right hcoef hliuNonneg
    exact hMul4.trans hfinalCoeff

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