import MathlibNt.SieveTheory.LiLiuGoldbachS2PaidUpper
import MathlibNt.Analysis.LogScaleAbsorption
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Data.Nat.Factors
import Mathlib.Order.Filter.AtTopBot.Basic
import MathlibNt.SieveTheory.LiLiuGoldbachB10SieveProduct
import MathlibNt.SieveTheory.LiLiuGoldbachS2MainMassUpper
import MathlibNt.SieveTheory.LiuPanPrimePowerCharacters

noncomputable section

open Filter
open scoped BigOperators

open MathlibNt.SieveTheory.LiuWeight

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

set_option autoImplicit false
set_option maxHeartbeats 400000

private theorem S2NormalizedUpper_sigma_pos {δ : ℝ} (hδ : 0 < δ) :
    0 < min (δ / 112) 1 := by
  refine lt_min ?_ zero_lt_one
  positivity

private theorem S2NormalizedUpper_main_coefficient_le
    {K η δ : ℝ}
    (_hK0 : 0 ≤ K) (hK1 : K ≤ 1) (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (hηδ : 112 * η ≤ δ) :
    8 * (1 + η) ^ 2 * (K + η) ≤ 8 * K + δ / 2 := by
  have hη2 : η ^ 2 ≤ η := by
    nlinarith [sq_nonneg (η - 1)]
  have hη3 : η ^ 3 ≤ η := by
    have hmul := mul_le_mul_of_nonneg_left hη2 hη0
    nlinarith
  have hKη : K * η ≤ η := by
    nlinarith
  have hKη2 : K * η ^ 2 ≤ η := by
    have htmp : K * η ^ 2 ≤ η ^ 2 := by nlinarith
    exact htmp.trans hη2
  have hmain :
      16 * K * η + 8 * K * η ^ 2 + 8 * η + 16 * η ^ 2 + 8 * η ^ 3 ≤ 56 * η := by
    nlinarith
  calc
    8 * (1 + η) ^ 2 * (K + η)
      = 8 * K + (16 * K * η + 8 * K * η ^ 2 + 8 * η + 16 * η ^ 2 + 8 * η ^ 3) := by
          ring
    _ ≤ 8 * K + 56 * η := by gcongr
    _ ≤ 8 * K + δ / 2 := by
          have h56 : 56 * η ≤ δ / 2 := by nlinarith [hηδ]
          linarith

private theorem S2NormalizedUpper_quarterCutoff_large_eventually
    (K : ℝ) (_hK : 0 < K) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      K ≤ (N : ℝ) ^ ((1 : ℝ) / 4) := by
  have hpow :
      Tendsto (fun N : ℕ => (N : ℝ) ^ ((1 : ℝ) / 4)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < (1 : ℝ) / 4)).comp
      tendsto_natCast_atTop_atTop
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp
    (hpow.eventually (eventually_ge_atTop K))
  refine ⟨max 4 N₀, le_max_left _ _, ?_⟩
  intro N hN
  exact hN₀ N ((le_max_right _ _).trans hN)

private theorem S2NormalizedUpper_paid_error_absorb_eventually
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

private theorem S2NormalizedUpper_quarterPower_absorb_eventually
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      2 * (N : ℝ) ^ ((1 : ℝ) / 4) ≤
        δ * SingularSeries.liuUniversalProduct * (N : ℝ) /
          Real.log (N : ℝ) ^ (2 : ℝ) := by
  have hcore :
      Tendsto (fun N : ℕ =>
        (2 * Real.log (N : ℝ) ^ (2 : ℝ)) / (N : ℝ) ^ ((3 : ℝ) / 4))
        atTop (nhds 0) := by
    have hsmall :
        Tendsto (fun N : ℕ =>
          Real.log (N : ℝ) ^ (2 : ℝ) / (N : ℝ) ^ ((3 : ℝ) / 4))
          atTop (nhds 0) := by
      exact
        ((isLittleO_log_rpow_rpow_atTop (2 : ℝ)
          (by norm_num : (0 : ℝ) < (3 : ℝ) / 4)).tendsto_div_nhds_zero).comp
            tendsto_natCast_atTop_atTop
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hsmall.const_mul 2
  have hδU : 0 < δ * SingularSeries.liuUniversalProduct := by
    exact mul_pos hδ SingularSeries.liuUniversalProduct_pos
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp
    (hcore.eventually (Metric.ball_mem_nhds 0 hδU))
  refine ⟨max 4 N₁, le_max_left _ _, ?_⟩
  intro N hN
  have hN₁' : N₁ ≤ N := (le_max_right _ _).trans hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlogNpos : 0 < Real.log (N : ℝ) := Real.log_pos (by
    exact_mod_cast (show 1 < N by omega))
  have hpowPos : 0 < (N : ℝ) ^ ((3 : ℝ) / 4) := Real.rpow_pos_of_pos hNpos _
  have hlogSqPos : 0 < Real.log (N : ℝ) ^ (2 : ℝ) := Real.rpow_pos_of_pos hlogNpos 2
  have hsmallN :
      (2 * Real.log (N : ℝ) ^ (2 : ℝ)) / (N : ℝ) ^ ((3 : ℝ) / 4) ≤
        δ * SingularSeries.liuUniversalProduct := by
    have hdist : dist ((2 * Real.log (N : ℝ) ^ (2 : ℝ)) / (N : ℝ) ^ ((3 : ℝ) / 4)) 0 <
        δ * SingularSeries.liuUniversalProduct := hN₁ N hN₁'
    have hnonneg :
        0 ≤ (2 * Real.log (N : ℝ) ^ (2 : ℝ)) / (N : ℝ) ^ ((3 : ℝ) / 4) := by
      positivity
    rw [Real.dist_eq] at hdist
    exact (lt_of_le_of_lt (by simpa [abs_of_nonneg hnonneg] using (le_abs_self
      ((2 * Real.log (N : ℝ) ^ (2 : ℝ)) / (N : ℝ) ^ ((3 : ℝ) / 4)))) hdist).le
  have hbound :
      2 * Real.log (N : ℝ) ^ (2 : ℝ) ≤
        δ * SingularSeries.liuUniversalProduct * (N : ℝ) ^ ((3 : ℝ) / 4) := by
    exact (div_le_iff₀ hpowPos).mp hsmallN
  have hmul :
      2 * (N : ℝ) ^ ((1 : ℝ) / 4) * Real.log (N : ℝ) ^ (2 : ℝ) ≤
        δ * SingularSeries.liuUniversalProduct * (N : ℝ) := by
    have htmp := mul_le_mul_of_nonneg_left hbound
      (by positivity : 0 ≤ (N : ℝ) ^ ((1 : ℝ) / 4))
    have hpow :
        (N : ℝ) ^ ((3 : ℝ) / 4) * (N : ℝ) ^ ((1 : ℝ) / 4) = (N : ℝ) := by
      rw [← Real.rpow_add hNpos]
      norm_num
    calc
      2 * (N : ℝ) ^ ((1 : ℝ) / 4) * Real.log (N : ℝ) ^ (2 : ℝ)
        = (N : ℝ) ^ ((1 : ℝ) / 4) * (2 * Real.log (N : ℝ) ^ (2 : ℝ)) := by ring
      _ ≤ (N : ℝ) ^ ((1 : ℝ) / 4) *
            (δ * SingularSeries.liuUniversalProduct * (N : ℝ) ^ ((3 : ℝ) / 4)) := htmp
      _ = δ * SingularSeries.liuUniversalProduct * (N : ℝ) := by
            calc
              (N : ℝ) ^ ((1 : ℝ) / 4) *
                  (δ * SingularSeries.liuUniversalProduct * (N : ℝ) ^ ((3 : ℝ) / 4))
                = δ * SingularSeries.liuUniversalProduct *
                    ((N : ℝ) ^ ((1 : ℝ) / 4) * (N : ℝ) ^ ((3 : ℝ) / 4)) := by ring
              _ = δ * SingularSeries.liuUniversalProduct * (N : ℝ) := by
                    rw [mul_comm ((N : ℝ) ^ ((1 : ℝ) / 4)), hpow]
  exact (le_div_iff₀ hlogSqPos).2 (by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hmul)

private theorem S2NormalizedUpper_smallPartner_absorb_eventually
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      (Nat.ceil ((N : ℝ) ^ ((1 : ℝ) / 4)) : ℝ) ≤
        δ * SingularSeries.liuUniversalProduct * (N : ℝ) /
          Real.log (N : ℝ) ^ (2 : ℝ) := by
  obtain ⟨NZ, hNZ4, hZlarge⟩ := S2NormalizedUpper_quarterCutoff_large_eventually 1 zero_lt_one
  obtain ⟨Npow, hNpow4, hpow⟩ := S2NormalizedUpper_quarterPower_absorb_eventually δ hδ
  refine ⟨max 4 (max NZ Npow), le_max_left _ _, ?_⟩
  intro N hN
  let Z : ℝ := (N : ℝ) ^ ((1 : ℝ) / 4)
  have hNZ' : NZ ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hNpow' : Npow ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  have hZ1 : 1 ≤ Z := by
    simpa [Z] using hZlarge N hNZ'
  have hceil : (Nat.ceil Z : ℝ) ≤ 2 * Z := by
    have hlt : (Nat.ceil Z : ℝ) < Z + 1 := Nat.ceil_lt_add_one (by positivity : 0 ≤ Z)
    have hle : (Nat.ceil Z : ℝ) ≤ Z + 1 := hlt.le
    have htwo : Z + 1 ≤ 2 * Z := by nlinarith
    exact hle.trans htwo
  calc
    (Nat.ceil Z : ℝ) ≤ 2 * Z := hceil
    _ ≤ δ * SingularSeries.liuUniversalProduct * (N : ℝ) /
          Real.log (N : ℝ) ^ (2 : ℝ) := by
            simpa [Z] using hpow N hNpow'

private theorem S2NormalizedUpper_primeFactors_absorb_eventually
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      (N.primeFactors.card : ℝ) ≤
        δ * SingularSeries.liuUniversalProduct * (N : ℝ) /
          Real.log (N : ℝ) ^ (2 : ℝ) := by
  have hcore :
      Tendsto (fun N : ℕ =>
        Real.log (N : ℝ) ^ (3 : ℝ) / (N : ℝ) ^ (1 : ℝ)) atTop (nhds 0) := by
    exact
      ((isLittleO_log_rpow_rpow_atTop (3 : ℝ)
        (by norm_num : (0 : ℝ) < 1)).tendsto_div_nhds_zero).comp
          tendsto_natCast_atTop_atTop
  have hδU2 : 0 < δ * SingularSeries.liuUniversalProduct * Real.log 2 := by
    exact mul_pos (mul_pos hδ SingularSeries.liuUniversalProduct_pos) (Real.log_pos (by norm_num))
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp
    (hcore.eventually (Metric.ball_mem_nhds 0 hδU2))
  refine ⟨max 4 N₁, le_max_left _ _, ?_⟩
  intro N hN
  have hN₁' : N₁ ≤ N := (le_max_right _ _).trans hN
  have hN4 : 4 ≤ N := (le_max_left _ _).trans hN
  have hpf :
      (N.primeFactors.card : ℝ) ≤ Real.log (N : ℝ) / Real.log 2 :=
    primeFactors_card_cast_le_log (by omega)
  have hlogNpos : 0 < Real.log (N : ℝ) := Real.log_pos (by
    exact_mod_cast (show 1 < N by omega))
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogSqPos : 0 < Real.log (N : ℝ) ^ (2 : ℝ) := Real.rpow_pos_of_pos hlogNpos 2
  have hpow3 :
      Real.log (N : ℝ) ^ (3 : ℝ) =
        Real.log (N : ℝ) * Real.log (N : ℝ) ^ (2 : ℝ) := by
    rw [show (3 : ℝ) = 1 + 2 by norm_num, Real.rpow_add hlogNpos, Real.rpow_one]
  have hmain :
      Real.log (N : ℝ) * Real.log (N : ℝ) ^ (2 : ℝ) ≤
        (δ * SingularSeries.liuUniversalProduct * Real.log 2) * (N : ℝ) := by
    have hsmallN :
        Real.log (N : ℝ) ^ (3 : ℝ) / (N : ℝ) ≤
          δ * SingularSeries.liuUniversalProduct * Real.log 2 := by
      have hdist : dist (Real.log (N : ℝ) ^ (3 : ℝ) / (N : ℝ) ^ (1 : ℝ)) 0 <
          δ * SingularSeries.liuUniversalProduct * Real.log 2 := hN₁ N hN₁'
      have hnonneg : 0 ≤ Real.log (N : ℝ) ^ (3 : ℝ) / (N : ℝ) ^ (1 : ℝ) := by
        positivity
      rw [Real.dist_eq] at hdist
      have hlt :
          Real.log (N : ℝ) ^ (3 : ℝ) / (N : ℝ) ^ (1 : ℝ) <
            δ * SingularSeries.liuUniversalProduct * Real.log 2 :=
        lt_of_le_of_lt (by simpa [abs_of_nonneg hnonneg] using
          (le_abs_self (Real.log (N : ℝ) ^ (3 : ℝ) / (N : ℝ) ^ (1 : ℝ)))) hdist
      simpa [Real.rpow_one] using hlt.le
    have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hbound :
        Real.log (N : ℝ) ^ (3 : ℝ) ≤
          (δ * SingularSeries.liuUniversalProduct * Real.log 2) * (N : ℝ) :=
      (div_le_iff₀ hNpos).mp hsmallN
    simpa [hpow3] using hbound
  have hlog :
      Real.log (N : ℝ) / Real.log 2 ≤
        δ * SingularSeries.liuUniversalProduct * (N : ℝ) /
          Real.log (N : ℝ) ^ (2 : ℝ) := by
    have hstep :
        Real.log (N : ℝ) ≤
          ((δ * SingularSeries.liuUniversalProduct * Real.log 2) * (N : ℝ)) /
            Real.log (N : ℝ) ^ (2 : ℝ) := by
      exact (le_div_iff₀ hlogSqPos).2 hmain
    exact (div_le_iff₀ hlog2pos).2 (by
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hstep)
  exact hpf.trans hlog

/-- The literal main-mass endpoint sum is definitionally the switched main mass
at cutoff `T = N^τ`. -/
theorem goldbachS2MainMassUpperSum_eq_goldbachS2SwitchedMainMass
    (N : ℕ) (τ : ℝ) :
    goldbachS2MainMassUpperSum N τ =
      goldbachS2SwitchedMainMass N ((N : ℝ) ^ τ) := by
  rfl

/-- The actual switched `S2` sieve product is the same normalized Euler product
already controlled in the mature `B10` library. -/
theorem goldbachS2SwitchedBoundingSieve_sieveProductPrimeFactors_log_le_liuSingularSeries
    (η : ℝ) (hη : 0 < η) :
    ∃ Z₀ : ℝ, 2 ≤ Z₀ ∧ ∀ (N : ℕ), 4 ≤ N → ∀ hEven : Even N,
      ∀ T Z : ℝ, Z₀ ≤ Z →
        AnalyticNumberTheory.Sieve.sieveProductPrimeFactors
            (goldbachS2SwitchedBoundingSieve N hEven T Z) *
            Real.log Z ≤
          2 * Real.exp (-Real.eulerMascheroniConstant) * (1 + η) *
            SingularSeries.liuSingularSeries N := by
  obtain ⟨Z₀, hZ₀, hmain⟩ := goldbachB10PrimeProduct_log_le_liuSingularSeries η hη
  refine ⟨Z₀, hZ₀, ?_⟩
  intro N hN hEven T Z hZ
  rw [← goldbachS2PrimeProduct_eq_sieveProductPrimeFactors N hEven T Z]
  exact hmain N hN hEven Z hZ

/-- The real switched `S2` count at `Z = N^(1/4)` is fully normalized against
the Liu singular series and the genuine `S2` main-mass logarithmic kernel. -/
theorem goldbachS2SwitchedSiftedCount_normalized_upper_nine_nineteen_sub
    (δ ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε) (hεu : ε < (2 : ℝ) / 15) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → ∀ _ : Even N,
      let Z : ℝ := (N : ℝ) ^ ((1 : ℝ) / 4)
      let T : ℝ := (N : ℝ) ^ ((9 : ℝ) / 19 - ε)
      (goldbachS2SwitchedSiftedCount N T Z : ℝ) ≤
        (8 * Real.log ((1 - ((9 : ℝ) / 19 - ε)) / ((9 : ℝ) / 19 - ε)) + δ) *
          SingularSeries.liuSingularSeries N * (N : ℝ) /
            Real.log (N : ℝ) ^ (2 : ℝ) := by
  let η : ℝ := min (δ / 112) 1
  let τ : ℝ := (9 : ℝ) / 19 - ε
  let K : ℝ := Real.log ((1 - τ) / τ)
  have hη : 0 < η := S2NormalizedUpper_sigma_pos hδ
  have hη0 : 0 ≤ η := hη.le
  have hη1 : η ≤ 1 := by
    dsimp [η]
    exact min_le_right _ _
  have hηδ : 112 * η ≤ δ := by
    dsimp [η]
    by_cases hsmall : δ / 112 ≤ 1
    · rw [min_eq_left hsmall]
      nlinarith
    · rw [min_eq_right (le_of_lt (lt_of_not_ge hsmall))]
      nlinarith
  have hτlo : (1 : ℝ) / 3 < τ := by
    dsimp [τ]
    nlinarith
  have hτhi : τ < (1 : ℝ) / 2 := by
    dsimp [τ]
    nlinarith
  have hτpos : 0 < τ := by linarith
  have hK0 : 0 ≤ K := by
    dsimp [K]
    have hratio : 1 ≤ (1 - τ) / τ := by
      exact (one_le_div₀ hτpos).2 (by linarith)
    exact Real.log_nonneg hratio
  have hK1 : K ≤ 1 := by
    dsimp [K]
    have hratioPos : 0 < (1 - τ) / τ := by
      exact div_pos (by linarith) hτpos
    have hratioLt : (1 - τ) / τ < Real.exp 1 := by
      have hlt2 : (1 - τ) / τ < 2 := by
        exact (div_lt_iff₀ hτpos).2 (by linarith)
      exact lt_trans hlt2 Real.exp_one_gt_two
    exact (Real.log_le_iff_le_exp hratioPos).2 hratioLt.le
  obtain ⟨C, hC, B, hB, hpaid⟩ := goldbachS2SwitchedSiftedCount_upper_paid η hη
  obtain ⟨Npaid, hNpaid4, hpaidN⟩ := hpaid ε hε hεu
  obtain ⟨Z₀, hZ₀, hsieve⟩ :=
    goldbachS2SwitchedBoundingSieve_sieveProductPrimeFactors_log_le_liuSingularSeries η hη
  obtain ⟨Nmass, hNmass4, hmass⟩ :=
    goldbachS2MainMassUpper_nine_nineteen_sub η ε hη hε hεu
  obtain ⟨NZ, hNZ4, hZlarge⟩ :=
    S2NormalizedUpper_quarterCutoff_large_eventually (max 2 Z₀)
      (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (le_max_left _ _))
  obtain ⟨Nerr, hNerr4, herr⟩ :=
    S2NormalizedUpper_paid_error_absorb_eventually C (δ / 2) hC (by positivity)
  let N₀ : ℕ := max 4 (max Npaid (max Nmass (max NZ Nerr)))
  refine ⟨N₀, le_max_left _ _, ?_⟩
  intro N hN hEven
  let Z : ℝ := (N : ℝ) ^ ((1 : ℝ) / 4)
  let T : ℝ := (N : ℝ) ^ τ
  let S := goldbachS2SwitchedBoundingSieve N hEven T Z
  let V := AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S
  have hN4 : 4 ≤ N := (le_max_left _ _).trans hN
  have hNpack : max Npaid (max Nmass (max NZ Nerr)) ≤ N := (le_max_right _ _).trans hN
  have hNpaid' : Npaid ≤ N := (le_max_left _ _).trans hNpack
  have hNrest₁ : max Nmass (max NZ Nerr) ≤ N := (le_max_right _ _).trans hNpack
  have hNmass' : Nmass ≤ N := (le_max_left _ _).trans hNrest₁
  have hNrest₂ : max NZ Nerr ≤ N := (le_max_right _ _).trans hNrest₁
  have hNZ' : NZ ≤ N := (le_max_left _ _).trans hNrest₂
  have hNerr' : Nerr ≤ N := (le_max_right _ _).trans hNrest₂
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlogNpos : 0 < Real.log (N : ℝ) := Real.log_pos (by
    exact_mod_cast (show 1 < N by omega))
  have hZ₀' : Z₀ ≤ Z := by
    have hbig : max 2 Z₀ ≤ Z := by simpa [Z] using hZlarge N hNZ'
    exact (le_max_right _ _).trans hbig
  have hpaidBound :
      (goldbachS2SwitchedSiftedCount N T Z : ℝ) ≤
        goldbachS2SwitchedMainMass N T *
          (Real.exp Real.eulerMascheroniConstant * (1 + η)) * V +
        C * (N : ℝ) / Real.log (N : ℝ) ^ (4 : ℝ) := by
    simpa [Z, T, S, V, τ] using hpaidN N hNpaid' hEven
  have hVlog :
      V * Real.log Z ≤
        2 * Real.exp (-Real.eulerMascheroniConstant) * (1 + η) *
          SingularSeries.liuSingularSeries N := by
    simpa [Z, T, S, V] using hsieve N hN4 hEven T Z hZ₀'
  have hlogZ : Real.log Z = Real.log (N : ℝ) / 4 := by
    dsimp [Z]
    rw [Real.log_rpow hNpos]
    ring
  have hV :
      V ≤
        8 * Real.exp (-Real.eulerMascheroniConstant) * (1 + η) *
          SingularSeries.liuSingularSeries N / Real.log (N : ℝ) := by
    have htmp :
        V * (Real.log (N : ℝ) / 4) ≤
          2 * Real.exp (-Real.eulerMascheroniConstant) * (1 + η) *
            SingularSeries.liuSingularSeries N := by
      simpa [hlogZ] using hVlog
    have hmul :
        V * Real.log (N : ℝ) ≤
          8 * Real.exp (-Real.eulerMascheroniConstant) * (1 + η) *
            SingularSeries.liuSingularSeries N := by
      nlinarith
    exact (le_div_iff₀ hlogNpos).2 (by
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hmul)
  have hX :
      goldbachS2SwitchedMainMass N T ≤
        (K + η) * ((N : ℝ) / Real.log (N : ℝ)) := by
    simpa [T, K, τ, goldbachS2MainMassUpperSum_eq_goldbachS2SwitchedMainMass] using
      hmass N hNmass'
  have hMainStep :
      goldbachS2SwitchedMainMass N T *
          (Real.exp Real.eulerMascheroniConstant * (1 + η)) * V ≤
        8 * (1 + η) ^ 2 * SingularSeries.liuSingularSeries N *
          goldbachS2SwitchedMainMass N T / Real.log (N : ℝ) := by
    have hfacNonneg :
        0 ≤ goldbachS2SwitchedMainMass N T *
          (Real.exp Real.eulerMascheroniConstant * (1 + η)) := by
      have hmass := goldbachS2SwitchedMainMass_nonneg N T
      positivity
    have hmul :
        goldbachS2SwitchedMainMass N T *
            (Real.exp Real.eulerMascheroniConstant * (1 + η)) * V ≤
          goldbachS2SwitchedMainMass N T *
            (Real.exp Real.eulerMascheroniConstant * (1 + η)) *
            (8 * Real.exp (-Real.eulerMascheroniConstant) * (1 + η) *
              SingularSeries.liuSingularSeries N / Real.log (N : ℝ)) := by
      exact mul_le_mul_of_nonneg_left hV hfacNonneg
    calc
      goldbachS2SwitchedMainMass N T *
          (Real.exp Real.eulerMascheroniConstant * (1 + η)) * V
        ≤ goldbachS2SwitchedMainMass N T *
            (Real.exp Real.eulerMascheroniConstant * (1 + η)) *
            (8 * Real.exp (-Real.eulerMascheroniConstant) * (1 + η) *
              SingularSeries.liuSingularSeries N / Real.log (N : ℝ)) := hmul
      _ = 8 * (1 + η) ^ 2 * SingularSeries.liuSingularSeries N *
            goldbachS2SwitchedMainMass N T / Real.log (N : ℝ) := by
          rw [div_eq_mul_inv]
          have hexp :
              Real.exp Real.eulerMascheroniConstant *
                  Real.exp (-Real.eulerMascheroniConstant) = 1 := by
            rw [← Real.exp_add]
            norm_num
          calc
            goldbachS2SwitchedMainMass N T *
                (Real.exp Real.eulerMascheroniConstant * (1 + η)) *
                (8 * Real.exp (-Real.eulerMascheroniConstant) * (1 + η) *
                  SingularSeries.liuSingularSeries N * (Real.log (N : ℝ))⁻¹)
              = goldbachS2SwitchedMainMass N T *
                  ((Real.exp Real.eulerMascheroniConstant *
                    Real.exp (-Real.eulerMascheroniConstant)) *
                    (8 * (1 + η) ^ 2 * SingularSeries.liuSingularSeries N *
                      (Real.log (N : ℝ))⁻¹)) := by ring
            _ = 8 * (1 + η) ^ 2 * SingularSeries.liuSingularSeries N *
                  goldbachS2SwitchedMainMass N T / Real.log (N : ℝ) := by
                  rw [hexp]
                  ring
  have hMain :
      goldbachS2SwitchedMainMass N T *
          (Real.exp Real.eulerMascheroniConstant * (1 + η)) * V ≤
        (8 * K + δ / 2) * SingularSeries.liuSingularSeries N * (N : ℝ) /
          Real.log (N : ℝ) ^ (2 : ℝ) := by
    have hcoefNonneg :
        0 ≤ 8 * (1 + η) ^ 2 * SingularSeries.liuSingularSeries N /
          Real.log (N : ℝ) := by
      exact div_nonneg
        (mul_nonneg (by positivity) (SingularSeries.liuSingularSeries_pos N).le)
        hlogNpos.le
    have hmulX :=
      mul_le_mul_of_nonneg_left hX hcoefNonneg
    have hXstep :
        8 * (1 + η) ^ 2 * SingularSeries.liuSingularSeries N *
            goldbachS2SwitchedMainMass N T / Real.log (N : ℝ) ≤
          (8 * (1 + η) ^ 2 * (K + η)) * SingularSeries.liuSingularSeries N *
            (N : ℝ) / Real.log (N : ℝ) ^ (2 : ℝ) := by
      calc
        8 * (1 + η) ^ 2 * SingularSeries.liuSingularSeries N *
            goldbachS2SwitchedMainMass N T / Real.log (N : ℝ)
          = (8 * (1 + η) ^ 2 * SingularSeries.liuSingularSeries N /
              Real.log (N : ℝ)) * goldbachS2SwitchedMainMass N T := by ring
        _ ≤ (8 * (1 + η) ^ 2 * SingularSeries.liuSingularSeries N /
              Real.log (N : ℝ)) *
            ((K + η) * ((N : ℝ) / Real.log (N : ℝ))) := by
              simpa [mul_assoc, mul_left_comm, mul_comm] using hmulX
        _ = (8 * (1 + η) ^ 2 * (K + η)) * SingularSeries.liuSingularSeries N *
              (N : ℝ) / Real.log (N : ℝ) ^ (2 : ℝ) := by
              rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.rpow_add hlogNpos, Real.rpow_one]
              ring
    have hCoeff :
        8 * (1 + η) ^ 2 * (K + η) ≤ 8 * K + δ / 2 := by
      exact S2NormalizedUpper_main_coefficient_le hK0 hK1 hη0 hη1 hηδ
    let Y : ℝ :=
      SingularSeries.liuSingularSeries N * (N : ℝ) /
        Real.log (N : ℝ) ^ (2 : ℝ)
    have hScale :
        0 ≤ SingularSeries.liuSingularSeries N * (N : ℝ) /
          Real.log (N : ℝ) ^ (2 : ℝ) := by
      exact div_nonneg
        (mul_nonneg (SingularSeries.liuSingularSeries_pos N).le (by positivity))
        (by positivity)
    have hCoeffStep0 :
        (8 * (1 + η) ^ 2 * (K + η)) * Y ≤
          (8 * K + δ / 2) * Y := by
      exact mul_le_mul_of_nonneg_right hCoeff hScale
    have hCoeffStep :
        (8 * (1 + η) ^ 2 * (K + η)) * SingularSeries.liuSingularSeries N *
            (N : ℝ) / Real.log (N : ℝ) ^ (2 : ℝ) ≤
          (8 * K + δ / 2) * SingularSeries.liuSingularSeries N *
            (N : ℝ) / Real.log (N : ℝ) ^ (2 : ℝ) := by
      simpa [Y, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hCoeffStep0
    calc
      goldbachS2SwitchedMainMass N T *
          (Real.exp Real.eulerMascheroniConstant * (1 + η)) * V
        ≤ 8 * (1 + η) ^ 2 * SingularSeries.liuSingularSeries N *
            goldbachS2SwitchedMainMass N T / Real.log (N : ℝ) := hMainStep
      _ ≤ (8 * (1 + η) ^ 2 * (K + η)) * SingularSeries.liuSingularSeries N *
            (N : ℝ) / Real.log (N : ℝ) ^ (2 : ℝ) := hXstep
      _ ≤ (8 * K + δ / 2) * SingularSeries.liuSingularSeries N * (N : ℝ) /
            Real.log (N : ℝ) ^ (2 : ℝ) := by
            exact hCoeffStep
  have hErrU :
      C * (N : ℝ) / Real.log (N : ℝ) ^ (4 : ℝ) ≤
        (δ / 2) * SingularSeries.liuUniversalProduct * (N : ℝ) /
          Real.log (N : ℝ) ^ (2 : ℝ) := herr N hNerr'
  have hErr :
      C * (N : ℝ) / Real.log (N : ℝ) ^ (4 : ℝ) ≤
        (δ / 2) * SingularSeries.liuSingularSeries N * (N : ℝ) /
          Real.log (N : ℝ) ^ (2 : ℝ) := by
    have hδseries :
        (δ / 2) * SingularSeries.liuUniversalProduct ≤
          (δ / 2) * SingularSeries.liuSingularSeries N := by
      exact mul_le_mul_of_nonneg_left
        (SingularSeries.liuUniversalProduct_le_liuSingularSeries N) (by positivity)
    have hscale :
        0 ≤ (N : ℝ) / Real.log (N : ℝ) ^ (2 : ℝ) := by positivity
    have hstep :
        (δ / 2) * SingularSeries.liuUniversalProduct * (N : ℝ) /
            Real.log (N : ℝ) ^ (2 : ℝ) ≤
          (δ / 2) * SingularSeries.liuSingularSeries N * (N : ℝ) /
            Real.log (N : ℝ) ^ (2 : ℝ) := by
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
        (mul_le_mul_of_nonneg_right hδseries hscale)
    exact hErrU.trans hstep
  have hfinal :
      (goldbachS2SwitchedSiftedCount N T Z : ℝ) ≤
        (8 * K + δ) * SingularSeries.liuSingularSeries N * (N : ℝ) /
          Real.log (N : ℝ) ^ (2 : ℝ) := by
    have hsum :
        goldbachS2SwitchedMainMass N T *
            (Real.exp Real.eulerMascheroniConstant * (1 + η)) * V +
          C * (N : ℝ) / Real.log (N : ℝ) ^ (4 : ℝ) ≤
        (8 * K + δ / 2) * SingularSeries.liuSingularSeries N * (N : ℝ) /
            Real.log (N : ℝ) ^ (2 : ℝ) +
          (δ / 2) * SingularSeries.liuSingularSeries N * (N : ℝ) /
            Real.log (N : ℝ) ^ (2 : ℝ) := by
      exact add_le_add hMain hErr
    have hEq :
        (8 * K + δ / 2) * SingularSeries.liuSingularSeries N * (N : ℝ) /
            Real.log (N : ℝ) ^ (2 : ℝ) +
          (δ / 2) * SingularSeries.liuSingularSeries N * (N : ℝ) /
            Real.log (N : ℝ) ^ (2 : ℝ) =
        (8 * K + δ) * SingularSeries.liuSingularSeries N * (N : ℝ) /
          Real.log (N : ℝ) ^ (2 : ℝ) := by
      ring
    have hmid :
        goldbachS2SwitchedMainMass N T *
            (Real.exp Real.eulerMascheroniConstant * (1 + η)) * V +
          C * (N : ℝ) / Real.log (N : ℝ) ^ (4 : ℝ) ≤
        (8 * K + δ) * SingularSeries.liuSingularSeries N * (N : ℝ) /
          Real.log (N : ℝ) ^ (2 : ℝ) := by
      calc
        goldbachS2SwitchedMainMass N T *
            (Real.exp Real.eulerMascheroniConstant * (1 + η)) * V +
          C * (N : ℝ) / Real.log (N : ℝ) ^ (4 : ℝ)
          ≤ (8 * K + δ / 2) * SingularSeries.liuSingularSeries N * (N : ℝ) /
              Real.log (N : ℝ) ^ (2 : ℝ) +
            (δ / 2) * SingularSeries.liuSingularSeries N * (N : ℝ) /
              Real.log (N : ℝ) ^ (2 : ℝ) := hsum
        _ = (8 * K + δ) * SingularSeries.liuSingularSeries N * (N : ℝ) /
              Real.log (N : ℝ) ^ (2 : ℝ) := hEq
    exact hpaidBound.trans hmid
  simpa [Z, T, K, τ] using hfinal

/-- The genuine finite `S2` count inherits the normalized switched upper bound
after paying the small-partner loss and the prime-factor bad set. -/
theorem goldbachS2_normalized_upper_nine_nineteen_sub
    (δ ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε) (hεu : ε < (2 : ℝ) / 15) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → ∀ _ : Even N,
      (goldbachS2 (goldbachDifferenceCarrier N ε) N ((N : ℝ) ^ ((9 : ℝ) / 19 - ε)) : ℝ) ≤
        (8 * Real.log ((1 - ((9 : ℝ) / 19 - ε)) / ((9 : ℝ) / 19 - ε)) + δ) *
          SingularSeries.liuSingularSeries N * (N : ℝ) /
            Real.log (N : ℝ) ^ (2 : ℝ) := by
  obtain ⟨Nswitch, hNswitch4, hswitch⟩ :=
    goldbachS2SwitchedSiftedCount_normalized_upper_nine_nineteen_sub
      (δ / 2) ε (by positivity) hε hεu
  obtain ⟨Nceil, hNceil4, hceil⟩ :=
    S2NormalizedUpper_smallPartner_absorb_eventually (δ / 4) (by positivity)
  obtain ⟨Npf, hNpf4, hpf⟩ :=
    S2NormalizedUpper_primeFactors_absorb_eventually (δ / 4) (by positivity)
  let Naux : ℕ := max 2 ⌈1 / ε ^ (2 : ℕ)⌉₊
  let N₀ : ℕ := max 4 (max Nswitch (max Nceil (max Npf Naux)))
  refine ⟨N₀, le_max_left _ _, ?_⟩
  intro N hN hEven
  let Z : ℝ := (N : ℝ) ^ ((1 : ℝ) / 4)
  let T : ℝ := (N : ℝ) ^ ((9 : ℝ) / 19 - ε)
  have hN4 : 4 ≤ N := (le_max_left _ _).trans hN
  have hNpack : max Nswitch (max Nceil (max Npf Naux)) ≤ N :=
    (le_max_right _ _).trans hN
  have hNswitch' : Nswitch ≤ N := (le_max_left _ _).trans hNpack
  have hNrest : max Nceil (max Npf Naux) ≤ N := (le_max_right _ _).trans hNpack
  have hNceil' : Nceil ≤ N := (le_max_left _ _).trans hNrest
  have hNrest' : max Npf Naux ≤ N := (le_max_right _ _).trans hNrest
  have hNpf' : Npf ≤ N := (le_max_left _ _).trans hNrest'
  have hNaux' : Naux ≤ N := (le_max_right _ _).trans hNrest'
  have hN2 : 2 ≤ N := by omega
  have hε1 : ε < 1 := by linarith
  have hT : 0 < T := by
    dsimp [T]
    exact Real.rpow_pos_of_pos (by positivity : 0 < (N : ℝ)) _
  have hcube : (N : ℝ) < T ^ 3 := by
    have hN1 : (1 : ℝ) < N := by
      exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2) hN2)
    have hpow :
        (N : ℝ) ^ (1 : ℝ) < (N : ℝ) ^ ((((9 : ℝ) / 19 - ε) * (3 : ℝ))) := by
      exact Real.rpow_lt_rpow_of_exponent_lt hN1 (by nlinarith)
    have hpow3 : T ^ 3 = (N : ℝ) ^ ((((9 : ℝ) / 19 - ε) * (3 : ℝ))) := by
      dsimp [T]
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ N)]
      norm_num
    calc
      (N : ℝ) = (N : ℝ) ^ (1 : ℝ) := by simp
      _ < (N : ℝ) ^ ((((9 : ℝ) / 19 - ε) * (3 : ℝ))) := hpow
      _ = T ^ 3 := hpow3.symm
  have hsqrt : Real.sqrt N ≤ ε * N := by
    have hceil :
        1 / ε ^ (2 : ℕ) ≤ (N : ℝ) := by
      calc
        1 / ε ^ (2 : ℕ) ≤ (⌈1 / ε ^ (2 : ℕ)⌉₊ : ℝ) := Nat.le_ceil _
        _ ≤ N := by
          exact_mod_cast
            (show ⌈1 / ε ^ (2 : ℕ)⌉₊ ≤ N from (le_max_right _ _).trans hNaux')
    have hmul :
        ε ^ (2 : ℕ) * (1 / ε ^ (2 : ℕ)) ≤ ε ^ (2 : ℕ) * N :=
      mul_le_mul_of_nonneg_left hceil (by positivity)
    have hone : (1 : ℝ) ≤ ε ^ (2 : ℕ) * N := by
      have hεsqne : ε ^ (2 : ℕ) ≠ 0 := by positivity
      simpa [div_eq_mul_inv, hεsqne, mul_assoc, mul_left_comm, mul_comm] using hmul
    have hsq : (N : ℝ) ≤ (ε * N) ^ 2 := by
      have hmulN := mul_le_mul_of_nonneg_right hone (show 0 ≤ (N : ℝ) by positivity)
      simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hmulN
    have hsq' : (Real.sqrt N) ^ 2 ≤ (ε * N) ^ 2 := by
      simpa [Real.sq_sqrt (show (0 : ℝ) ≤ N by positivity)] using hsq
    have hright : 0 ≤ ε * N := by positivity
    nlinarith [Real.sqrt_nonneg (N : ℝ), hsq']
  have hbridge :
      goldbachS2 (goldbachDifferenceCarrier N ε) N T ≤
        (goldbachS2SwitchedSiftedCount N T Z : ℤ) +
          (Nat.ceil Z : ℤ) +
          (N.primeFactors.card : ℤ) := by
    exact goldbachS2_le_switchedSiftedCount_add_ceil_add_primeFactors
      N ε T Z hN2 hε hε1 hT hcube hsqrt
  have hbridgeR :
      (goldbachS2 (goldbachDifferenceCarrier N ε) N T : ℝ) ≤
        (goldbachS2SwitchedSiftedCount N T Z : ℝ) + (Nat.ceil Z : ℝ) +
          (N.primeFactors.card : ℝ) := by
    exact_mod_cast hbridge
  have hswitch' :
      (goldbachS2SwitchedSiftedCount N T Z : ℝ) ≤
        (8 * Real.log ((1 - ((9 : ℝ) / 19 - ε)) / ((9 : ℝ) / 19 - ε)) + δ / 2) *
          SingularSeries.liuSingularSeries N * (N : ℝ) /
            Real.log (N : ℝ) ^ (2 : ℝ) := by
    simpa [Z, T] using hswitch N hNswitch' hEven
  have hceilU :
      (Nat.ceil Z : ℝ) ≤
        (δ / 4) * SingularSeries.liuUniversalProduct * (N : ℝ) /
          Real.log (N : ℝ) ^ (2 : ℝ) := by
    simpa [Z] using hceil N hNceil'
  have hpfU :
      (N.primeFactors.card : ℝ) ≤
        (δ / 4) * SingularSeries.liuUniversalProduct * (N : ℝ) /
          Real.log (N : ℝ) ^ (2 : ℝ) := hpf N hNpf'
  have hseriesQuarter :
      (δ / 4) * SingularSeries.liuUniversalProduct ≤
        (δ / 4) * SingularSeries.liuSingularSeries N := by
    exact mul_le_mul_of_nonneg_left
      (SingularSeries.liuUniversalProduct_le_liuSingularSeries N) (by positivity)
  have hscale :
      0 ≤ (N : ℝ) / Real.log (N : ℝ) ^ (2 : ℝ) := by positivity
  have hceilS :
      (Nat.ceil Z : ℝ) ≤
        (δ / 4) * SingularSeries.liuSingularSeries N * (N : ℝ) /
          Real.log (N : ℝ) ^ (2 : ℝ) := by
    have hstep :
        (δ / 4) * SingularSeries.liuUniversalProduct * (N : ℝ) /
            Real.log (N : ℝ) ^ (2 : ℝ) ≤
          (δ / 4) * SingularSeries.liuSingularSeries N * (N : ℝ) /
            Real.log (N : ℝ) ^ (2 : ℝ) := by
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
        (mul_le_mul_of_nonneg_right hseriesQuarter hscale)
    exact hceilU.trans hstep
  have hpfS :
      (N.primeFactors.card : ℝ) ≤
        (δ / 4) * SingularSeries.liuSingularSeries N * (N : ℝ) /
          Real.log (N : ℝ) ^ (2 : ℝ) := by
    have hstep :
        (δ / 4) * SingularSeries.liuUniversalProduct * (N : ℝ) /
            Real.log (N : ℝ) ^ (2 : ℝ) ≤
          (δ / 4) * SingularSeries.liuSingularSeries N * (N : ℝ) /
            Real.log (N : ℝ) ^ (2 : ℝ) := by
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
        (mul_le_mul_of_nonneg_right hseriesQuarter hscale)
    exact hpfU.trans hstep
  have hsum :
      (goldbachS2SwitchedSiftedCount N T Z : ℝ) + (Nat.ceil Z : ℝ) +
          (N.primeFactors.card : ℝ) ≤
        (8 * Real.log ((1 - ((9 : ℝ) / 19 - ε)) / ((9 : ℝ) / 19 - ε)) + δ / 2) *
            SingularSeries.liuSingularSeries N * (N : ℝ) /
              Real.log (N : ℝ) ^ (2 : ℝ) +
          ((δ / 4) * SingularSeries.liuSingularSeries N * (N : ℝ) /
              Real.log (N : ℝ) ^ (2 : ℝ) +
            (δ / 4) * SingularSeries.liuSingularSeries N * (N : ℝ) /
              Real.log (N : ℝ) ^ (2 : ℝ)) := by
    nlinarith [hswitch', hceilS, hpfS]
  have hfinalEq :
      (8 * Real.log ((1 - ((9 : ℝ) / 19 - ε)) / ((9 : ℝ) / 19 - ε)) + δ / 2) *
          SingularSeries.liuSingularSeries N * (N : ℝ) /
            Real.log (N : ℝ) ^ (2 : ℝ) +
        ((δ / 4) * SingularSeries.liuSingularSeries N * (N : ℝ) /
            Real.log (N : ℝ) ^ (2 : ℝ) +
          (δ / 4) * SingularSeries.liuSingularSeries N * (N : ℝ) /
            Real.log (N : ℝ) ^ (2 : ℝ)) =
      (8 * Real.log ((1 - ((9 : ℝ) / 19 - ε)) / ((9 : ℝ) / 19 - ε)) + δ) *
          SingularSeries.liuSingularSeries N * (N : ℝ) /
            Real.log (N : ℝ) ^ (2 : ℝ) := by
    ring
  exact hbridgeR.trans <| hsum.trans_eq hfinalEq

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig