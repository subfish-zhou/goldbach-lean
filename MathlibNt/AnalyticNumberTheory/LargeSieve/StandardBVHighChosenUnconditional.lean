import MathlibNt.AnalyticNumberTheory.Vaughan.ProductionVaughanTypeIIHighConductorAllAspect
import MathlibNt.AnalyticNumberTheory.Vaughan.ProductionVaughanTypeIElementaryPeriodCauchy
import MathlibNt.AnalyticNumberTheory.LargeSieve.StandardBVAdaptiveSmallCutoff

/-!
# Unconditional chosen Standard-BV high-conductor source

This checker constructs the genuine chosen high-conductor source with explicit parameters.
-/

namespace AnalyticNumberTheory.LargeSieve

open Classical Finset Filter
open scoped BigOperators ArithmeticFunction Topology

noncomputable section
set_option maxHeartbeats 2400000

/-- Explicit Pan exponent for the chosen all-aspect Type-II payment. -/
def standardBVHighChosenUnconditionalTypeIIExponent (A : ℕ) : ℕ := 3 * A + 200

/-- Explicit conductor exponent for the chosen all-aspect Type-II payment. -/
def standardBVHighChosenUnconditionalTypeIIConductorExponent (A : ℕ) : ℕ :=
  2 * (A + 50)

/-- Both Vaughan cutoffs are the literal logarithmic conductor threshold. -/
def standardBVHighChosenUnconditionalTypeIICutoff (A N : ℕ) : ℕ :=
  logConductorThreshold N (standardBVHighChosenUnconditionalTypeIIConductorExponent A)

private theorem chosenTypeII_logPower_le_threshold_eventually (A : ℕ) :
    ∀ᶠ N : ℕ in Filter.atTop,
      Real.log (N : ℝ) ^ (2 * (A + 49)) ≤
        (standardBVHighChosenUnconditionalTypeIICutoff A N : ℝ) := by
  filter_upwards [eventually_ge_atTop (9 : ℕ)] with N hN
  let x : ℝ := Real.log (N : ℝ)
  let t : ℕ := A + 49
  have hx2 : 2 ≤ x := by
    dsimp [x]
    have he1 : Real.exp 1 < (3 : ℝ) :=
      Real.exp_one_lt_d9.trans (by norm_num)
    have he10 : 0 < Real.exp (1 : ℝ) := Real.exp_pos 1
    have h9 : Real.exp 2 < (9 : ℝ) := by
      rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
      nlinarith
    have hexp : Real.exp 2 < (N : ℝ) := h9.trans_le (by exact_mod_cast hN)
    exact (Real.lt_log_iff_exp_lt (by positivity : (0 : ℝ) < N)).2 hexp |>.le
  have hx0 : 0 ≤ x := hx2.trans' (by norm_num)
  have hxpow2 : 2 ≤ x ^ 2 := by nlinarith [sq_nonneg (x - 2)]
  have hp2 : 2 ≤ x ^ (2 * (t + 1)) := by
    rw [show 2 * (t + 1) = 2 * t + 2 by omega, pow_add]
    have hbase : 1 ≤ x ^ (2 * t) := one_le_pow₀ (by linarith)
    nlinarith [pow_nonneg hx0 (2 * t)]
  have hfloor := Nat.sub_one_lt_floor (x ^ (2 * (t + 1)))
  have hhalf : x ^ (2 * t) ≤ x ^ (2 * (t + 1)) - 1 := by
    rw [show 2 * (t + 1) = 2 * t + 2 by omega, pow_add]
    have hbase : 1 ≤ x ^ (2 * t) := one_le_pow₀ (by linarith)
    nlinarith [pow_nonneg hx0 (2 * t)]
  have hcast : x ^ (2 * t) ≤ (Nat.floor (x ^ (2 * (t + 1))) : ℝ) :=
    hhalf.trans hfloor.le
  simpa [standardBVHighChosenUnconditionalTypeIICutoff,
    standardBVHighChosenUnconditionalTypeIIConductorExponent, standardBVHighChosenUnconditionalTypeIIExponent,
    logConductorThreshold, x, t, Nat.cast_ofNat] using hcast

/-- The concrete active rectangle family has the advertised squared binary-log
cardinality budget. -/
theorem standardBVHighChosenUnconditionalTypeII_activeCard_le (A N : ℕ) :
    (vaughanTypeIIActiveCanonicalRectangles N
        (standardBVHighChosenUnconditionalTypeIICutoff A N)
        (standardBVHighChosenUnconditionalTypeIICutoff A N)).card ≤ (Nat.log2 N + 1) ^ 2 := by
  simpa [Nat.log2_eq_log_two] using
    card_vaughanTypeIIActiveCanonicalRectangles_le N
      (standardBVHighChosenUnconditionalTypeIICutoff A N)
      (standardBVHighChosenUnconditionalTypeIICutoff A N)

/-- Unconditional closure of exactly the chosen-parameter Type-II
high-conductor contribution. -/
theorem standardBVHighChosenUnconditional_typeII (A : ℕ) :
    let B := 3 * A + 200
    let C := 2 * (A + 50)
    let u : ℕ → ℕ := fun N => logConductorThreshold N C
    let v : ℕ → ℕ := fun N => logConductorThreshold N C
    ∃ K : ℝ, 0 < K ∧
      ∀ᶠ N : ℕ in Filter.atTop,
        let Q := MathlibNt.SieveTheory.LiuWeight.panModulusCutoff N (B : ℝ)
        4 * discreteAbelAmplifierPrefixMax N * conductorHarmonicFactor Q ^ 2 *
            highConductorVaughanTypeIIMean N Q C (u N) (v N) ≤
          K * (N : ℝ) / Real.log N ^ A := by
  dsimp only
  let K : ℝ := 1000000000000000000
  refine ⟨K, by norm_num [K], ?_⟩
  filter_upwards [eventually_ge_atTop (9 : ℕ),
    chosenTypeII_logPower_le_threshold_eventually A,
    log_pow_le_sqrt_eventually (3 * A + 200),
    log_pow_le_sqrt_eventually (2 * (3 * A + 200))] with N hN hRlower hQgrow hCgrow
  let B : ℕ := 3 * A + 200
  let C : ℕ := 2 * (A + 50)
  let R : ℕ := logConductorThreshold N C
  let Q := MathlibNt.SieveTheory.LiuWeight.panModulusCutoff N (B : ℝ)
  let x : ℝ := Real.log (N : ℝ)
  have hx1 : 1 ≤ x := by
    dsimp [x]
    have he1 : Real.exp 1 < (3 : ℝ) := Real.exp_one_lt_d9.trans (by norm_num)
    exact (Real.lt_log_iff_exp_lt (by positivity : (0 : ℝ) < N)).2
      (he1.trans_le (by exact_mod_cast (show 3 ≤ N by omega))) |>.le
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx1
  have hRpow : x ^ (2 * (A + 49)) ≤ (R : ℝ) := by
    simpa [R, C, standardBVHighChosenUnconditionalTypeIICutoff,
      standardBVHighChosenUnconditionalTypeIIConductorExponent,
      standardBVHighChosenUnconditionalTypeIIExponent, x] using hRlower
  have hRpos : 0 < R := by
    exact_mod_cast (lt_of_lt_of_le (pow_pos hx0 _) hRpow)
  have hsRpos : 0 < Real.sqrt (R : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hRpos)
  have hsR : x ^ (A + 49) ≤ Real.sqrt (R : ℝ) := by
    have hsRsq : Real.sqrt (R : ℝ) ^ 2 = R := Real.sq_sqrt (by positivity)
    have hp : (x ^ (A + 49)) ^ 2 = x ^ (2 * (A + 49)) := by
      rw [← pow_mul]
      congr 1
      omega
    have hp0 : 0 ≤ x ^ (A + 49) := pow_nonneg hx0.le _
    nlinarith
  have hQone : 1 ≤ Q := by
    dsimp [Q, MathlibNt.SieveTheory.LiuWeight.panModulusCutoff]
    have hden : 0 < x ^ B := pow_pos hx0 _
    have hgrow : x ^ B ≤ Real.sqrt N := by
      simpa [B, x] using hQgrow
    have hratio : (1 : ℝ) ≤ (N : ℝ) ^ (1 / 2 : ℝ) / x ^ B := by
      rw [← Real.sqrt_eq_rpow]
      exact (one_le_div₀ hden).2 hgrow
    exact Nat.le_floor (by
      simpa [x, Real.rpow_natCast] using hratio)
  have hQpos : 0 < Q := by omega
  have hQsq : Q ^ 2 ≤ N := by
    simpa [Q] using MathlibNt.SieveTheory.LiuWeight.panModulusCutoff_sq_le
      N (B : ℝ) (by omega) (by positivity : 0 ≤ (B : ℝ))
  have hQleN : Q ≤ N := by
    calc
      Q ≤ Q ^ 2 := by nlinarith
      _ ≤ N := hQsq
  have hQleHalf : Q ≤ N / 2 := by
    apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).2
    have hQreal : (Q : ℝ) ≤ Real.sqrt N := by
      have hQsqR : ((Q : ℝ) ^ 2) ≤ (N : ℝ) := by exact_mod_cast hQsq
      have hsSq : Real.sqrt N ^ 2 = (N : ℝ) := Real.sq_sqrt (by positivity)
      nlinarith [show (0 : ℝ) ≤ Q by positivity, Real.sqrt_nonneg (N : ℝ)]
    have hsN : Real.sqrt N ≤ (N : ℝ) / 2 := by
      have hsSq : Real.sqrt N ^ 2 = (N : ℝ) := Real.sq_sqrt (by positivity)
      have hsNonneg := Real.sqrt_nonneg (N : ℝ)
      have hs9 : 3 ≤ Real.sqrt N := by
        nlinarith [show (9 : ℝ) ≤ N by exact_mod_cast hN]
      nlinarith
    have htwo : (2 : ℝ) * Q ≤ N := by nlinarith [hQreal.trans hsN]
    have htwoNat : 2 * Q ≤ N := by exact_mod_cast htwo
    simpa [mul_comm] using htwoNat
  have hRltN : R < N := by
    have hRreal : (R : ℝ) ≤ Real.sqrt N := by
      calc
        (R : ℝ) ≤ Real.log (N : ℝ) ^ C := by
          dsimp [R, logConductorThreshold]
          exact Nat.floor_le (pow_nonneg (Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))) _)
        _ ≤ Real.sqrt N := by
          have hpowmono : x ^ C ≤ x ^ (2 * (3 * A + 200)) := by
            apply pow_le_pow_right₀ hx1
            dsimp [C]
            omega
          exact hpowmono.trans (by simpa [x] using hCgrow)
    have hsSq : Real.sqrt N ^ 2 = (N : ℝ) := Real.sq_sqrt (by positivity)
    have hslt : Real.sqrt N < (N : ℝ) := by
      nlinarith [Real.sqrt_nonneg (N : ℝ), show (1 : ℝ) < N by exact_mod_cast (show 1 < N by omega)]
    exact_mod_cast hRreal.trans_lt hslt
  have haggregate := apNormalizedVaughanTypeIIMeanOn_highConductor_le_allAspect_aggregate
    N Q C R R hN hRpos hQleHalf hRltN hRltN
  have hindexNat :
      (productionConductorBlockGeometry N Q C hRpos).index.card ≤ Nat.log2 N + 1 :=
    productionConductorBlockGeometry_index_card_le_log2 N Q C hRpos hQleN
  have hactiveNat :
      (vaughanTypeIIActiveCanonicalRectangles N R R).card ≤ (Nat.log2 N + 1) ^ 2 := by
    simpa [R, C, standardBVHighChosenUnconditionalTypeIICutoff,
      standardBVHighChosenUnconditionalTypeIIConductorExponent, standardBVHighChosenUnconditionalTypeIIExponent] using
      standardBVHighChosenUnconditionalTypeII_activeCard_le A N
  have hlog2 : (Nat.log2 N : ℝ) ≤ 2 * x := by
    simpa [x] using natLog2_cast_le_two_log (show 2 ≤ N by omega)
  have hlog2one : ((Nat.log2 N + 1 : ℕ) : ℝ) ≤ 3 * x := by
    push_cast
    linarith
  have hactive :
      ((vaughanTypeIIActiveCanonicalRectangles N R R).card : ℝ) ≤ 9 * x ^ 2 := by
    calc
      _ ≤ (((Nat.log2 N + 1 : ℕ) : ℝ) ^ 2) := by exact_mod_cast hactiveNat
      _ ≤ (3 * x) ^ 2 := pow_le_pow_left₀ (by positivity) hlog2one 2
      _ = 9 * x ^ 2 := by ring
  have hindex :
      (((productionConductorBlockGeometry N Q C hRpos).index.card : ℕ) : ℝ) ≤ 3 * x := by
    have hc : (((productionConductorBlockGeometry N Q C hRpos).index.card : ℕ) : ℝ) ≤
        ((Nat.log2 N + 1 : ℕ) : ℝ) := by exact_mod_cast hindexNat
    exact hc.trans hlog2one
  have hlog4 : Real.log (4 * N + 4 : ℕ) ≤ 3 * x := by
    have hpoly : 4 * N + 4 ≤ N * N := by nlinarith
    calc
      Real.log (4 * N + 4 : ℕ) ≤ Real.log (N * N : ℕ) :=
        Real.log_le_log (by positivity) (by exact_mod_cast hpoly)
      _ = 2 * x := by rw [Nat.cast_mul, Real.log_mul (by positivity) (by positivity)]; ring
      _ ≤ 3 * x := by nlinarith
  have hH : conductorHarmonicFactor Q ≤ 2 * x := by
    have hlogQ : Real.log (Q : ℝ) ≤ x := by
      dsimp [x]
      exact Real.log_le_log (by exact_mod_cast hQpos) (by exact_mod_cast hQleN)
    exact (conductorHarmonicFactor_le Q).trans (by linarith)
  have habel : discreteAbelAmplifierPrefixMax N ≤ 3 := by
    refine (discreteAbelAmplifierPrefixMax_le_two_inv_log_two N).trans ?_
    have htwo : (2 / 3 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
    rw [mul_inv_le_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))]
    linarith
  have hQpay : (Q : ℝ) * Real.sqrt N ≤ (N : ℝ) / x ^ B := by
    have hq : (Q : ℝ) ≤ Real.sqrt N / x ^ B := by
      calc
        (Q : ℝ) ≤ (N : ℝ) ^ (1 / 2 : ℝ) / Real.log N ^ (B : ℝ) :=
          Nat.floor_le (by positivity)
        _ = Real.sqrt N / x ^ B := by
          rw [Real.sqrt_eq_rpow, Real.rpow_natCast]
    have hs : Real.sqrt N ^ 2 = (N : ℝ) := Real.sq_sqrt (by positivity)
    calc
      (Q : ℝ) * Real.sqrt N ≤ (Real.sqrt N / x ^ B) * Real.sqrt N := by gcongr
      _ = (Real.sqrt N * Real.sqrt N) / x ^ B := by ring
      _ = (N : ℝ) / x ^ B := by rw [← pow_two, hs]
  have hRinv : (N : ℝ) / R ≤ (N : ℝ) / x ^ (A + 49) := by
    have hsRq : Real.sqrt (R : ℝ) ^ 2 = (R : ℝ) := Real.sq_sqrt (by positivity)
    have hsRleR : Real.sqrt (R : ℝ) ≤ (R : ℝ) := by
      nlinarith [Real.sqrt_nonneg (R : ℝ), show (1 : ℝ) ≤ R by exact_mod_cast hRpos]
    exact div_le_div_of_nonneg_left (by positivity) (pow_pos hx0 _) (hsR.trans hsRleR)
  have hRsqrt : (N : ℝ) / Real.sqrt (R + 1 : ℕ) ≤
      (N : ℝ) / x ^ (A + 49) := by
    have hsmono : Real.sqrt (R : ℝ) ≤ Real.sqrt (R + 1 : ℕ) := Real.sqrt_le_sqrt (by norm_num)
    exact div_le_div_of_nonneg_left (by positivity) (pow_pos hx0 _) (hsR.trans hsmono)
  have hbracket :
      2 * (N : ℝ) / R +
          (((productionConductorBlockGeometry N Q C hRpos).index.card : ℕ) : ℝ) *
            ((N : ℝ) / Real.sqrt (R + 1 : ℕ) + (N : ℝ) / Real.sqrt (R + 1 : ℕ)) +
          2 * (Q : ℝ) * Real.sqrt N ≤
        10 * (N : ℝ) / x ^ (A + 48) := by
    have hpow38 : x ^ (A + 48) ≤ x ^ (A + 49) :=
      pow_le_pow_right₀ hx1 (by omega)
    have hden39 : 0 < x ^ (A + 49) := pow_pos hx0 _
    have hden38 : 0 < x ^ (A + 48) := pow_pos hx0 _
    have hsmall : (N : ℝ) / x ^ (A + 49) ≤ (N : ℝ) / x ^ (A + 48) :=
      div_le_div_of_nonneg_left (by positivity) hden38 hpow38
    have hBden : x ^ (A + 48) ≤ x ^ B := by
      dsimp [B]
      exact pow_le_pow_right₀ hx1 (by omega)
    have hqsmall : (N : ℝ) / x ^ B ≤ (N : ℝ) / x ^ (A + 48) :=
      div_le_div_of_nonneg_left (by positivity) hden38 hBden
    let T : ℝ := (N : ℝ) / x ^ (A + 48)
    have hfirst : 2 * (N : ℝ) / R ≤ 2 * T := by
      dsimp [T]
      calc
        2 * (N : ℝ) / R = 2 * ((N : ℝ) / R) := by ring
        _ ≤ 2 * ((N : ℝ) / x ^ (A + 48)) :=
          mul_le_mul_of_nonneg_left (hRinv.trans hsmall) (by norm_num)
    have hsum : (N : ℝ) / Real.sqrt (R + 1 : ℕ) +
        (N : ℝ) / Real.sqrt (R + 1 : ℕ) ≤ 2 * ((N : ℝ) / x ^ (A + 49)) := by
      nlinarith [hRsqrt]
    have hmiddle0 :
        (((productionConductorBlockGeometry N Q C hRpos).index.card : ℕ) : ℝ) *
          ((N : ℝ) / Real.sqrt (R + 1 : ℕ) + (N : ℝ) / Real.sqrt (R + 1 : ℕ)) ≤
        (3 * x) * (2 * ((N : ℝ) / x ^ (A + 49))) := by
      exact mul_le_mul hindex hsum (by positivity) (by positivity)
    have hcancel : (3 * x) * (2 * ((N : ℝ) / x ^ (A + 49))) = 6 * T := by
      dsimp [T]
      rw [show A + 49 = (A + 48) + 1 by omega, pow_succ]
      field_simp
      ring
    have hmiddle :
        (((productionConductorBlockGeometry N Q C hRpos).index.card : ℕ) : ℝ) *
          ((N : ℝ) / Real.sqrt (R + 1 : ℕ) + (N : ℝ) / Real.sqrt (R + 1 : ℕ)) ≤
        6 * T := hmiddle0.trans_eq hcancel
    have hthird : 2 * (Q : ℝ) * Real.sqrt N ≤ 2 * T := by
      dsimp [T]
      nlinarith [hQpay, hqsmall]
    calc
      2 * (N : ℝ) / R +
          (((productionConductorBlockGeometry N Q C hRpos).index.card : ℕ) : ℝ) *
            ((N : ℝ) / Real.sqrt (R + 1 : ℕ) + (N : ℝ) / Real.sqrt (R + 1 : ℕ)) +
          2 * (Q : ℝ) * Real.sqrt N ≤ 2 * T + 6 * T + 2 * T :=
        add_le_add (add_le_add hfirst hmiddle) hthird
      _ = 10 * (N : ℝ) / x ^ (A + 48) := by dsimp [T]; ring
  have hmean : highConductorVaughanTypeIIMean N Q C R R ≤
      (9 * x ^ 2) * (1000000 * (3 * x) ^ 15) *
        (10 * (N : ℝ) / x ^ (A + 48)) := by
    change apNormalizedVaughanTypeIIMeanOn N R R (highConductorSet N Q C) ≤ _
    exact haggregate.trans (by gcongr)
  have houter :
      4 * discreteAbelAmplifierPrefixMax N * conductorHarmonicFactor Q ^ 2 ≤
        48 * x ^ 2 := by
    have hH0 : 0 ≤ conductorHarmonicFactor Q := conductorHarmonicFactor_nonneg Q
    have hHsq : conductorHarmonicFactor Q ^ 2 ≤ (2 * x) ^ 2 :=
      pow_le_pow_left₀ hH0 hH 2
    calc
      _ ≤ 4 * 3 * (2 * x) ^ 2 := by
        exact mul_le_mul (mul_le_mul_of_nonneg_left habel (by norm_num)) hHsq
          (sq_nonneg _) (by positivity)
      _ = 48 * x ^ 2 := by ring
  have hnonneg : 0 ≤ highConductorVaughanTypeIIMean N Q C R R := by
    unfold highConductorVaughanTypeIIMean apNormalizedPrimitiveMeanOn
    exact Finset.sum_nonneg fun d hd =>
      mul_nonneg (inv_nonneg.mpr (by positivity))
        (Finset.sum_nonneg fun ψ hψ => primitivePrefixAmplitude_nonneg _ _ _ _)
  calc
    4 * discreteAbelAmplifierPrefixMax N * conductorHarmonicFactor Q ^ 2 *
        highConductorVaughanTypeIIMean N Q C R R ≤
      (48 * x ^ 2) * ((9 * x ^ 2) * (1000000 * (3 * x) ^ 15) *
        (10 * (N : ℝ) / x ^ (A + 48))) :=
      mul_le_mul houter hmean hnonneg (by positivity)
    _ ≤ K * (N : ℝ) / x ^ A := by
      dsimp [K]
      have hconst : (61987278240000000 : ℝ) ≤ 1000000000000000000 := by norm_num
      have hpow : x ^ A ≤ x ^ (A + 29) := pow_le_pow_right₀ hx1 (by omega)
      have hdiv : (N : ℝ) / x ^ (A + 29) ≤ (N : ℝ) / x ^ A :=
        div_le_div_of_nonneg_left (by positivity) (pow_pos hx0 A) hpow
      calc
        (48 * x ^ 2) * (9 * x ^ 2 * (1000000 * (3 * x) ^ 15) *
            (10 * (N : ℝ) / x ^ (A + 48))) =
            61987278240000000 * ((N : ℝ) / x ^ (A + 29)) := by
              rw [show A + 48 = (A + 29) + 19 by omega, pow_add]
              field_simp
              ring
        _ ≤ 61987278240000000 * ((N : ℝ) / x ^ A) :=
          mul_le_mul_of_nonneg_left hdiv (by norm_num)
        _ ≤ 1000000000000000000 * ((N : ℝ) / x ^ A) :=
          mul_le_mul_of_nonneg_right hconst (by positivity)
        _ = 1000000000000000000 * (N : ℝ) / x ^ A := by ring

/-- The elementary finite-complex-Cauchy Type-I estimate is payable at the
same explicit cutoff.  No row-triangle theorem is used here. -/
theorem standardBVHighChosenUnconditional_typeI (A : ℕ) :
    let B := 3 * A + 200
    let C := 2 * (A + 50)
    let u : ℕ → ℕ := fun N => logConductorThreshold N C
    let v : ℕ → ℕ := fun N => logConductorThreshold N C
    ∃ K : ℝ, 0 < K ∧
      ∀ᶠ N : ℕ in Filter.atTop,
        let Q := MathlibNt.SieveTheory.LiuWeight.panModulusCutoff N (B : ℝ)
        4 * discreteAbelAmplifierPrefixMax N * conductorHarmonicFactor Q ^ 2 *
            highConductorVaughanTypeIMean N Q C (u N) (v N) ≤
          K * (N : ℝ) / Real.log N ^ A := by
  dsimp only
  refine ⟨2000, by norm_num, ?_⟩
  filter_upwards [eventually_ge_atTop (9 : ℕ),
    log_pow_le_sqrt_eventually (2 * (A + 50))] with N hN hCgrow
  let B : ℕ := 3 * A + 200
  let C : ℕ := 2 * (A + 50)
  let R : ℕ := logConductorThreshold N C
  let Q := MathlibNt.SieveTheory.LiuWeight.panModulusCutoff N (B : ℝ)
  let x : ℝ := Real.log (N : ℝ)
  have hx1 : 1 ≤ x := by
    dsimp [x]
    have he1 : Real.exp 1 < (3 : ℝ) := Real.exp_one_lt_d9.trans (by norm_num)
    exact (Real.lt_log_iff_exp_lt (by positivity : (0 : ℝ) < N)).2
      (he1.trans_le (by exact_mod_cast (show 3 ≤ N by omega))) |>.le
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx1
  have hRcast : (R : ℝ) ≤ x ^ C := by
    dsimp [R, logConductorThreshold]
    exact Nat.floor_le (pow_nonneg hx0.le _)
  have hRC : (0 : ℝ) ≤ R := by positivity
  have hRleN : R ≤ N := by
    have hRsqrt : (R : ℝ) ≤ Real.sqrt N := hRcast.trans (by simpa [C, x] using hCgrow)
    have hsSq : Real.sqrt N ^ 2 = (N : ℝ) := Real.sq_sqrt (by positivity)
    have hsle : Real.sqrt N ≤ (N : ℝ) := by
      nlinarith [Real.sqrt_nonneg (N : ℝ), show (1 : ℝ) ≤ N by exact_mod_cast (show 1 ≤ N by omega)]
    exact_mod_cast hRsqrt.trans hsle
  have hlogN1 : Real.log (N + 1 : ℕ) ≤ 2 * x := by
    have hpoly : N + 1 ≤ N * N := by nlinarith
    calc
      Real.log (N + 1 : ℕ) ≤ Real.log (N * N : ℕ) :=
        Real.log_le_log (by positivity) (by exact_mod_cast hpoly)
      _ = 2 * x := by rw [Nat.cast_mul, Real.log_mul (by positivity) (by positivity)]; ring
  have hlogR1 : Real.log (R + 1 : ℕ) ≤ 2 * x := by
    exact (Real.log_le_log (by positivity) (by exact_mod_cast Nat.succ_le_succ hRleN)).trans hlogN1
  have hRCone : (1 : ℝ) ≤ x ^ C := one_le_pow₀ hx1
  have hcore :
      (R : ℝ) * Real.log (N + 1 : ℕ) +
          (R : ℝ) * R * Real.log (R + 1 : ℕ) ≤
        4 * x ^ (2 * C + 1) := by
    have hR2 : (R : ℝ) ^ 2 ≤ (x ^ C) ^ 2 :=
      pow_le_pow_left₀ hRC hRcast 2
    have hfirst : (R : ℝ) * Real.log (N + 1 : ℕ) ≤ 2 * x ^ (2 * C + 1) := by
      calc
        (R : ℝ) * Real.log (N + 1 : ℕ) ≤ (x ^ C) * (2 * x) :=
          mul_le_mul hRcast hlogN1
            (Real.log_nonneg (by exact_mod_cast (show 1 ≤ N + 1 by omega)))
            (pow_nonneg hx0.le _)
        _ ≤ 2 * x ^ (2 * C + 1) := by
          calc
            x ^ C * (2 * x) ≤ x ^ C * x ^ C * (2 * x) := by
              apply mul_le_mul_of_nonneg_right _ (by positivity)
              calc
                x ^ C = x ^ C * 1 := by ring
                _ ≤ x ^ C * x ^ C :=
                  mul_le_mul_of_nonneg_left hRCone (pow_nonneg hx0.le _)
            _ = 2 * x ^ (2 * C + 1) := by
              rw [show 2 * C + 1 = C + C + 1 by omega, pow_add, pow_succ]
              ring
    have hsecond : (R : ℝ) * R * Real.log (R + 1 : ℕ) ≤
        2 * x ^ (2 * C + 1) := by
      calc
        (R : ℝ) * R * Real.log (R + 1 : ℕ) = (R : ℝ) ^ 2 * Real.log (R + 1 : ℕ) := by ring
        _ ≤ (x ^ C) ^ 2 * (2 * x) :=
          mul_le_mul hR2 hlogR1
            (Real.log_nonneg (by exact_mod_cast (show 1 ≤ R + 1 by omega))) (sq_nonneg _)
        _ = 2 * x ^ (2 * C + 1) := by rw [← pow_mul, pow_succ]; ring
    linarith
  have hQcast : (Q : ℝ) ≤ Real.sqrt N / x ^ B := by
    calc
      (Q : ℝ) ≤ (N : ℝ) ^ (1 / 2 : ℝ) / Real.log N ^ (B : ℝ) :=
        Nat.floor_le (by positivity)
      _ = Real.sqrt N / x ^ B := by
        rw [Real.sqrt_eq_rpow, Real.rpow_natCast]
  have hQ0 : (0 : ℝ) ≤ Q := by positivity
  have hQsq : (Q : ℝ) ^ 2 ≤ (N : ℝ) / x ^ (2 * B) := by
    have hsSq : Real.sqrt N ^ 2 = (N : ℝ) := Real.sq_sqrt (by positivity)
    have hden : 0 < x ^ B := pow_pos hx0 _
    have hsquared := pow_le_pow_left₀ hQ0 hQcast 2
    calc
      (Q : ℝ) ^ 2 ≤ (Real.sqrt N / x ^ B) ^ 2 := hsquared
      _ = (N : ℝ) / x ^ (2 * B) := by
        rw [div_pow, hsSq, ← pow_mul, show B * 2 = 2 * B by omega]
  have hmean := highConductorVaughanTypeIMean_le_elementaryCauchy N Q C R R
  have hmean' : highConductorVaughanTypeIMean N Q C R R ≤
      24 * ((N : ℝ) / x ^ (2 * B)) * x ^ (2 * C + 1) := by
    calc
      _ ≤ 6 * (Q : ℝ) ^ 2 *
          ((R : ℝ) * Real.log (N + 1 : ℕ) +
            (R : ℝ) * R * Real.log (R + 1 : ℕ)) := hmean
      _ ≤ 6 * ((N : ℝ) / x ^ (2 * B)) * (4 * x ^ (2 * C + 1)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hQsq (by norm_num)) hcore
          (by positivity) (by positivity)
      _ = 24 * ((N : ℝ) / x ^ (2 * B)) * x ^ (2 * C + 1) := by ring
  have hH : conductorHarmonicFactor Q ≤ 2 * x := by
    by_cases hQ : Q = 0
    · simp [hQ, conductorHarmonicFactor, x, hx0.le]
    · have hQleN : Q ≤ N := by
        have hqreal : (Q : ℝ) ≤ Real.sqrt N := hQcast.trans (div_le_self (Real.sqrt_nonneg _) (one_le_pow₀ hx1))
        have hsle : Real.sqrt N ≤ (N : ℝ) := by
          have hsSq : Real.sqrt N ^ 2 = (N : ℝ) := Real.sq_sqrt (by positivity)
          nlinarith [Real.sqrt_nonneg (N : ℝ), show (1 : ℝ) ≤ N by exact_mod_cast (show 1 ≤ N by omega)]
        exact_mod_cast hqreal.trans hsle
      exact (conductorHarmonicFactor_le Q).trans (by
        have hQposR : (0 : ℝ) < Q := by exact_mod_cast (Nat.pos_of_ne_zero hQ)
        have hQleNR : (Q : ℝ) ≤ N := by exact_mod_cast hQleN
        have hlogQN := Real.log_le_log hQposR hQleNR
        dsimp [x] at *
        linarith)
  have habel : discreteAbelAmplifierPrefixMax N ≤ 3 := by
    refine (discreteAbelAmplifierPrefixMax_le_two_inv_log_two N).trans ?_
    have htwo : (2 / 3 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
    rw [mul_inv_le_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))]
    linarith
  have houter : 4 * discreteAbelAmplifierPrefixMax N * conductorHarmonicFactor Q ^ 2 ≤
      48 * x ^ 2 := by
    have hH0 : 0 ≤ conductorHarmonicFactor Q := conductorHarmonicFactor_nonneg Q
    calc
      _ ≤ 4 * 3 * (2 * x) ^ 2 := by
        gcongr
      _ = 48 * x ^ 2 := by ring
  have hscale : ((N : ℝ) / x ^ (2 * B)) * x ^ (2 * C + 3) ≤
      (N : ℝ) / x ^ A := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (pow_pos hx0 _) (pow_pos hx0 _)]
    have hexp : 2 * C + 3 + A ≤ 2 * B := by dsimp [B, C]; omega
    calc
      (N : ℝ) * x ^ (2 * C + 3) * x ^ A = (N : ℝ) * x ^ (2 * C + 3 + A) := by rw [pow_add]; ring
      _ ≤ (N : ℝ) * x ^ (2 * B) := by
        gcongr
  have hnonneg : 0 ≤ highConductorVaughanTypeIMean N Q C R R := by
    unfold highConductorVaughanTypeIMean apNormalizedPrimitiveMeanOn
    exact Finset.sum_nonneg fun d hd => mul_nonneg (inv_nonneg.mpr (by positivity))
      (Finset.sum_nonneg fun ψ hψ => primitivePrefixAmplitude_nonneg _ _ _ _)
  calc
    4 * discreteAbelAmplifierPrefixMax N * conductorHarmonicFactor Q ^ 2 *
        highConductorVaughanTypeIMean N Q C R R ≤
      (48 * x ^ 2) * (24 * ((N : ℝ) / x ^ (2 * B)) * x ^ (2 * C + 1)) :=
        mul_le_mul houter hmean' hnonneg (by positivity)
    _ = 1152 * (((N : ℝ) / x ^ (2 * B)) * x ^ (2 * C + 3)) := by ring
    _ ≤ 2000 * (N : ℝ) / x ^ A := by
      calc
        _ ≤ 1152 * ((N : ℝ) / x ^ A) := mul_le_mul_of_nonneg_left hscale (by norm_num)
        _ ≤ 2000 * ((N : ℝ) / x ^ A) :=
          mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
        _ = _ := by ring

theorem standardBVHighChosenUnconditional_cutoff_le_balanced_eventually (A : ℕ) :
    ∀ᶠ N : ℕ in Filter.atTop,
      logConductorThreshold N (2 * (A + 50)) ≤
        standardBVBalancedSmallCutoff N := by
  filter_upwards [eventually_ge_atTop (2 : ℕ),
    log_pow_le_sqrt_eventually (3 * (2 * (A + 50)))] with N hN hlog
  let x : ℝ := Real.log (N : ℝ)
  let C : ℕ := 2 * (A + 50)
  have hx0 : 0 ≤ x := by
    dsimp [x]
    exact Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  have hN0 : (0 : ℝ) ≤ N := by positivity
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hsqrtSq : Real.sqrt (N : ℝ) ^ 2 = (N : ℝ) := Real.sq_sqrt hN0
  have hsqrt : Real.sqrt (N : ℝ) ≤ (N : ℝ) := by
    nlinarith [Real.sqrt_nonneg (N : ℝ)]
  have hpow : x ^ (3 * C) ≤ Real.sqrt (N : ℝ) := by
    simpa [x, C] using hlog
  have hcub : (x ^ C) ^ 3 ≤ (N : ℝ) := by
    rw [← pow_mul]
    have heq : C * 3 = 3 * C := by omega
    rw [heq]
    exact hpow.trans hsqrt
  have hrpow : x ^ C ≤ (N : ℝ) ^ (1 / 3 : ℝ) := by
    have hcub' : (x ^ C) ^ (3 : ℝ) ≤ (N : ℝ) := by
      simpa [Real.rpow_natCast] using hcub
    have h := (Real.le_rpow_inv_iff_of_pos
      (pow_nonneg hx0 C) hN0 (by norm_num : (0 : ℝ) < 3)).2 hcub'
    simpa [one_div] using h
  unfold logConductorThreshold standardBVBalancedSmallCutoff
  exact Nat.floor_mono (by simpa [x, C] using hrpow)

private lemma highConductorSet_eq_interval_highChosenUnconditional (N Q C : ℕ)
    (hR : 1 ≤ logConductorThreshold N C) :
    highConductorSet N Q C =
      Finset.Icc (logConductorThreshold N C + 1) Q := by
  ext d
  simp only [highConductorSet, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨-, hdQ⟩, hRd⟩
    exact ⟨Nat.add_one_le_iff.mpr hRd, hdQ⟩
  · rintro ⟨hRd, hdQ⟩
    exact ⟨⟨by omega, hdQ⟩, Nat.add_one_le_iff.mp hRd⟩

/-- Unconditional closure of exactly the small Vaughan lane at the chosen
chosen parameters `B=3*A+200`, `C=2*(A+50)`, and
`v(N)=logConductorThreshold N C`. -/
theorem standardBVHighChosenUnconditional_small (A : ℕ) :
    let B := 3 * A + 200
    let C := 2 * (A + 50)
    let v : ℕ → ℕ := fun N => logConductorThreshold N C
    ∃ K : ℝ, 0 < K ∧
      ∀ᶠ N : ℕ in Filter.atTop,
        let Q := MathlibNt.SieveTheory.LiuWeight.panModulusCutoff N (B : ℝ)
        let P := 4 * discreteAbelAmplifierPrefixMax N * conductorHarmonicFactor Q ^ 2
        P * highConductorVaughanSmallMean N Q C (v N) ≤
          K * (N : ℝ) / Real.log N ^ A := by
  dsimp only
  let B : ℕ := 3 * A + 200
  let C : ℕ := 2 * (A + 50)
  let v : ℕ → ℕ := fun N => logConductorThreshold N C
  have hv : ∀ᶠ N : ℕ in Filter.atTop,
      v N ≤ standardBVBalancedSmallCutoff N := by
    simpa [v, C] using standardBVHighChosenUnconditional_cutoff_le_balanced_eventually A
  obtain ⟨K₀, hK₀, hsmallSource⟩ :=
    standardBVSmall_squareLedger_payable_of_le_balanced v hv A 0 B C
  refine ⟨K₀, hK₀, ?_⟩
  filter_upwards [hsmallSource, eventually_ge_atTop (9 : ℕ)] with N hsmallPay hN9
  dsimp only at hsmallPay ⊢
  let Q := MathlibNt.SieveTheory.LiuWeight.panModulusCutoff N (B : ℝ)
  let R := logConductorThreshold N C
  let P := 4 * discreteAbelAmplifierPrefixMax N * conductorHarmonicFactor Q ^ 2
  have hR : 0 < R := by
    dsimp [R, logConductorThreshold]
    have hlog : 1 < Real.log (N : ℝ) := by
      have h9 : Real.exp 1 < (9 : ℝ) := by
        nlinarith [Real.exp_one_lt_d9]
      exact (Real.lt_log_iff_exp_lt (by positivity : (0 : ℝ) < N)).2
        (h9.trans_le (by exact_mod_cast hN9))
    have hpow : 1 < Real.log (N : ℝ) ^ C := by
      have hC : 0 < C := by dsimp [C]; omega
      exact one_lt_pow₀ hlog hC.ne'
    exact Nat.floor_pos.mpr hpow.le
  have hP : 0 ≤ P := by
    dsimp [P]
    have ha : 0 ≤ discreteAbelAmplifierPrefixMax N := by
      have h0 : 0 ≤ discreteAbelAmplifier 0 := by
        unfold discreteAbelAmplifier
        positivity
      exact h0.trans (by
        unfold discreteAbelAmplifierPrefixMax
        exact Finset.le_max' _ _ (Finset.mem_image.mpr ⟨0, by simp, rfl⟩))
    positivity
  have hcard : ∀ d ∈ Finset.Icc (R + 1) Q,
      Fintype.card (PrimitiveCharacter d) ≤ d.totient := by
    intro d hd
    exact card_primitiveCharacter_le_totient d (by
      have hdR := (Finset.mem_Icc.mp hd).1
      omega)
  have hRone : 1 ≤ R := by omega
  have hsmallCauchy := apNormalizedPrimitiveMeanOn_high_sq_le
    (vaughanSmallCoeff vaughanUnitIntegerCoeff (v N)) N Q R hcard
  rw [← highConductorSet_eq_interval_highChosenUnconditional N Q C
    (by simpa only [R] using hRone)] at hsmallCauchy
  have hsmallNonneg : 0 ≤ highConductorVaughanSmallMean N Q C (v N) := by
    unfold highConductorVaughanSmallMean apNormalizedPrimitiveMeanOn
    exact Finset.sum_nonneg fun d hd => mul_nonneg (inv_nonneg.mpr (by positivity))
      (Finset.sum_nonneg fun ψ hψ => primitivePrefixAmplitude_nonneg _ _ _ _)
  have hharmNonneg : 0 ≤ highConductorHarmonicFactor Q R := by
    unfold highConductorHarmonicFactor
    positivity
  have hledgerNonneg : 0 ≤ primitivePrefixSquareLedgerOn
      (vaughanSmallCoeff vaughanUnitIntegerCoeff (v N)) N
      (highConductorSet N Q C) := by
    unfold primitivePrefixSquareLedgerOn
    exact Finset.sum_nonneg fun d hd =>
      mul_nonneg (div_nonneg (by positivity) (by positivity))
        (Finset.sum_nonneg fun ψ hψ =>
          primitiveCharacterPrefixMaxSquare_nonneg _ _ _ _ _)
  have hsmallSq :
      (P * highConductorVaughanSmallMean N Q C (v N)) ^ 2 ≤
        (K₀ * ((N : ℝ) / Real.log N ^ A)) ^ 2 := by
    calc
      (P * highConductorVaughanSmallMean N Q C (v N)) ^ 2 =
          P ^ 2 * highConductorVaughanSmallMean N Q C (v N) ^ 2 := by ring
      _ ≤ P ^ 2 * (highConductorHarmonicFactor Q R *
          primitivePrefixSquareLedgerOn
            (vaughanSmallCoeff vaughanUnitIntegerCoeff (v N)) N
            (highConductorSet N Q C)) :=
        mul_le_mul_of_nonneg_left hsmallCauchy (sq_nonneg P)
      _ ≤ P ^ 2 * (3 * highConductorHarmonicFactor Q R *
          primitivePrefixSquareLedgerOn
            (vaughanSmallCoeff vaughanUnitIntegerCoeff (v N)) N
            (highConductorSet N Q C)) := by
        have hcore : 0 ≤ highConductorHarmonicFactor Q R *
            primitivePrefixSquareLedgerOn
              (vaughanSmallCoeff vaughanUnitIntegerCoeff (v N)) N
              (highConductorSet N Q C) :=
          mul_nonneg hharmNonneg hledgerNonneg
        nlinarith [sq_nonneg P]
      _ ≤ (K₀ * ((N : ℝ) / Real.log N ^ A)) ^ 2 := by
        simpa only [Nat.add_zero] using hsmallPay
  have hlogPos : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hsmall : P * highConductorVaughanSmallMean N Q C (v N) ≤
      K₀ * ((N : ℝ) / Real.log N ^ A) :=
    (sq_le_sq₀ (mul_nonneg hP hsmallNonneg) (by positivity)).mp hsmallSq
  calc
    P * highConductorVaughanSmallMean N Q C (v N) ≤
        K₀ * ((N : ℝ) / Real.log N ^ A) := hsmall
    _ = K₀ * (N : ℝ) / Real.log N ^ A := by ring


/-- Unconditional inhabitant of the genuine chosen high-conductor source.
The shared pair is `u(N)=v(N)=logConductorThreshold N (2*(A+50))`. -/
theorem standardBVHighChosenUnconditional :
    StandardBVHighTypeITypeIIHybridChosenSource := by
  intro A
  obtain ⟨K₁, hK₁, hI⟩ := standardBVHighChosenUnconditional_typeI A
  obtain ⟨K₂, hK₂, hII⟩ := standardBVHighChosenUnconditional_typeII A
  obtain ⟨K₀, hK₀, hsmall⟩ := standardBVHighChosenUnconditional_small A
  let B : ℕ := 3 * A + 200
  let C : ℕ := 2 * (A + 50)
  let u : ℕ → ℕ := fun N => logConductorThreshold N C
  let v : ℕ → ℕ := fun N => logConductorThreshold N C
  refine ⟨B, C, by dsimp [B]; omega, u, v, K₁ + K₂ + K₀, by positivity, ?_⟩
  filter_upwards [hI, hII, hsmall] with N hIN hIIN hsmallN
  dsimp only at hIN hIIN hsmallN ⊢
  let Q := MathlibNt.SieveTheory.LiuWeight.panModulusCutoff N (B : ℝ)
  let P := 4 * discreteAbelAmplifierPrefixMax N * conductorHarmonicFactor Q ^ 2
  have hI' : P * highConductorVaughanTypeIMean N Q C (u N) (v N) ≤
      K₁ * (N : ℝ) / Real.log N ^ A := by
    simpa only [P, Q, B, C, u, v] using hIN
  have hII' : P * highConductorVaughanTypeIIMean N Q C (u N) (v N) ≤
      K₂ * (N : ℝ) / Real.log N ^ A := by
    simpa only [P, Q, B, C, u, v] using hIIN
  have hsmall' : P * highConductorVaughanSmallMean N Q C (v N) ≤
      K₀ * (N : ℝ) / Real.log N ^ A := by
    simpa only [P, Q, B, C, v] using hsmallN
  calc
    P * (highConductorVaughanTypeIMean N Q C (u N) (v N) +
        highConductorVaughanTypeIIMean N Q C (u N) (v N) +
        highConductorVaughanSmallMean N Q C (v N)) =
      P * highConductorVaughanTypeIMean N Q C (u N) (v N) +
        P * highConductorVaughanTypeIIMean N Q C (u N) (v N) +
        P * highConductorVaughanSmallMean N Q C (v N) := by ring
    _ ≤ K₁ * (N : ℝ) / Real.log N ^ A +
        K₂ * (N : ℝ) / Real.log N ^ A +
        K₀ * (N : ℝ) / Real.log N ^ A := add_le_add (add_le_add hI' hII') hsmall'
    _ = (K₁ + K₂ + K₀) * (N : ℝ) / Real.log N ^ A := by ring

end
end AnalyticNumberTheory.LargeSieve
