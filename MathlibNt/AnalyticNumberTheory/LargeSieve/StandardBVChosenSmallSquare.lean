import MathlibNt.AnalyticNumberTheory.LargeSieve.StandardBVPayload
import MathlibNt.AnalyticNumberTheory.LargeSieve.StandardBVLowHighConductor
import MathlibNt.SieveTheory.Distribution.LiuPan.LiuPanPrimePowerLargeSieve

namespace AnalyticNumberTheory.LargeSieve

open Classical Finset Filter
open scoped BigOperators ArithmeticFunction Topology

noncomputable section

/-- Legacy degenerate cutoff retained only for compatibility shims that still
expect the historically zeroed small lane. -/
def standardBVChosenSmallCutoff (N : ℕ) : ℕ := min N 1

/-- Production balanced cutoff for the retained small lane. -/
def standardBVBalancedSmallCutoff (N : ℕ) : ℕ :=
  Nat.floor ((N : ℝ) ^ (1 / 3 : ℝ))

lemma standardBVBalancedSmallCutoff_le (N : ℕ) :
    standardBVBalancedSmallCutoff N ≤ N := by
  rcases N with _ | N
  · simp [standardBVBalancedSmallCutoff]
  · have hbase : (1 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by
      exact_mod_cast (show 1 ≤ N + 1 by omega)
    have hrpow : ((N + 1 : ℕ) : ℝ) ^ (1 / 3 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by
      simpa using (Real.rpow_le_rpow_of_exponent_le hbase (by norm_num : (1 / 3 : ℝ) ≤ 1))
    have hfloor : (standardBVBalancedSmallCutoff (N + 1) : ℝ) ≤
        ((N + 1 : ℕ) : ℝ) ^ (1 / 3 : ℝ) := by
      exact Nat.floor_le (Real.rpow_nonneg (by positivity) _)
    exact_mod_cast (hfloor.trans hrpow)

lemma standardBVBalancedSmallCutoff_cast_le_sqrt (N : ℕ) :
    (standardBVBalancedSmallCutoff N : ℝ) ≤ Real.sqrt N := by
  rcases N with _ | N
  · simp [standardBVBalancedSmallCutoff]
  · have hbase : (1 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by
      exact_mod_cast (show 1 ≤ N + 1 by omega)
    have hrpow : ((N + 1 : ℕ) : ℝ) ^ (1 / 3 : ℝ) ≤
        ((N + 1 : ℕ) : ℝ) ^ (1 / 2 : ℝ) := by
      exact Real.rpow_le_rpow_of_exponent_le hbase (by norm_num : (1 / 3 : ℝ) ≤ (1 / 2 : ℝ))
    have hfloor : (standardBVBalancedSmallCutoff (N + 1) : ℝ) ≤
        ((N + 1 : ℕ) : ℝ) ^ (1 / 3 : ℝ) := by
      exact Nat.floor_le (Real.rpow_nonneg (by positivity) _)
    calc
      (standardBVBalancedSmallCutoff (N + 1) : ℝ) ≤ ((N + 1 : ℕ) : ℝ) ^ (1 / 3 : ℝ) := hfloor
      _ ≤ ((N + 1 : ℕ) : ℝ) ^ (1 / 2 : ℝ) := hrpow
      _ = Real.sqrt (N + 1 : ℕ) := by rw [Real.sqrt_eq_rpow]

private lemma highConductorSet_subset_Icc_one (N Q C : ℕ) :
    highConductorSet N Q C ⊆ Finset.Icc 1 Q := by
  intro d hd
  have hd' := (Finset.mem_filter.mp hd).1
  have hd2 := (Finset.mem_Icc.mp hd').1
  exact Finset.mem_Icc.mpr ⟨by omega, (Finset.mem_Icc.mp hd').2⟩

/-- Ordinary primitive prefix-maximal large sieve, specialized to the exact
production small coefficient. -/
theorem standardBVChosenSmall_squareLedger_le (N Q C : ℕ) (hQ : 0 < Q) :
    primitivePrefixSquareLedgerOn
        (vaughanSmallCoeff vaughanUnitIntegerCoeff (standardBVBalancedSmallCutoff N)) N
        (highConductorSet N Q C) ≤
      (((Nat.log2 N + 1 : ℕ) : ℝ) ^ 2) * primitiveLargeSieveConstant N Q *
        ((standardBVBalancedSmallCutoff N : ℝ) *
          Real.log ((standardBVBalancedSmallCutoff N + 1 : ℕ) : ℝ) ^ 2) := by
  let v := standardBVBalancedSmallCutoff N
  have hledger : primitivePrefixSquareLedgerOn
      (vaughanSmallCoeff vaughanUnitIntegerCoeff v) N (highConductorSet N Q C) ≤
      (((Nat.log2 N + 1 : ℕ) : ℝ) ^ 2) * primitiveLargeSieveConstant N Q *
        ∑ n ∈ Finset.Icc (1 : ℤ) N,
          ‖vaughanSmallCoeff vaughanUnitIntegerCoeff v n‖ ^ 2 := by
    unfold primitivePrefixSquareLedgerOn
    refine (Finset.sum_le_sum_of_subset_of_nonneg
      (highConductorSet_subset_Icc_one N Q C) ?_).trans ?_
    · intro d hd hnot
      exact mul_nonneg (by positivity) (Finset.sum_nonneg fun ψ hψ =>
        primitiveCharacterPrefixMaxSquare_nonneg _ _ _ _ _)
    · simpa using weighted_primitive_prefix_maximal
        (vaughanSmallCoeff vaughanUnitIntegerCoeff v) 0 N Q hQ
  refine hledger.trans ?_
  apply mul_le_mul_of_nonneg_left
  · simpa using vaughanSmallCoeff_energy_le_v_mul_log_sq
      vaughanUnitIntegerCoeff N v 1 (by norm_num) (by
        intro n hn
        simp [vaughanUnitIntegerCoeff])
  · unfold primitiveLargeSieveConstant
    positivity

/-- At the chosen endpoint, the exact production small coefficient is zero. -/
theorem standardBVChosenSmallCoeff_eq_zero (N : ℕ) :
    vaughanSmallCoeff vaughanUnitIntegerCoeff (standardBVChosenSmallCutoff N) = 0 := by
  funext n
  unfold vaughanSmallCoeff standardBVChosenSmallCutoff vaughanSmall
  simp only [vaughanUnitIntegerCoeff, one_mul]
  split_ifs with h
  · have hn : n.toNat = 0 ∨ n.toNat = 1 := by omega
    rcases hn with hn | hn <;> simp [hn]
  · rfl

set_option maxHeartbeats 1000000 in
/-- The complete weighted small square ledger is paid unconditionally with the
production balanced cutoff and no coefficient zeroing. -/
theorem standardBVChosenSmall_squareLedger_payable (A κ B C : ℕ) :
    ∃ K₀ : ℝ, 0 < K₀ ∧
      ∀ᶠ N : ℕ in Filter.atTop,
        let Q := MathlibNt.SieveTheory.LiuWeight.panModulusCutoff N (B : ℝ)
        let R := logConductorThreshold N C
        let P := 4 * discreteAbelAmplifierPrefixMax N * conductorHarmonicFactor Q ^ 2
        let X := (N : ℝ) / Real.log N ^ (A + κ)
        P ^ 2 * (3 * highConductorHarmonicFactor Q R *
            primitivePrefixSquareLedgerOn
              (vaughanSmallCoeff vaughanUnitIntegerCoeff
                (standardBVBalancedSmallCutoff N)) N
              (highConductorSet N Q C)) ≤ (K₀ * X) ^ 2 := by
  let cLS : ℝ := 15 + 4 / Real.log 2
  let M : ℝ := 1000000 * cLS
  let K₀ : ℝ := Real.sqrt M + 1
  refine ⟨K₀, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (8 : ℕ),
    log_pow_le_sqrt_eventually (10 + 2 * (A + κ)),
    log_pow_le_sqrt_eventually B] with N hN hlogPay hcutGrow
  dsimp only
  let Q := MathlibNt.SieveTheory.LiuWeight.panModulusCutoff N (B : ℝ)
  let R := logConductorThreshold N C
  let P := 4 * discreteAbelAmplifierPrefixMax N * conductorHarmonicFactor Q ^ 2
  let X := (N : ℝ) / Real.log N ^ (A + κ)
  let v := standardBVBalancedSmallCutoff N
  have hlog : 1 ≤ Real.log (N : ℝ) := by
    have he1 : Real.exp 1 < (3 : ℝ) :=
      Real.exp_one_lt_d9.trans (by norm_num)
    exact (Real.lt_log_iff_exp_lt (by positivity : (0 : ℝ) < N)).2
      (he1.trans_le (by exact_mod_cast (show 3 ≤ N by omega))) |>.le
  have hlogPos : 0 < Real.log (N : ℝ) :=
    lt_of_lt_of_le zero_lt_one hlog
  have hQone : 1 ≤ Q := by
    dsimp [Q, MathlibNt.SieveTheory.LiuWeight.panModulusCutoff]
    have hdenPos : 0 < Real.log (N : ℝ) ^ (B : ℝ) := by
      simpa [Real.rpow_natCast] using pow_pos hlogPos B
    have hcutGrow' : Real.log (N : ℝ) ^ (B : ℝ) ≤ (N : ℝ) ^ (1 / 2 : ℝ) := by
      simpa [Real.sqrt_eq_rpow, Real.rpow_natCast] using hcutGrow
    have hratioReal : (1 : ℝ) ≤
        (N : ℝ) ^ (1 / 2 : ℝ) / Real.log (N : ℝ) ^ (B : ℝ) :=
      (one_le_div₀ hdenPos).2 hcutGrow'
    have hratio : ((1 : ℕ) : ℝ) ≤
        (N : ℝ) ^ (1 / 2 : ℝ) / Real.log (N : ℝ) ^ (B : ℝ) := by
      simpa using hratioReal
    exact Nat.le_floor hratio
  have hQpos : 0 < Q := by omega
  have hQsq : Q ^ 2 ≤ N := by
    simpa [Q] using MathlibNt.SieveTheory.LiuWeight.panModulusCutoff_sq_le
      N (B : ℝ) (by omega) (by positivity : 0 ≤ (B : ℝ))
  have hQle : Q ≤ N := by
    calc
      Q = Q * 1 := by simp
      _ ≤ Q * Q := Nat.mul_le_mul_left Q (Nat.succ_le_iff.mpr hQpos)
      _ = Q ^ 2 := by ring
      _ ≤ N := hQsq
  have hH : conductorHarmonicFactor Q ≤ 2 * Real.log (N : ℝ) := by
    have hlogQ : Real.log (Q : ℝ) ≤ Real.log (N : ℝ) :=
      Real.log_le_log (by exact_mod_cast hQpos) (by exact_mod_cast hQle)
    exact (conductorHarmonicFactor_le Q).trans (by linarith)
  have hH0 : 0 ≤ conductorHarmonicFactor Q := conductorHarmonicFactor_nonneg Q
  have hHH : highConductorHarmonicFactor Q R ≤ 2 * Real.log (N : ℝ) :=
    (highConductorHarmonicFactor_le Q R).trans hH
  have hHH0 : 0 ≤ highConductorHarmonicFactor Q R := by
    unfold highConductorHarmonicFactor
    positivity
  have habel : discreteAbelAmplifierPrefixMax N ≤ 3 := by
    refine (discreteAbelAmplifierPrefixMax_le_two_inv_log_two N).trans ?_
    have htwo : (2 / 3 : ℝ) < Real.log 2 := by
      linarith [Real.log_two_gt_d9]
    rw [mul_inv_le_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))]
    linarith
  have hP : P ^ 2 ≤ 144 * conductorHarmonicFactor Q ^ 4 := by
    have hP1 : P ≤ 12 * conductorHarmonicFactor Q ^ 2 := by
      dsimp [P]
      nlinarith [habel, sq_nonneg (conductorHarmonicFactor Q)]
    have hP0 : 0 ≤ P := by
      dsimp [P]
      have hA0 : 0 ≤ discreteAbelAmplifierPrefixMax N := by
        have h0 : 0 ≤ discreteAbelAmplifier 0 := by
          unfold discreteAbelAmplifier
          positivity
        exact h0.trans (by
          unfold discreteAbelAmplifierPrefixMax
          exact Finset.le_max' _ _ (Finset.mem_image.mpr ⟨0, by simp, rfl⟩))
      nlinarith [hA0, sq_nonneg (conductorHarmonicFactor Q)]
    calc
      P ^ 2 ≤ (12 * conductorHarmonicFactor Q ^ 2) ^ 2 :=
        pow_le_pow_left₀ hP0 hP1 2
      _ = 144 * conductorHarmonicFactor Q ^ 4 := by ring
  have hHpow4 : conductorHarmonicFactor Q ^ 4 ≤ (2 * Real.log (N : ℝ)) ^ 4 := by
    exact pow_le_pow_left₀ (conductorHarmonicFactor_nonneg Q) hH 4
  have hlog2N : (Nat.log2 N : ℝ) ≤ 2 * Real.log (N : ℝ) :=
    natLog2_cast_le_two_log (by omega)
  have hlog2N1 : (Nat.log2 N + 1 : ℝ) ≤ 3 * Real.log (N : ℝ) := by
    linarith
  have hlog2N1' : (((Nat.log2 N + 1 : ℕ) : ℝ)) ≤ 3 * Real.log (N : ℝ) := by
    simpa using hlog2N1
  have hlog2Sq : (((Nat.log2 N + 1 : ℕ) : ℝ) ^ 2) ≤ 9 * Real.log (N : ℝ) ^ 2 := by
    have hsq :
        ((((Nat.log2 N + 1 : ℕ) : ℝ)) ^ 2) ≤ (3 * Real.log (N : ℝ)) ^ 2 := by
      exact pow_le_pow_left₀
        (by positivity : (0 : ℝ) ≤ (((Nat.log2 N + 1 : ℕ) : ℝ))) hlog2N1' 2
    calc
      (((Nat.log2 N + 1 : ℕ) : ℝ) ^ 2) ≤ (3 * Real.log (N : ℝ)) ^ 2 := hsq
      _ = 9 * Real.log (N : ℝ) ^ 2 := by ring
  have hvN : v ≤ N := by
    simpa [v] using standardBVBalancedSmallCutoff_le N
  have hvSqrt : (v : ℝ) ≤ Real.sqrt N := by
    simpa [v] using standardBVBalancedSmallCutoff_cast_le_sqrt N
  have hlogv : Real.log ((v + 1 : ℕ) : ℝ) ≤ 2 * Real.log (N : ℝ) := by
    have hv1 : v + 1 ≤ N + 1 := Nat.succ_le_succ hvN
    have hlogvN1 : Real.log ((v + 1 : ℕ) : ℝ) ≤ Real.log (N + 1 : ℕ) :=
      Real.log_le_log (by positivity) (by exact_mod_cast hv1)
    have hN1 : N + 1 ≤ N * N := by
      have hN2 : 2 ≤ N := by omega
      calc
        N + 1 ≤ 2 * N := by omega
        _ ≤ N * N := by nlinarith
    have hlogN1 : Real.log (N + 1 : ℕ) ≤ 2 * Real.log (N : ℝ) := by
      calc
        Real.log (N + 1 : ℕ) ≤ Real.log (N * N : ℕ) :=
          Real.log_le_log (by positivity) (by exact_mod_cast hN1)
        _ = 2 * Real.log (N : ℝ) := by
          rw [Nat.cast_mul, Real.log_mul (by positivity) (by positivity)]
          ring
    exact hlogvN1.trans hlogN1
  have hvLogSq : (v : ℝ) * Real.log ((v + 1 : ℕ) : ℝ) ^ 2 ≤
      4 * Real.sqrt N * Real.log (N : ℝ) ^ 2 := by
    have hlogvSq : Real.log ((v + 1 : ℕ) : ℝ) ^ 2 ≤ 4 * Real.log (N : ℝ) ^ 2 := by
      have hlogv0 : 0 ≤ Real.log ((v + 1 : ℕ) : ℝ) := by
        exact Real.log_nonneg (by exact_mod_cast (show 1 ≤ v + 1 by omega))
      have hsq : (Real.log ((v + 1 : ℕ) : ℝ)) ^ 2 ≤ (2 * Real.log (N : ℝ)) ^ 2 := by
        nlinarith [hlogv0, hlogv]
      calc
        Real.log ((v + 1 : ℕ) : ℝ) ^ 2 ≤ (2 * Real.log (N : ℝ)) ^ 2 := hsq
        _ = 4 * Real.log (N : ℝ) ^ 2 := by ring
    calc
      (v : ℝ) * Real.log ((v + 1 : ℕ) : ℝ) ^ 2 ≤
          Real.sqrt N * Real.log ((v + 1 : ℕ) : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right hvSqrt (sq_nonneg _)
      _ ≤ Real.sqrt N * (4 * Real.log (N : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left hlogvSq (Real.sqrt_nonneg _)
      _ = 4 * Real.sqrt N * Real.log (N : ℝ) ^ 2 := by ring
  have hPLC : primitiveLargeSieveConstant N Q ≤ cLS * (N : ℝ) * Real.log (N : ℝ) := by
    have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    have hQsq1 : (1 : ℝ) ≤ (Q : ℝ) ^ 2 := by
      have : (1 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQone
      nlinarith
    have hceil :
        ((Nat.ceil (Real.log ((Q : ℝ) ^ 2) / Real.log 2) : ℕ) : ℝ) ≤
          2 * Real.log (N : ℝ) / Real.log 2 + 1 := by
      have hx0 : 0 ≤ Real.log ((Q : ℝ) ^ 2) / Real.log 2 :=
        div_nonneg (Real.log_nonneg hQsq1) hlog2.le
      have hlogQ : Real.log (Q : ℝ) ≤ Real.log (N : ℝ) :=
        Real.log_le_log (by exact_mod_cast hQpos) (by exact_mod_cast hQle)
      have hquotlog : 2 * Real.log (Q : ℝ) / Real.log 2 ≤
          2 * Real.log (N : ℝ) / Real.log 2 :=
        (div_le_div_iff_of_pos_right hlog2).2
          (mul_le_mul_of_nonneg_left hlogQ (by norm_num))
      calc
        ((Nat.ceil (Real.log ((Q : ℝ) ^ 2) / Real.log 2) : ℕ) : ℝ) ≤
            Real.log ((Q : ℝ) ^ 2) / Real.log 2 + 1 := (Nat.ceil_lt_add_one hx0).le
        _ = 2 * Real.log (Q : ℝ) / Real.log 2 + 1 := by
          rw [Real.log_pow]
          norm_num
        _ ≤ 2 * Real.log (N : ℝ) / Real.log 2 + 1 := by linarith
    have hQsqR : (Q : ℝ) ^ 2 ≤ (N : ℝ) := by exact_mod_cast hQsq
    unfold primitiveLargeSieveConstant cLS
    calc
      (N : ℝ) +
          (2 * (Nat.ceil (Real.log ((Q : ℝ) ^ 2) / Real.log 2) : ℝ) + 12) *
            (Q : ℝ) ^ 2 ≤
        (N : ℝ) + (((4 / Real.log 2) * Real.log (N : ℝ) + 14) * N) := by
          have hcoef :
              2 * (Nat.ceil (Real.log ((Q : ℝ) ^ 2) / Real.log 2) : ℝ) + 12 ≤
                (4 / Real.log 2) * Real.log (N : ℝ) + 14 := by
            calc
              2 * (Nat.ceil (Real.log ((Q : ℝ) ^ 2) / Real.log 2) : ℝ) + 12 ≤
                  2 * (2 * Real.log (N : ℝ) / Real.log 2 + 1) + 12 := by
                    gcongr
              _ = (4 / Real.log 2) * Real.log (N : ℝ) + 14 := by ring
          have hcoef0 :
              0 ≤ (4 / Real.log 2) * Real.log (N : ℝ) + 14 := by
            positivity
          have hmul :
              (2 * (Nat.ceil (Real.log ((Q : ℝ) ^ 2) / Real.log 2) : ℝ) + 12) *
                  (Q : ℝ) ^ 2 ≤
                ((4 / Real.log 2) * Real.log (N : ℝ) + 14) * N := by
            exact mul_le_mul hcoef hQsqR (by positivity) hcoef0
          linarith
      _ = (N : ℝ) * ((4 / Real.log 2) * Real.log (N : ℝ) + 15) := by ring
      _ ≤ (N : ℝ) * ((15 + 4 / Real.log 2) * Real.log (N : ℝ)) := by
          have h15 : (15 : ℝ) ≤ 15 * Real.log (N : ℝ) := by nlinarith [hlog]
          have hinner :
              (4 / Real.log 2) * Real.log (N : ℝ) + 15 ≤
                (4 / Real.log 2) * Real.log (N : ℝ) + 15 * Real.log (N : ℝ) := by
            linarith
          calc
            (N : ℝ) * ((4 / Real.log 2) * Real.log (N : ℝ) + 15)
                ≤ (N : ℝ) * ((4 / Real.log 2) * Real.log (N : ℝ) + 15 * Real.log (N : ℝ)) :=
                  mul_le_mul_of_nonneg_left hinner (by positivity)
            _ = (N : ℝ) * ((15 + 4 / Real.log 2) * Real.log (N : ℝ)) := by ring
      _ = (15 + 4 / Real.log 2) * (N : ℝ) * Real.log (N : ℝ) := by ring
  have hPLC0 : 0 ≤ primitiveLargeSieveConstant N Q := by
    unfold primitiveLargeSieveConstant
    positivity
  have hledger := standardBVChosenSmall_squareLedger_le N Q C hQpos
  have htop :
      P ^ 2 * (3 * highConductorHarmonicFactor Q R *
          primitivePrefixSquareLedgerOn
            (vaughanSmallCoeff vaughanUnitIntegerCoeff v) N
            (highConductorSet N Q C)) ≤
        M * (N : ℝ) * Real.sqrt N * Real.log (N : ℝ) ^ 10 := by
    have hratio :
        P ^ 2 * (3 * highConductorHarmonicFactor Q R *
            primitivePrefixSquareLedgerOn
              (vaughanSmallCoeff vaughanUnitIntegerCoeff v) N
              (highConductorSet N Q C)) ≤
          497664 * cLS * (N : ℝ) * Real.sqrt N * Real.log (N : ℝ) ^ 10 := by
      have hledger' :
          primitivePrefixSquareLedgerOn
              (vaughanSmallCoeff vaughanUnitIntegerCoeff v) N
              (highConductorSet N Q C) ≤
            (((Nat.log2 N + 1 : ℕ) : ℝ) ^ 2) * primitiveLargeSieveConstant N Q *
              ((v : ℝ) * Real.log ((v + 1 : ℕ) : ℝ) ^ 2) := by
        simpa [v] using hledger
      calc
        P ^ 2 * (3 * highConductorHarmonicFactor Q R *
            primitivePrefixSquareLedgerOn
              (vaughanSmallCoeff vaughanUnitIntegerCoeff v) N
              (highConductorSet N Q C))
            ≤ P ^ 2 * (3 * highConductorHarmonicFactor Q R *
                ((((Nat.log2 N + 1 : ℕ) : ℝ) ^ 2) *
                  primitiveLargeSieveConstant N Q *
                  ((v : ℝ) * Real.log ((v + 1 : ℕ) : ℝ) ^ 2))) := by
                have hmult0 : 0 ≤ 3 * highConductorHarmonicFactor Q R := by
                  nlinarith [hHH0]
                have hleft := mul_le_mul_of_nonneg_left hledger' hmult0
                exact mul_le_mul_of_nonneg_left hleft (sq_nonneg P)
        _ ≤ (144 * conductorHarmonicFactor Q ^ 4) *
            (3 * conductorHarmonicFactor Q *
              (9 * Real.log (N : ℝ) ^ 2 *
                (cLS * (N : ℝ) * Real.log (N : ℝ)) *
                (4 * Real.sqrt N * Real.log (N : ℝ) ^ 2))) := by
              have hcoef :
                  3 * highConductorHarmonicFactor Q R ≤ 3 * conductorHarmonicFactor Q := by
                nlinarith [highConductorHarmonicFactor_le Q R]
              have hcore :
                  (((Nat.log2 N + 1 : ℕ) : ℝ) ^ 2) * primitiveLargeSieveConstant N Q *
                      ((v : ℝ) * Real.log ((v + 1 : ℕ) : ℝ) ^ 2) ≤
                    9 * Real.log (N : ℝ) ^ 2 *
                      (cLS * (N : ℝ) * Real.log (N : ℝ)) *
                      (4 * Real.sqrt N * Real.log (N : ℝ) ^ 2) := by
                gcongr <;> try positivity <;>
                  first
                  | exact hlog2Sq
                  | exact hPLC
                  | exact hvLogSq
                  | exact hPLC0
              have hcore0 :
                  0 ≤ (((Nat.log2 N + 1 : ℕ) : ℝ) ^ 2) * primitiveLargeSieveConstant N Q *
                    ((v : ℝ) * Real.log ((v + 1 : ℕ) : ℝ) ^ 2) := by
                have hv0 : 0 ≤ (v : ℝ) := by positivity
                have hlogvSq0 : 0 ≤ Real.log ((v + 1 : ℕ) : ℝ) ^ 2 := sq_nonneg _
                have hV0 : 0 ≤ (v : ℝ) * Real.log ((v + 1 : ℕ) : ℝ) ^ 2 :=
                  mul_nonneg hv0 hlogvSq0
                exact mul_nonneg (mul_nonneg (by positivity) hPLC0) hV0
              have hcoef0 : 0 ≤ 3 * conductorHarmonicFactor Q := by nlinarith [hH0]
              have hmid :
                  3 * highConductorHarmonicFactor Q R *
                      ((((Nat.log2 N + 1 : ℕ) : ℝ) ^ 2) * primitiveLargeSieveConstant N Q *
                        ((v : ℝ) * Real.log ((v + 1 : ℕ) : ℝ) ^ 2)) ≤
                    3 * conductorHarmonicFactor Q *
                      (9 * Real.log (N : ℝ) ^ 2 *
                        (cLS * (N : ℝ) * Real.log (N : ℝ)) *
                        (4 * Real.sqrt N * Real.log (N : ℝ) ^ 2)) := by
                exact mul_le_mul hcoef hcore hcore0 hcoef0
              have hmid0 :
                  0 ≤ 3 * highConductorHarmonicFactor Q R *
                    ((((Nat.log2 N + 1 : ℕ) : ℝ) ^ 2) * primitiveLargeSieveConstant N Q *
                      ((v : ℝ) * Real.log ((v + 1 : ℕ) : ℝ) ^ 2)) := by
                have hcoef0 : 0 ≤ 3 * highConductorHarmonicFactor Q R := by
                  nlinarith [hHH0]
                exact mul_nonneg hcoef0 hcore0
              have hleft0 : 0 ≤ 144 * conductorHarmonicFactor Q ^ 4 := by positivity
              exact mul_le_mul hP hmid hmid0 hleft0
        _ ≤ (144 * (2 * Real.log (N : ℝ)) ^ 4) *
            (3 * (2 * Real.log (N : ℝ)) *
              (9 * Real.log (N : ℝ) ^ 2 *
                (cLS * (N : ℝ) * Real.log (N : ℝ)) *
                (4 * Real.sqrt N * Real.log (N : ℝ) ^ 2))) := by
              have hpow :
                  144 * conductorHarmonicFactor Q ^ 4 ≤
                    144 * (2 * Real.log (N : ℝ)) ^ 4 := by
                exact mul_le_mul_of_nonneg_left hHpow4 (by positivity)
              have hbulk0 :
                  0 ≤ 9 * Real.log (N : ℝ) ^ 2 *
                    (cLS * (N : ℝ) * Real.log (N : ℝ)) *
                    (4 * Real.sqrt N * Real.log (N : ℝ) ^ 2) := by
                positivity
              have hcond :
                  3 * conductorHarmonicFactor Q ≤ 3 * (2 * Real.log (N : ℝ)) := by
                nlinarith [hH]
              have hcondMul :
                  3 * conductorHarmonicFactor Q *
                      (9 * Real.log (N : ℝ) ^ 2 *
                        (cLS * (N : ℝ) * Real.log (N : ℝ)) *
                        (4 * Real.sqrt N * Real.log (N : ℝ) ^ 2)) ≤
                    3 * (2 * Real.log (N : ℝ)) *
                      (9 * Real.log (N : ℝ) ^ 2 *
                        (cLS * (N : ℝ) * Real.log (N : ℝ)) *
                        (4 * Real.sqrt N * Real.log (N : ℝ) ^ 2)) := by
                exact mul_le_mul_of_nonneg_right hcond hbulk0
              have hcondMul0 :
                  0 ≤ 3 * conductorHarmonicFactor Q *
                    (9 * Real.log (N : ℝ) ^ 2 *
                      (cLS * (N : ℝ) * Real.log (N : ℝ)) *
                      (4 * Real.sqrt N * Real.log (N : ℝ) ^ 2)) := by
                nlinarith [hH0, hbulk0]
              have hpowR0 : 0 ≤ 144 * (2 * Real.log (N : ℝ)) ^ 4 := by positivity
              exact mul_le_mul hpow hcondMul hcondMul0 hpowR0
        _ = 497664 * cLS * (N : ℝ) * Real.sqrt N * Real.log (N : ℝ) ^ 10 := by
            ring
    have hcLS0 : 0 ≤ cLS := by
      dsimp [cLS]
      positivity
    have hconst : (497664 : ℝ) * cLS ≤ M := by
      dsimp [M]
      nlinarith
    have hmul :
        497664 * cLS * (N : ℝ) * Real.sqrt N * Real.log (N : ℝ) ^ 10 ≤
          M * (N : ℝ) * Real.sqrt N * Real.log (N : ℝ) ^ 10 := by
      have hfac0 : 0 ≤ (N : ℝ) * Real.sqrt N * Real.log (N : ℝ) ^ 10 := by positivity
      have hmul' := mul_le_mul_of_nonneg_right hconst hfac0
      simpa [mul_assoc, mul_left_comm, mul_comm] using hmul'
    exact hratio.trans hmul
  have hlogDiv : Real.log (N : ℝ) ^ 10 ≤
      Real.sqrt N / Real.log N ^ (2 * (A + κ)) := by
    have hden : 0 < Real.log (N : ℝ) ^ (2 * (A + κ)) := by
      exact pow_pos hlogPos _
    apply (le_div_iff₀ hden).2
    simpa [pow_add, mul_assoc, mul_left_comm, mul_comm] using hlogPay
  have hMtoTarget :
      M * (N : ℝ) * Real.sqrt N * Real.log (N : ℝ) ^ 10 ≤
        K₀ ^ 2 * ((N : ℝ) ^ 2) / Real.log N ^ (2 * (A + κ)) := by
    have hmain :
        M * (N : ℝ) * Real.sqrt N * Real.log (N : ℝ) ^ 10 ≤
          M * (N : ℝ) * Real.sqrt N *
            (Real.sqrt N / Real.log N ^ (2 * (A + κ))) := by
      gcongr
    have hsqrt : Real.sqrt N * Real.sqrt N = (N : ℝ) := by
      simpa [pow_two] using (Real.sq_sqrt (show (0 : ℝ) ≤ N by positivity))
    have hmain' :
        M * (N : ℝ) * Real.sqrt N *
            (Real.sqrt N / Real.log N ^ (2 * (A + κ))) =
          M * (((N : ℝ) ^ 2) / Real.log N ^ (2 * (A + κ))) := by
      calc
        M * (N : ℝ) * Real.sqrt N *
            (Real.sqrt N / Real.log N ^ (2 * (A + κ)))
            = M * (((N : ℝ) * (Real.sqrt N * Real.sqrt N)) /
                Real.log N ^ (2 * (A + κ))) := by ring
        _ = M * (((N : ℝ) * (N : ℝ)) / Real.log N ^ (2 * (A + κ))) := by
          rw [hsqrt]
        _ = M * (((N : ℝ) ^ 2) / Real.log N ^ (2 * (A + κ))) := by ring
    have hKsq : M ≤ K₀ ^ 2 := by
      have hM0 : 0 ≤ M := by
        dsimp [M, cLS]
        positivity
      dsimp [K₀]
      calc
        M = (Real.sqrt M) ^ 2 := by
          symm
          exact Real.sq_sqrt hM0
        _ ≤ (Real.sqrt M) ^ 2 + 2 * Real.sqrt M + 1 := by
          nlinarith [Real.sqrt_nonneg M]
        _ = (Real.sqrt M + 1) ^ 2 := by ring
    have hfrac0 : 0 ≤ ((N : ℝ) ^ 2) / Real.log N ^ (2 * (A + κ)) := by
      have hden : 0 < Real.log N ^ (2 * (A + κ)) := pow_pos hlogPos _
      exact div_nonneg (sq_nonneg (N : ℝ)) hden.le
    let T : ℝ := ((N : ℝ) ^ 2) / Real.log N ^ (2 * (A + κ))
    have hcoef :
        M * T ≤ K₀ ^ 2 * T := by
      exact mul_le_mul_of_nonneg_right hKsq (by simpa [T] using hfrac0)
    calc
      M * (N : ℝ) * Real.sqrt N * Real.log (N : ℝ) ^ 10
          ≤ M * (N : ℝ) * Real.sqrt N *
              (Real.sqrt N / Real.log N ^ (2 * (A + κ))) := hmain
      _ = M * T := by simpa [T] using hmain'
      _ ≤ K₀ ^ 2 * T := hcoef
      _ = K₀ ^ 2 * ((N : ℝ) ^ 2) / Real.log N ^ (2 * (A + κ)) := by ring
  have hX :
      K₀ ^ 2 * ((N : ℝ) ^ 2) / Real.log N ^ (2 * (A + κ)) = (K₀ * X) ^ 2 := by
    dsimp [X]
    ring
  calc
    P ^ 2 * (3 * highConductorHarmonicFactor Q R *
        primitivePrefixSquareLedgerOn
          (vaughanSmallCoeff vaughanUnitIntegerCoeff
            (standardBVBalancedSmallCutoff N)) N
          (highConductorSet N Q C))
        = P ^ 2 * (3 * highConductorHarmonicFactor Q R *
            primitivePrefixSquareLedgerOn
              (vaughanSmallCoeff vaughanUnitIntegerCoeff v) N
              (highConductorSet N Q C)) := by rfl
    _ ≤ M * (N : ℝ) * Real.sqrt N * Real.log (N : ℝ) ^ 10 := htop
    _ ≤ K₀ ^ 2 * ((N : ℝ) ^ 2) / Real.log N ^ (2 * (A + κ)) := hMtoTarget
    _ = (K₀ * X) ^ 2 := hX

end
end AnalyticNumberTheory.LargeSieve
