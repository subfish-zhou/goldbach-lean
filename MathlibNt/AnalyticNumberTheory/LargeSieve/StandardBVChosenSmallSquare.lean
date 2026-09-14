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

lemma highConductorSet_subset_Icc_one (N Q C : ℕ) :
    highConductorSet N Q C ⊆ Finset.Icc 1 Q := by
  intro d hd
  have hd' := (Finset.mem_filter.mp hd).1
  have hd2 := (Finset.mem_Icc.mp hd').1
  exact Finset.mem_Icc.mpr ⟨by omega, (Finset.mem_Icc.mp hd').2⟩

/-- Coefficient-faithful small-lane energy estimate, before choosing a cutoff. -/
theorem standardBVSmall_squareLedger_energy_le (N Q C v : ℕ) (hQ : 0 < Q) :
    primitivePrefixSquareLedgerOn
        (vaughanSmallCoeff vaughanUnitIntegerCoeff v) N
        (highConductorSet N Q C) ≤
      (((Nat.log2 N + 1 : ℕ) : ℝ) ^ 2) * primitiveLargeSieveConstant N Q *
        ((v : ℝ) * Real.log ((v + 1 : ℕ) : ℝ) ^ 2) := by
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

/-- Ordinary primitive prefix-maximal large sieve, specialized to the exact
production small coefficient. -/
theorem standardBVChosenSmall_squareLedger_le (N Q C : ℕ) (hQ : 0 < Q) :
    primitivePrefixSquareLedgerOn
        (vaughanSmallCoeff vaughanUnitIntegerCoeff (standardBVBalancedSmallCutoff N)) N
        (highConductorSet N Q C) ≤
      (((Nat.log2 N + 1 : ℕ) : ℝ) ^ 2) * primitiveLargeSieveConstant N Q *
        ((standardBVBalancedSmallCutoff N : ℝ) *
          Real.log ((standardBVBalancedSmallCutoff N + 1 : ℕ) : ℝ) ^ 2) := by
  exact standardBVSmall_squareLedger_energy_le N Q C (standardBVBalancedSmallCutoff N) hQ

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

/-- Uniform envelope for the complete weighted square ledger.  The coefficient
is unchanged; only its energy is bounded.  The logarithmic costs are respectively
4 (squared conductor amplifier), 1 (high harmonic), 2 (prefix maximum),
1 (large sieve), and 2 (small-coefficient energy). -/
theorem standardBVSmall_weightedSquareLedger_le_log
    (N Q R C v : ℕ) (hN : 8 ≤ N) (hQpos : 0 < Q) (hQsq : Q ^ 2 ≤ N)
    (hvN : v ≤ N) (hvSqrt : (v : ℝ) ≤ Real.sqrt N) :
    (4 * discreteAbelAmplifierPrefixMax N * conductorHarmonicFactor Q ^ 2) ^ 2 *
        (3 * highConductorHarmonicFactor Q R *
          primitivePrefixSquareLedgerOn
            (vaughanSmallCoeff vaughanUnitIntegerCoeff v) N (highConductorSet N Q C)) ≤
      497664 * (15 + 4 / Real.log 2) * (N : ℝ) * Real.sqrt N *
        Real.log (N : ℝ) ^ 10 := by
  let cLS : ℝ := 15 + 4 / Real.log 2
  let P := 4 * discreteAbelAmplifierPrefixMax N * conductorHarmonicFactor Q ^ 2
  have hlog : 1 ≤ Real.log (N : ℝ) := by
    have he1 : Real.exp 1 < (3 : ℝ) :=
      Real.exp_one_lt_d9.trans (by norm_num)
    exact (Real.lt_log_iff_exp_lt (by positivity : (0 : ℝ) < N)).2
      (he1.trans_le (by exact_mod_cast (show 3 ≤ N by omega))) |>.le
  have hlogPos : 0 < Real.log (N : ℝ) :=
    lt_of_lt_of_le zero_lt_one hlog
  have hQone : 1 ≤ Q := hQpos
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
      exact mul_nonneg
        (mul_nonneg (by norm_num) (discreteAbelAmplifierPrefixMax_nonneg N))
        (sq_nonneg _)
    calc
      P ^ 2 ≤ (12 * conductorHarmonicFactor Q ^ 2) ^ 2 :=
        pow_le_pow_left₀ hP0 hP1 2
      _ = 144 * conductorHarmonicFactor Q ^ 4 := by ring
  have hHpow4 : conductorHarmonicFactor Q ^ 4 ≤ (2 * Real.log (N : ℝ)) ^ 4 := by
    exact pow_le_pow_left₀ (conductorHarmonicFactor_nonneg Q) hH 4
  have hlog2N : (Nat.log2 N : ℝ) ≤ 2 * Real.log (N : ℝ) :=
    natLog2_cast_le_two_log (by omega)
  have hlog2N1 : ((Nat.log2 N + 1 : ℕ) : ℝ) ≤ 3 * Real.log (N : ℝ) := by
    push_cast
    linarith only [hlog2N, hlog]
  have hlog2Sq : (((Nat.log2 N + 1 : ℕ) : ℝ) ^ 2) ≤ 9 * Real.log (N : ℝ) ^ 2 := by
    calc
      (((Nat.log2 N + 1 : ℕ) : ℝ) ^ 2) ≤ (3 * Real.log (N : ℝ)) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hlog2N1 2
      _ = 9 * Real.log (N : ℝ) ^ 2 := by ring
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
      calc
        Real.log ((v + 1 : ℕ) : ℝ) ^ 2 ≤ (2 * Real.log (N : ℝ)) ^ 2 :=
          pow_le_pow_left₀ hlogv0 hlogv 2
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
    have hQsqR : (Q : ℝ) ^ 2 ≤ (N : ℝ) := by exact_mod_cast hQsq
    have hQsq1 : (1 : ℝ) ≤ (Q : ℝ) ^ 2 := by exact_mod_cast (one_le_pow₀ hQone)
    have hceil := (Nat.ceil_lt_add_one
      (div_nonneg (Real.log_nonneg hQsq1) hlog2.le)).le
    have hlogQ := Real.log_le_log (by positivity : (0 : ℝ) < (Q : ℝ) ^ 2) hQsqR
    have hcoef :
        2 * (Nat.ceil (Real.log ((Q : ℝ) ^ 2) / Real.log 2) : ℝ) + 12 ≤
          (4 / Real.log 2) * Real.log (N : ℝ) + 14 := by
      have hquot := (div_le_div_iff_of_pos_right hlog2).2 hlogQ
      have hquot0 : 0 ≤ Real.log (N : ℝ) / Real.log 2 := by positivity
      calc
        _ ≤ 4 * (Real.log (N : ℝ) / Real.log 2) + 14 := by
          linarith only [hceil, hquot, hquot0]
        _ = _ := by ring
    unfold primitiveLargeSieveConstant
    calc
      (N : ℝ) +
          (2 * (Nat.ceil (Real.log ((Q : ℝ) ^ 2) / Real.log 2) : ℝ) + 12) * (Q : ℝ) ^ 2
          ≤ (N : ℝ) + ((4 / Real.log 2) * Real.log (N : ℝ) + 14) * N := by
            gcongr
      _ ≤ cLS * (N : ℝ) * Real.log (N : ℝ) := by
        dsimp [cLS]
        nlinarith only [mul_nonneg (Nat.cast_nonneg N) (sub_nonneg.mpr hlog)]
  have hPLC0 : 0 ≤ primitiveLargeSieveConstant N Q := by
    unfold primitiveLargeSieveConstant
    positivity
  have hledger := standardBVSmall_squareLedger_energy_le N Q C v hQpos
  calc
    P ^ 2 * (3 * highConductorHarmonicFactor Q R *
        primitivePrefixSquareLedgerOn
          (vaughanSmallCoeff vaughanUnitIntegerCoeff v) N (highConductorSet N Q C))
        ≤ P ^ 2 * (3 * highConductorHarmonicFactor Q R *
          ((((Nat.log2 N + 1 : ℕ) : ℝ) ^ 2) * primitiveLargeSieveConstant N Q *
            ((v : ℝ) * Real.log ((v + 1 : ℕ) : ℝ) ^ 2))) := by
              gcongr
    _ ≤ (144 * (2 * Real.log (N : ℝ)) ^ 4) *
        (3 * (2 * Real.log (N : ℝ)) *
          (9 * Real.log (N : ℝ) ^ 2 * (cLS * (N : ℝ) * Real.log (N : ℝ)) *
            (4 * Real.sqrt N * Real.log (N : ℝ) ^ 2))) := by
              have hPlog := hP.trans (mul_le_mul_of_nonneg_left hHpow4 (by norm_num))
              gcongr
    _ = 497664 * cLS * (N : ℝ) * Real.sqrt N * Real.log (N : ℝ) ^ 10 := by ring

/-- One payment theorem for all eventually balanced-bounded small cutoffs. -/
theorem standardBVSmall_weightedSquareLedger_payable
    (cutoff : ℕ → ℕ)
    (hcutoff : ∀ᶠ N : ℕ in Filter.atTop,
      cutoff N ≤ standardBVBalancedSmallCutoff N)
    (A κ B C : ℕ) :
    ∃ K₀ : ℝ, 0 < K₀ ∧
      ∀ᶠ N : ℕ in Filter.atTop,
        let Q := MathlibNt.SieveTheory.LiuWeight.panModulusCutoff N (B : ℝ)
        let R := logConductorThreshold N C
        let P := 4 * discreteAbelAmplifierPrefixMax N * conductorHarmonicFactor Q ^ 2
        let X := (N : ℝ) / Real.log N ^ (A + κ)
        P ^ 2 * (3 * highConductorHarmonicFactor Q R *
            primitivePrefixSquareLedgerOn
              (vaughanSmallCoeff vaughanUnitIntegerCoeff
                (cutoff N)) N
              (highConductorSet N Q C)) ≤ (K₀ * X) ^ 2 := by
  let M : ℝ := 497664 * (15 + 4 / Real.log 2)
  let K₀ : ℝ := Real.sqrt M + 1
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hK : M ≤ K₀ ^ 2 := by
    dsimp [K₀]
    nlinarith only [Real.sq_sqrt hM, Real.sqrt_nonneg M]
  refine ⟨K₀, by positivity, ?_⟩
  filter_upwards [hcutoff, eventually_ge_atTop (8 : ℕ),
    log_pow_le_sqrt_eventually (10 + 2 * (A + κ)),
    log_pow_le_sqrt_eventually B] with N hcut hN hlogPay hcutGrow
  dsimp only
  let Q := MathlibNt.SieveTheory.LiuWeight.panModulusCutoff N (B : ℝ)
  have hlogPos : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hQone : 1 ≤ Q := by
    dsimp [Q, MathlibNt.SieveTheory.LiuWeight.panModulusCutoff]
    have hdenPos : 0 < Real.log (N : ℝ) ^ (B : ℝ) := by
      simpa [Real.rpow_natCast] using pow_pos hlogPos B
    have hcutGrow' : Real.log (N : ℝ) ^ (B : ℝ) ≤ (N : ℝ) ^ (1 / 2 : ℝ) := by
      simpa [Real.sqrt_eq_rpow, Real.rpow_natCast] using hcutGrow
    apply Nat.le_floor
    simpa only [Nat.cast_one] using (one_le_div₀ hdenPos).2 hcutGrow'
  have hQpos : 0 < Q := by omega
  have hQsq : Q ^ 2 ≤ N := by
    simpa [Q] using MathlibNt.SieveTheory.LiuWeight.panModulusCutoff_sq_le
      N (B : ℝ) (by omega) (by positivity : 0 ≤ (B : ℝ))
  have hvN := hcut.trans (standardBVBalancedSmallCutoff_le N)
  have hvSqrt : (cutoff N : ℝ) ≤ Real.sqrt N :=
    (Nat.cast_le.mpr hcut).trans (standardBVBalancedSmallCutoff_cast_le_sqrt N)
  have htop := standardBVSmall_weightedSquareLedger_le_log N Q
    (logConductorThreshold N C) C (cutoff N) hN hQpos hQsq hvN hvSqrt
  have hlogDiv : Real.log (N : ℝ) ^ 10 ≤
      Real.sqrt N / Real.log N ^ (2 * (A + κ)) := by
    apply (le_div_iff₀ (pow_pos hlogPos _)).2
    simpa only [pow_add] using hlogPay
  refine htop.trans ?_
  calc
    M * (N : ℝ) * Real.sqrt N * Real.log (N : ℝ) ^ 10
        ≤ M * (N : ℝ) * Real.sqrt N *
          (Real.sqrt N / Real.log N ^ (2 * (A + κ))) := by gcongr
    _ = M * ((N : ℝ) ^ 2 / Real.log N ^ (2 * (A + κ))) := by
      calc
        _ = M * ((N : ℝ) * (Real.sqrt N * Real.sqrt N) /
            Real.log N ^ (2 * (A + κ))) := by ring
        _ = _ := by rw [Real.mul_self_sqrt (Nat.cast_nonneg N)]; ring
    _ ≤ K₀ ^ 2 * ((N : ℝ) ^ 2 / Real.log N ^ (2 * (A + κ))) := by gcongr
    _ = (K₀ * ((N : ℝ) / Real.log N ^ (A + κ))) ^ 2 := by ring

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
  exact standardBVSmall_weightedSquareLedger_payable standardBVBalancedSmallCutoff
    (Filter.Eventually.of_forall fun _ => le_rfl) A κ B C

end
end AnalyticNumberTheory.LargeSieve
