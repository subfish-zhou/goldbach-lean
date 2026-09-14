import MathlibNt.AnalyticNumberTheory.LargeSieve.StandardBVBlockL1WeightedPrimitive

namespace AnalyticNumberTheory.LargeSieve

open Classical Finset Filter
open scoped BigOperators ArithmeticFunction Topology

noncomputable section

/-- Faithful Vaughan small cutoff for a fixed global modulus cutoff `Q`.
The explicit zero branch records the safe interpretation at `Q = 0`. -/
def standardBVAdaptiveSmallCutoff (Q N : ℕ) : ℕ :=
  if Q = 0 then 0
  else min (Q ^ 2) (min (standardBVBalancedSmallCutoff N) (N / Q ^ 2))

@[simp] theorem standardBVAdaptiveSmallCutoff_zero (N : ℕ) :
    standardBVAdaptiveSmallCutoff 0 N = 0 := by
  simp [standardBVAdaptiveSmallCutoff]

theorem standardBVAdaptiveSmallCutoff_le_balanced (Q N : ℕ) :
    standardBVAdaptiveSmallCutoff Q N ≤ standardBVBalancedSmallCutoff N := by
  by_cases hQ : Q = 0
  · simp [standardBVAdaptiveSmallCutoff, hQ]
  · simp only [standardBVAdaptiveSmallCutoff, hQ, if_false]
    exact (min_le_right _ _).trans (min_le_left _ _)

theorem standardBVAdaptiveSmallCutoff_le (Q N : ℕ) :
    standardBVAdaptiveSmallCutoff Q N ≤ N := by
  exact (standardBVAdaptiveSmallCutoff_le_balanced Q N).trans
    (standardBVBalancedSmallCutoff_le N)

private lemma highConductorSet_subset_Icc_one_adaptive (N Q C : ℕ) :
    highConductorSet N Q C ⊆ Finset.Icc 1 Q := by
  exact highConductorSet_subset_Icc_one N Q C

/-- Ordinary primitive prefix-maximal large sieve for an arbitrary small cutoff.
No comparison of coefficient values is used: the dependence on `v` enters only
through the established small-coefficient energy bound. -/
theorem standardBVSmall_squareLedger_le (N Q C v : ℕ) (hQ : 0 < Q) :
    primitivePrefixSquareLedgerOn
        (vaughanSmallCoeff vaughanUnitIntegerCoeff v) N
        (highConductorSet N Q C) ≤
      (((Nat.log2 N + 1 : ℕ) : ℝ) ^ 2) * primitiveLargeSieveConstant N Q *
        ((v : ℝ) * Real.log ((v + 1 : ℕ) : ℝ) ^ 2) := by
  exact standardBVSmall_squareLedger_energy_le N Q C v hQ

/-- The prefix maximum contains the nonnegative amplifier at zero. -/
private lemma discreteAbelAmplifierPrefixMax_nonneg_adaptive (N : ℕ) :
    0 ≤ discreteAbelAmplifierPrefixMax N := by
  exact discreteAbelAmplifierPrefixMax_nonneg N

set_option maxHeartbeats 3000000 in
/-- The complete weighted small square ledger is paid for any eventually
balanced-bounded cutoff, with no coefficient zeroing. -/
theorem standardBVSmall_squareLedger_payable_of_le_balanced
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
  exact standardBVSmall_weightedSquareLedger_payable cutoff hcutoff A κ B C

/-- Weighted adaptive source used as the intermediate output of the five-log
envelope payment.  Its only cutoff restriction is the balanced upper bound. -/
def StandardBVProductionAdaptiveBlockL1WeightedSource (loss : ℕ) : Prop :=
  ∀ A : ℕ,
    let B := standardBVBlockL1ModulusExponent A loss
    let C := standardBVBlockL1ConductorExponent A loss
    ∃ u v : ℕ → ℕ, (∀ N, v N ≤ standardBVBalancedSmallCutoff N) ∧
      ∃ K₁ K₂ : ℝ, 0 < K₁ ∧ 0 < K₂ ∧
        ∀ᶠ N : ℕ in Filter.atTop,
          let Q := MathlibNt.SieveTheory.LiuWeight.panModulusCutoff N (B : ℝ)
          let P := 4 * discreteAbelAmplifierPrefixMax N * conductorHarmonicFactor Q ^ 2
          ∀ hR : 0 < logConductorThreshold N C,
            let G := productionConductorBlockGeometry N Q C hR
            ProductionTypeIBlockMeanValue N (u N) (v N) loss P K₁ G ∧
              ProductionTypeIIBlockMeanValue N (u N) (v N) loss P K₂ G

/-- Adaptive bare block source.  Since the existential pair is selected after
`A`, both cutoffs may vary with `A` and `N`; no equality to a canonical cutoff
is imposed, only `v N ≤` the balanced cube-root cutoff. -/
def StandardBVProductionAdaptiveBlockL1BareSource (loss : ℕ) : Prop :=
  ∀ A : ℕ,
    let paidLoss := loss + 5
    let B := standardBVBlockL1ModulusExponent A paidLoss
    let C := standardBVBlockL1ConductorExponent A paidLoss
    ∃ u v : ℕ → ℕ, (∀ N, v N ≤ standardBVBalancedSmallCutoff N) ∧
      ∃ K₁ K₂ : ℝ, 0 < K₁ ∧ 0 < K₂ ∧
        ∀ᶠ N : ℕ in Filter.atTop,
          let Q := MathlibNt.SieveTheory.LiuWeight.panModulusCutoff N (B : ℝ)
          ∀ hR : 0 < logConductorThreshold N C,
            let G := productionConductorBlockGeometry N Q C hR
            ProductionTypeIBlockMeanValueBare N (u N) (v N) loss K₁ G ∧
              ProductionTypeIIBlockMeanValueBare N (u N) (v N) loss K₂ G

theorem standardBVProductionAdaptiveBlockL1WeightedSource_of_bare
    {loss : ℕ} (hbare : StandardBVProductionAdaptiveBlockL1BareSource loss) :
    StandardBVProductionAdaptiveBlockL1WeightedSource (loss + 5) := by
  intro A
  obtain ⟨u, v, hv, K₁, K₂, hK₁, hK₂, hsource⟩ := hbare A
  refine ⟨u, v, hv, 48 * K₁, 48 * K₂, by positivity, by positivity, ?_⟩
  filter_upwards [hsource,
    productionAbelConductorEnvelope_le_logPow_five
      (standardBVBlockL1ModulusExponent A (loss + 5))] with N hN hP
  dsimp only at hN hP ⊢
  intro hR
  rcases hN hR with ⟨hI, hII⟩
  let Q := MathlibNt.SieveTheory.LiuWeight.panModulusCutoff N
    (standardBVBlockL1ModulusExponent A (loss + 5) : ℝ)
  let G := productionConductorBlockGeometry N Q
    (standardBVBlockL1ConductorExponent A (loss + 5)) hR
  have hP' :
      4 * discreteAbelAmplifierPrefixMax N * conductorHarmonicFactor Q ^ 2 ≤
        48 * Real.log (N : ℝ) ^ 5 := by
    simpa only [Q] using hP
  exact ⟨productionTypeIBlockMeanValue_of_bare_logPow_five
      N (u N) (v N) loss
      (4 * discreteAbelAmplifierPrefixMax N * conductorHarmonicFactor Q ^ 2)
      K₁ G hP' hI,
    productionTypeIIBlockMeanValue_of_bare_logPow_five
      N (u N) (v N) loss
      (4 * discreteAbelAmplifierPrefixMax N * conductorHarmonicFactor Q ^ 2)
      K₂ G hP' hII⟩

private lemma highConductorSet_eq_interval_adaptive (N Q C : ℕ)
    (hR : 1 ≤ logConductorThreshold N C) :
    highConductorSet N Q C =
      Finset.Icc (logConductorThreshold N C + 1) Q := by
  exact highConductorSet_eq_interval N Q C hR

/-- Production block-L¹ chosen assembler.  Type-I and Type-II use one shared
pair `u,v`, with only `v N ≤ standardBVBalancedSmallCutoff N`; their block first moments
are paid by the block geometry, while the retained small mean is paid
by `standardBVSmall_squareLedger_payable_of_le_balanced` followed by the existing
high-conductor weighted Cauchy inequality. -/
theorem standardBVHighTypeITypeIIHybridChosenSource_of_adaptiveBlockL1Weighted
    {loss : ℕ} (hblock : StandardBVProductionAdaptiveBlockL1WeightedSource loss) :
    StandardBVHighTypeITypeIIHybridChosenSource := by
  intro A
  let B := standardBVBlockL1ModulusExponent A loss
  let C := standardBVBlockL1ConductorExponent A loss
  obtain ⟨u, v, hv, K₁, K₂, hK₁, hK₂, hsource⟩ := hblock A
  obtain ⟨K₀, hK₀, hsmallSource⟩ :=
    standardBVSmall_squareLedger_payable_of_le_balanced v
      (Filter.Eventually.of_forall hv) A 0 B C
  refine ⟨B, C, by simpa [B] using standardBVBlockL1_margin_B A loss,
    u, v, 10 * (K₁ + K₂) + K₀, by positivity, ?_⟩
  filter_upwards [hsource, standardBVBlockL1_scales_payable A loss,
    hsmallSource, eventually_ge_atTop (9 : ℕ)] with N hN hpay hsmallPay hN9
  dsimp only at hN hpay hsmallPay ⊢
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
      have hC : 0 < C := by
        dsimp [C, standardBVBlockL1ConductorExponent]
        omega
      exact one_lt_pow₀ hlog hC.ne'
    exact Nat.floor_pos.mpr hpow.le
  let G := productionConductorBlockGeometry N Q C hR
  rcases hN hR with ⟨hIblock, hIIblock⟩
  have hP : 0 ≤ P := by
    dsimp [P]
    exact mul_nonneg
      (mul_nonneg (by norm_num) (discreteAbelAmplifierPrefixMax_nonneg_adaptive N))
      (sq_nonneg _)
  have hI := productionTypeI_blockWeighted_to_highMean
    N Q C (u N) (v N) loss P K₁ G hP hK₁.le hIblock
  have hII := productionTypeII_blockWeighted_to_highMean
    N Q C (u N) (v N) loss P K₂ G hP hK₂.le hIIblock
  have hlarge :
      P * (highConductorVaughanTypeIMean N Q C (u N) (v N) +
        highConductorVaughanTypeIIMean N Q C (u N) (v N)) ≤
        10 * (K₁ + K₂) * (N : ℝ) / Real.log (N : ℝ) ^ A := by
    have hsum : P * (highConductorVaughanTypeIMean N Q C (u N) (v N) +
        highConductorVaughanTypeIIMean N Q C (u N) (v N)) ≤
        (K₁ + K₂) * Real.log (N : ℝ) ^ loss *
          (2 * (N : ℝ) / (R : ℝ) + 8 * (Q : ℝ) * Real.sqrt N) := by
      rw [mul_add]
      exact (add_le_add hI hII).trans_eq (by ring)
    have hp := hpay
    change Real.log (N : ℝ) ^ loss *
        (2 * (N : ℝ) / (R : ℝ) + 8 * (Q : ℝ) * Real.sqrt N) ≤
      10 * (N : ℝ) / Real.log (N : ℝ) ^ A at hp
    exact hsum.trans (by
      calc
        (K₁ + K₂) * Real.log (N : ℝ) ^ loss *
            (2 * (N : ℝ) / (R : ℝ) + 8 * (Q : ℝ) * Real.sqrt N) =
          (K₁ + K₂) * (Real.log (N : ℝ) ^ loss *
            (2 * (N : ℝ) / (R : ℝ) + 8 * (Q : ℝ) * Real.sqrt N)) := by ring
        _ ≤ (K₁ + K₂) * (10 * (N : ℝ) / Real.log (N : ℝ) ^ A) := by gcongr
        _ = 10 * (K₁ + K₂) * (N : ℝ) / Real.log (N : ℝ) ^ A := by ring)
  have hcard : ∀ d ∈ Finset.Icc (R + 1) Q,
      Fintype.card (PrimitiveCharacter d) ≤ d.totient := by
    intro d hd
    exact card_primitiveCharacter_le_totient d (by
      have hdR := (Finset.mem_Icc.mp hd).1
      omega)
  have hRone : 1 ≤ R := by omega
  have hsmallCauchy := apNormalizedPrimitiveMeanOn_high_sq_le
    (vaughanSmallCoeff vaughanUnitIntegerCoeff (v N)) N Q R hcard
  rw [← highConductorSet_eq_interval_adaptive N Q C (by simpa only [R] using hRone)] at hsmallCauchy
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
  have hsmall :
      P * highConductorVaughanSmallMean N Q C (v N) ≤
        K₀ * ((N : ℝ) / Real.log N ^ A) := by
    exact (sq_le_sq₀ (mul_nonneg hP hsmallNonneg) (by positivity)).mp hsmallSq
  calc
    P * (highConductorVaughanTypeIMean N Q C (u N) (v N) +
        highConductorVaughanTypeIIMean N Q C (u N) (v N) +
        highConductorVaughanSmallMean N Q C (v N)) =
      P * (highConductorVaughanTypeIMean N Q C (u N) (v N) +
        highConductorVaughanTypeIIMean N Q C (u N) (v N)) +
        P * highConductorVaughanSmallMean N Q C (v N) := by ring
    _ ≤ 10 * (K₁ + K₂) * (N : ℝ) / Real.log (N : ℝ) ^ A +
        K₀ * ((N : ℝ) / Real.log N ^ A) := add_le_add hlarge hsmall
    _ = (10 * (K₁ + K₂) + K₀) * (N : ℝ) /
        Real.log (N : ℝ) ^ A := by ring


/-- Five-log envelope payment followed by the generalized small-lane payment. -/
theorem standardBVHighTypeITypeIIHybridChosenSource_of_adaptiveBlockL1Bare
    {loss : ℕ} (hbare : StandardBVProductionAdaptiveBlockL1BareSource loss) :
    StandardBVHighTypeITypeIIHybridChosenSource :=
  standardBVHighTypeITypeIIHybridChosenSource_of_adaptiveBlockL1Weighted
    (standardBVProductionAdaptiveBlockL1WeightedSource_of_bare hbare)

end
end AnalyticNumberTheory.LargeSieve
