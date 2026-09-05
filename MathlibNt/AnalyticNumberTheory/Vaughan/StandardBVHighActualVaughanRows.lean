

import MathlibNt.AnalyticNumberTheory.Vaughan.ConductorLocalVaughanShellLedgers
import MathlibNt.AnalyticNumberTheory.Vaughan.HighConductorVaughanTypeIIShellSum
import MathlibNt.AnalyticNumberTheory.Vaughan.VaughanTypeILongCoeffMomentExplicit
import MathlibNt.AnalyticNumberTheory.LargeSieve.StandardBVHighHybridFeasibility
import MathlibNt.AnalyticNumberTheory.Vaughan.VaughanDirectAPNormalizedTypeIIActualPhysical
import MathlibNt.AnalyticNumberTheory.LargeSieve.StandardBVChosenSmallSquare

/-!
 # Actual Vaughan square ledgers produce the moving high source

The sole analytic input in this file is a square-ledger theorem for the three
literal Vaughan coefficient rows on the retained primitive-conductor interval.
In particular, it is not an estimate for the final unsquared high mean.  The
fixed exponent `κ` is the complete reserve for shell counts, prefix maxima,
Möbius/logarithmic convolution coefficients, and the conductor/Abel envelopes.
-/

namespace AnalyticNumberTheory.LargeSieve

open Classical Finset Filter
open scoped BigOperators ArithmeticFunction Topology

noncomputable section

/-- The sum of the three literal Vaughan square ledgers on the actual high
conductor set.  The Type-I and Type-II entries are the production coefficients,
not abstract test rows and not high-mean conclusions. -/
def actualVaughanRowsSquareLedger (N Q C u v : ℕ) : ℝ :=
  primitivePrefixSquareLedgerOn
      (vaughanTypeICoeff vaughanUnitIntegerCoeff u v) N
      (highConductorSet N Q C) +
    primitivePrefixSquareLedgerOn
      (vaughanTypeIICoeff vaughanUnitIntegerCoeff u v) N
      (highConductorSet N Q C) +
    primitivePrefixSquareLedgerOn
      (vaughanSmallCoeff vaughanUnitIntegerCoeff v) N
      (highConductorSet N Q C)

lemma actualVaughanRowsSquareLedger_nonneg (N Q C u v : ℕ) :
    0 ≤ actualVaughanRowsSquareLedger N Q C u v := by
  unfold actualVaughanRowsSquareLedger primitivePrefixSquareLedgerOn
  have hledger (a : ℤ → ℂ) :
      0 ≤ ∑ d ∈ highConductorSet N Q C,
        ((d : ℝ) / (d.totient : ℝ)) *
          ∑ ψ : PrimitiveCharacter d,
            primitiveCharacterPrefixMaxSquare a 0 N d ψ := by
    apply Finset.sum_nonneg
    intro d hd
    exact mul_nonneg (div_nonneg (by positivity) (by positivity))
      (Finset.sum_nonneg fun ψ hψ =>
        primitiveCharacterPrefixMaxSquare_nonneg a 0 N d ψ)
  exact add_nonneg (add_nonneg (hledger _) (hledger _)) (hledger _)

/-- The fixed polylogarithmic reserve attached to the actual shell aggregation.
The inequality is deliberately frozen at square-ledger level.  Its left side
contains the exact Abel/conductor envelopes and the exact production Vaughan
rows; it neither mentions `StandardBVHighTypeITypeIIHybridMovingSource` nor
assumes an unsquared high mean.

The established production ingredients feeding this interface are:
* the uniform Type-I `μ/log` convolution moment with exponent `5`;
* the actual first/product-dyadic Type-I row partition;
* the canonical hyperbolic Type-II collected-prefix partition and its fixed-row
  prefix ledger; and
* one finite Cauchy payment for the three Vaughan lanes.
-/
def ActualVaughanRowsSquareLedgerSource (κ : ℕ) : Prop :=
  ∀ A C B : ℕ, ∃ u v : ℕ → ℕ, ∃ K : ℝ, 0 < K ∧
    ∀ᶠ N : ℕ in Filter.atTop,
      let Q := MathlibNt.SieveTheory.LiuWeight.panModulusCutoff N (B : ℝ)
      let R := logConductorThreshold N C
      let P := 4 * discreteAbelAmplifierPrefixMax N * conductorHarmonicFactor Q ^ 2
      P ^ 2 * (3 * highConductorHarmonicFactor Q R *
          actualVaughanRowsSquareLedger N Q C (u N) (v N)) ≤
        (K * (N : ℝ) / Real.log N ^ (A + κ)) ^ 2

/-- Canonical square-ledger source with faithful quantifier order: for each
requested decay `A`, choose `B,C` first, then `u,v,K`.  The margin on `B` is
exactly the one required by the Standard-BV elementary payload. -/
def ActualVaughanRowsChosenSquareLedgerSource (κ : ℕ) : Prop :=
  ∀ A : ℕ, ∃ B C : ℕ, A + 3 ≤ B ∧
    ∃ u v : ℕ → ℕ, ∃ K : ℝ, 0 < K ∧
      ∀ᶠ N : ℕ in Filter.atTop,
        let Q := MathlibNt.SieveTheory.LiuWeight.panModulusCutoff N (B : ℝ)
        let R := logConductorThreshold N C
        let P := 4 * discreteAbelAmplifierPrefixMax N * conductorHarmonicFactor Q ^ 2
        P ^ 2 * (3 * highConductorHarmonicFactor Q R *
            actualVaughanRowsSquareLedger N Q C (u N) (v N)) ≤
          (K * (N : ℝ) / Real.log N ^ (A + κ)) ^ 2

/-- Source-faithful separated chosen source.  Its only analytic inputs are the
exact production Type-I and Type-II ledgers.  Both are evaluated at the shared
chosen cutoff; the exact small coefficient is paid internally by the adapter. -/
def ActualVaughanRowsComponentwiseChosenSquareLedgerSource (κ : ℕ) : Prop :=
  ∀ A : ℕ, ∃ B C : ℕ, A + 3 ≤ B ∧
    ∃ u v : ℕ → ℕ, v = standardBVBalancedSmallCutoff ∧ ∃ K₁ K₂ : ℝ,
      0 < K₁ ∧ 0 < K₂ ∧
      ∀ᶠ N : ℕ in Filter.atTop,
        let Q := MathlibNt.SieveTheory.LiuWeight.panModulusCutoff N (B : ℝ)
        let R := logConductorThreshold N C
        let P := 4 * discreteAbelAmplifierPrefixMax N * conductorHarmonicFactor Q ^ 2
        let X := (N : ℝ) / Real.log N ^ (A + κ)
        P ^ 2 * (3 * highConductorHarmonicFactor Q R *
            primitivePrefixSquareLedgerOn
              (vaughanTypeICoeff vaughanUnitIntegerCoeff (u N)
                (v N)) N
              (highConductorSet N Q C)) ≤ (K₁ * X) ^ 2 ∧
          P ^ 2 * (3 * highConductorHarmonicFactor Q R *
            primitivePrefixSquareLedgerOn
              (vaughanTypeIICoeff vaughanUnitIntegerCoeff (u N)
                (v N)) N
              (highConductorSet N Q C)) ≤ (K₂ * X) ^ 2

/-- Adding the two analytic ledgers and the internally paid exact small ledger
yields the canonical chosen total source. -/
theorem actualVaughanRowsChosenSquareLedgerSource_of_componentwise
    {κ : ℕ} (hrows : ActualVaughanRowsComponentwiseChosenSquareLedgerSource κ) :
    ActualVaughanRowsChosenSquareLedgerSource κ := by
  intro A
  obtain ⟨B, C, hAB, u, v, hv, K₁, K₂, hK₁, hK₂, hrowsN⟩ := hrows A
  obtain ⟨K₀, hK₀, hsmallN⟩ := standardBVChosenSmall_squareLedger_payable A κ B C
  refine ⟨B, C, hAB, u, v, K₁ + K₂ + K₀, by positivity, ?_⟩
  filter_upwards [hrowsN, hsmallN] with N hN hsmall
  dsimp only at hN hsmall ⊢
  rcases hN with ⟨hI, hII⟩
  have hKsq : K₁ ^ 2 + K₂ ^ 2 + K₀ ^ 2 ≤ (K₁ + K₂ + K₀) ^ 2 := by
    nlinarith [mul_pos hK₁ hK₂, mul_pos hK₁ hK₀, mul_pos hK₂ hK₀]
  unfold actualVaughanRowsSquareLedger
  calc
    _ = (4 * discreteAbelAmplifierPrefixMax N *
            conductorHarmonicFactor
              (MathlibNt.SieveTheory.LiuWeight.panModulusCutoff N (B : ℝ)) ^ 2) ^ 2 *
          (3 * highConductorHarmonicFactor
              (MathlibNt.SieveTheory.LiuWeight.panModulusCutoff N (B : ℝ))
              (logConductorThreshold N C) *
            primitivePrefixSquareLedgerOn
              (vaughanTypeICoeff vaughanUnitIntegerCoeff (u N) (v N)) N
              (highConductorSet N
                (MathlibNt.SieveTheory.LiuWeight.panModulusCutoff N (B : ℝ)) C)) +
        (4 * discreteAbelAmplifierPrefixMax N *
            conductorHarmonicFactor
              (MathlibNt.SieveTheory.LiuWeight.panModulusCutoff N (B : ℝ)) ^ 2) ^ 2 *
          (3 * highConductorHarmonicFactor
              (MathlibNt.SieveTheory.LiuWeight.panModulusCutoff N (B : ℝ))
              (logConductorThreshold N C) *
            primitivePrefixSquareLedgerOn
              (vaughanTypeIICoeff vaughanUnitIntegerCoeff (u N) (v N)) N
              (highConductorSet N
                (MathlibNt.SieveTheory.LiuWeight.panModulusCutoff N (B : ℝ)) C)) +
        (4 * discreteAbelAmplifierPrefixMax N *
            conductorHarmonicFactor
              (MathlibNt.SieveTheory.LiuWeight.panModulusCutoff N (B : ℝ)) ^ 2) ^ 2 *
          (3 * highConductorHarmonicFactor
              (MathlibNt.SieveTheory.LiuWeight.panModulusCutoff N (B : ℝ))
              (logConductorThreshold N C) *
            primitivePrefixSquareLedgerOn
              (vaughanSmallCoeff vaughanUnitIntegerCoeff (v N)) N
              (highConductorSet N
                (MathlibNt.SieveTheory.LiuWeight.panModulusCutoff N (B : ℝ)) C)) := by ring
    _ ≤ (K₁ * ((N : ℝ) / Real.log N ^ (A + κ))) ^ 2 +
          (K₂ * ((N : ℝ) / Real.log N ^ (A + κ))) ^ 2 +
          (K₀ * ((N : ℝ) / Real.log N ^ (A + κ))) ^ 2 := by
      simpa only [hv] using
        add_le_add (add_le_add hI hII) hsmall
    _ = (K₁ ^ 2 + K₂ ^ 2 + K₀ ^ 2) *
          ((N : ℝ) / Real.log N ^ (A + κ)) ^ 2 := by ring
    _ ≤ (K₁ + K₂ + K₀) ^ 2 *
          ((N : ℝ) / Real.log N ^ (A + κ)) ^ 2 :=
      mul_le_mul_of_nonneg_right hKsq (sq_nonneg _)
    _ = ((K₁ + K₂ + K₀) * (N : ℝ) /
          Real.log N ^ (A + κ)) ^ 2 := by ring

/-- Compatibility adapter: the old uniformly quantified square source is
strictly stronger than the canonical chosen-cutoff source. -/
theorem actualVaughanRowsChosenSquareLedgerSource_of_legacy
    {κ : ℕ} (hrows : ActualVaughanRowsSquareLedgerSource κ) :
    ActualVaughanRowsChosenSquareLedgerSource κ := by
  intro A
  refine ⟨A + 3, 1, le_rfl, ?_⟩
  exact hrows A 1 (A + 3)

private lemma highConductorSet_eq_interval (N Q C : ℕ)
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

private lemma three_sq_le_three_sum_sq {x y z : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    (x + y + z) ^ 2 ≤ 3 * (x ^ 2 + y ^ 2 + z ^ 2) := by
  nlinarith [sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z)]

/-- The actual high Vaughan hybrid is extracted from the source-specific square
ledger by weighted conductor Cauchy.  This is the only passage from squares to
an unsquared mean. -/
theorem highConductorVaughanHybrid_sq_le_actualRowsLedger
    (N Q C u v : ℕ) (hRpos : 1 ≤ logConductorThreshold N C) :
    (highConductorVaughanTypeIMean N Q C u v +
        highConductorVaughanTypeIIMean N Q C u v +
        highConductorVaughanSmallMean N Q C v) ^ 2 ≤
      3 * highConductorHarmonicFactor Q (logConductorThreshold N C) *
        actualVaughanRowsSquareLedger N Q C u v := by
  let R := logConductorThreshold N C
  let S := Finset.Icc (R + 1) Q
  have hcard : ∀ d ∈ S, Fintype.card (PrimitiveCharacter d) ≤ d.totient := by
    intro d hd
    exact card_primitiveCharacter_le_totient d (by
      have := (Finset.mem_Icc.mp hd).1
      omega)
  have hI := apNormalizedPrimitiveMeanOn_high_sq_le
    (vaughanTypeICoeff vaughanUnitIntegerCoeff u v) N Q R hcard
  have hII := apNormalizedPrimitiveMeanOn_high_sq_le
    (vaughanTypeIICoeff vaughanUnitIntegerCoeff u v) N Q R hcard
  have hS := apNormalizedPrimitiveMeanOn_high_sq_le
    (vaughanSmallCoeff vaughanUnitIntegerCoeff v) N Q R hcard
  rw [← highConductorSet_eq_interval N Q C hRpos] at hI hII hS
  have hnI : 0 ≤ highConductorVaughanTypeIMean N Q C u v := by
    unfold highConductorVaughanTypeIMean apNormalizedPrimitiveMeanOn
    exact Finset.sum_nonneg fun d hd => mul_nonneg (inv_nonneg.mpr (by positivity))
      (Finset.sum_nonneg fun ψ hψ => primitivePrefixAmplitude_nonneg _ _ _ _)
  have hnII : 0 ≤ highConductorVaughanTypeIIMean N Q C u v := by
    unfold highConductorVaughanTypeIIMean apNormalizedPrimitiveMeanOn
    exact Finset.sum_nonneg fun d hd => mul_nonneg (inv_nonneg.mpr (by positivity))
      (Finset.sum_nonneg fun ψ hψ => primitivePrefixAmplitude_nonneg _ _ _ _)
  have hnS : 0 ≤ highConductorVaughanSmallMean N Q C v := by
    unfold highConductorVaughanSmallMean apNormalizedPrimitiveMeanOn
    exact Finset.sum_nonneg fun d hd => mul_nonneg (inv_nonneg.mpr (by positivity))
      (Finset.sum_nonneg fun ψ hψ => primitivePrefixAmplitude_nonneg _ _ _ _)
  refine (three_sq_le_three_sum_sq hnI hnII hnS).trans ?_
  unfold actualVaughanRowsSquareLedger
  have hadd := add_le_add (add_le_add hI hII) hS
  calc
    3 * (_ ^ 2 + _ ^ 2 + _ ^ 2) ≤
        3 * (highConductorHarmonicFactor Q R * _ +
          highConductorHarmonicFactor Q R * _ +
          highConductorHarmonicFactor Q R * _) :=
      mul_le_mul_of_nonneg_left hadd (by norm_num)
    _ = 3 * highConductorHarmonicFactor Q R * (_ + _ + _) := by ring

/-- A chosen-cutoff square-ledger theorem for the actual Vaughan rows, with one
fixed polylogarithmic reserve `κ`, inhabits the canonical chosen high source. -/
theorem standardBVHighTypeITypeIIHybridChosenSource_of_actualRows
    {κ : ℕ} (hrows : ActualVaughanRowsChosenSquareLedgerSource κ) :
    StandardBVHighTypeITypeIIHybridChosenSource := by
  intro A
  obtain ⟨B, C, hAB, u, v, K, hK, hrowsN⟩ := hrows A
  refine ⟨B, C, hAB, u, v, K, hK, ?_⟩
  filter_upwards [hrowsN, eventually_ge_atTop (3 : ℕ)] with N hledger hN
  let Q := MathlibNt.SieveTheory.LiuWeight.panModulusCutoff N (B : ℝ)
  let R := logConductorThreshold N C
  let P := 4 * discreteAbelAmplifierPrefixMax N * conductorHarmonicFactor Q ^ 2
  let H := highConductorVaughanTypeIMean N Q C (u N) (v N) +
    highConductorVaughanTypeIIMean N Q C (u N) (v N) +
    highConductorVaughanSmallMean N Q C (v N)
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
  have hH : 0 ≤ H := by
    dsimp [H]
    exact add_nonneg (add_nonneg
      (by unfold highConductorVaughanTypeIMean apNormalizedPrimitiveMeanOn
          exact Finset.sum_nonneg fun d hd =>
            mul_nonneg (inv_nonneg.mpr (by positivity))
              (Finset.sum_nonneg fun ψ hψ => primitivePrefixAmplitude_nonneg _ _ _ _))
      (by unfold highConductorVaughanTypeIIMean apNormalizedPrimitiveMeanOn
          exact Finset.sum_nonneg fun d hd =>
            mul_nonneg (inv_nonneg.mpr (by positivity))
              (Finset.sum_nonneg fun ψ hψ => primitivePrefixAmplitude_nonneg _ _ _ _)))
      (by unfold highConductorVaughanSmallMean apNormalizedPrimitiveMeanOn
          exact Finset.sum_nonneg fun d hd =>
            mul_nonneg (inv_nonneg.mpr (by positivity))
              (Finset.sum_nonneg fun ψ hψ => primitivePrefixAmplitude_nonneg _ _ _ _))
  have hRpos : 1 ≤ R := by
    dsimp [R, logConductorThreshold]
    have hlog0 : 1 ≤ Real.log (N : ℝ) := by
      have he1 : Real.exp 1 < (3 : ℝ) :=
        Real.exp_one_lt_d9.trans (by norm_num)
      exact (Real.lt_log_iff_exp_lt (by positivity : (0 : ℝ) < N)).2
        (he1.trans_le (by exact_mod_cast hN)) |>.le
    have hp : ((1 : ℕ) : ℝ) ≤ Real.log (N : ℝ) ^ C := by simpa using one_le_pow₀ hlog0
    exact Nat.le_floor hp
  have hsqH := highConductorVaughanHybrid_sq_le_actualRowsLedger
    N Q C (u N) (v N) (by simpa [R] using hRpos)
  have hsq : (P * H) ^ 2 ≤
      (K * (N : ℝ) / Real.log N ^ (A + κ)) ^ 2 := by
    rw [mul_pow]
    exact (mul_le_mul_of_nonneg_left hsqH (sq_nonneg P)).trans (by
      simpa [Q, R, P] using hledger)
  have hlog : 1 ≤ Real.log (N : ℝ) := by
    have he1 : Real.exp 1 < (3 : ℝ) :=
      Real.exp_one_lt_d9.trans (by norm_num)
    have hexp : Real.exp 1 < (N : ℝ) :=
      he1.trans_le (by exact_mod_cast hN)
    exact (Real.lt_log_iff_exp_lt (by positivity : (0 : ℝ) < N)).2 hexp |>.le
  have hden : 0 < Real.log (N : ℝ) ^ (A + κ) :=
    pow_pos (lt_of_lt_of_le (by norm_num) hlog) _
  have htarget0 : 0 ≤ K * (N : ℝ) / Real.log N ^ (A + κ) := by positivity
  have hroot : P * H ≤ K * (N : ℝ) / Real.log N ^ (A + κ) :=
    (sq_le_sq₀ (mul_nonneg hP hH) htarget0).mp hsq
  have hpow : Real.log (N : ℝ) ^ A ≤ Real.log N ^ (A + κ) := by
    rw [pow_add]
    exact le_mul_of_one_le_right (pow_nonneg (by positivity) A)
      (one_le_pow₀ hlog)
  have hweaken : K * (N : ℝ) / Real.log N ^ (A + κ) ≤
      K * (N : ℝ) / Real.log N ^ A := by
    exact div_le_div_of_nonneg_left (mul_nonneg hK.le (by positivity))
      (pow_pos (by positivity) A) hpow
  exact hroot.trans hweaken

/-- Legacy compatibility endpoint.  New production code should use
`standardBVHighTypeITypeIIHybridChosenSource_of_actualRows`; this wrapper keeps
the old all-`B,C` API callable without making it canonical. -/
theorem standardBVHighTypeITypeIIHybridMovingSource_of_actualRowsSquareLedger
    {κ : ℕ} (hrows : ActualVaughanRowsSquareLedgerSource κ) :
    StandardBVHighTypeITypeIIHybridMovingSource := by
  intro A C B
  obtain ⟨u, v, K, hK, hrowsN⟩ := hrows A C B
  refine ⟨u, v, K, hK, ?_⟩
  filter_upwards [hrowsN, eventually_ge_atTop (3 : ℕ)] with N hledger hN
  let Q := MathlibNt.SieveTheory.LiuWeight.panModulusCutoff N (B : ℝ)
  let R := logConductorThreshold N C
  let P := 4 * discreteAbelAmplifierPrefixMax N * conductorHarmonicFactor Q ^ 2
  let H := highConductorVaughanTypeIMean N Q C (u N) (v N) +
    highConductorVaughanTypeIIMean N Q C (u N) (v N) +
    highConductorVaughanSmallMean N Q C (v N)
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
  have hH : 0 ≤ H := by
    dsimp [H]
    exact add_nonneg (add_nonneg
      (by unfold highConductorVaughanTypeIMean apNormalizedPrimitiveMeanOn
          exact Finset.sum_nonneg fun d hd =>
            mul_nonneg (inv_nonneg.mpr (by positivity))
              (Finset.sum_nonneg fun ψ hψ => primitivePrefixAmplitude_nonneg _ _ _ _))
      (by unfold highConductorVaughanTypeIIMean apNormalizedPrimitiveMeanOn
          exact Finset.sum_nonneg fun d hd =>
            mul_nonneg (inv_nonneg.mpr (by positivity))
              (Finset.sum_nonneg fun ψ hψ => primitivePrefixAmplitude_nonneg _ _ _ _)))
      (by unfold highConductorVaughanSmallMean apNormalizedPrimitiveMeanOn
          exact Finset.sum_nonneg fun d hd =>
            mul_nonneg (inv_nonneg.mpr (by positivity))
              (Finset.sum_nonneg fun ψ hψ => primitivePrefixAmplitude_nonneg _ _ _ _))
  have hRpos : 1 ≤ R := by
    dsimp [R, logConductorThreshold]
    have hlog0 : 1 ≤ Real.log (N : ℝ) := by
      have he1 : Real.exp 1 < (3 : ℝ) :=
        Real.exp_one_lt_d9.trans (by norm_num)
      exact (Real.lt_log_iff_exp_lt (by positivity : (0 : ℝ) < N)).2
        (he1.trans_le (by exact_mod_cast hN)) |>.le
    have hp : ((1 : ℕ) : ℝ) ≤ Real.log (N : ℝ) ^ C := by simpa using one_le_pow₀ hlog0
    exact Nat.le_floor hp
  have hsqH := highConductorVaughanHybrid_sq_le_actualRowsLedger
    N Q C (u N) (v N) (by simpa [R] using hRpos)
  have hsq : (P * H) ^ 2 ≤
      (K * (N : ℝ) / Real.log N ^ (A + κ)) ^ 2 := by
    rw [mul_pow]
    exact (mul_le_mul_of_nonneg_left hsqH (sq_nonneg P)).trans (by
      simpa [Q, R, P] using hledger)
  have hlog : 1 ≤ Real.log (N : ℝ) := by
    have he1 : Real.exp 1 < (3 : ℝ) :=
      Real.exp_one_lt_d9.trans (by norm_num)
    have hexp : Real.exp 1 < (N : ℝ) :=
      he1.trans_le (by exact_mod_cast hN)
    exact (Real.lt_log_iff_exp_lt (by positivity : (0 : ℝ) < N)).2 hexp |>.le
  have hden : 0 < Real.log (N : ℝ) ^ (A + κ) :=
    pow_pos (lt_of_lt_of_le (by norm_num) hlog) _
  have htarget0 : 0 ≤ K * (N : ℝ) / Real.log N ^ (A + κ) := by positivity
  have hroot : P * H ≤ K * (N : ℝ) / Real.log N ^ (A + κ) :=
    (sq_le_sq₀ (mul_nonneg hP hH) htarget0).mp hsq
  have hpow : Real.log (N : ℝ) ^ A ≤ Real.log N ^ (A + κ) := by
    rw [pow_add]
    exact le_mul_of_one_le_right (pow_nonneg (by positivity) A)
      (one_le_pow₀ hlog)
  have hweaken : K * (N : ℝ) / Real.log N ^ (A + κ) ≤
      K * (N : ℝ) / Real.log N ^ A := by
    exact div_le_div_of_nonneg_left (mul_nonneg hK.le (by positivity))
      (pow_pos (by positivity) A) hpow
  exact hroot.trans hweaken

end
end AnalyticNumberTheory.LargeSieve
