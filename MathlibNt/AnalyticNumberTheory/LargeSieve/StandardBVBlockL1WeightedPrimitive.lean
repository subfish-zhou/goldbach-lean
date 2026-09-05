

import MathlibNt.AnalyticNumberTheory.Vaughan.StandardBVHighActualVaughanRows
import MathlibNt.AnalyticNumberTheory.LargeSieve.ImprimitiveConductorWeightLinear
import MathlibNt.AnalyticNumberTheory.LargeSieve.ProductionDyadicConductorGeometry
import MathlibNt.AnalyticNumberTheory.LargeSieve.StandardBVElementaryPayments

/-!
 # Block-L¹ weighted primitive consumers for the production Vaughan rows

The analytic hypotheses in this file are block-local first-moment estimates for
exactly the production Type-I and Type-II coefficients.  The finite consumer
converts `d / φ(d)` to the AP normalization on each block, reindexes a disjoint
finite block partition exactly, and then uses only the two scalar geometric
ledgers.  The small lane is the production coefficient at
`standardBVBalancedSmallCutoff`, hence is retained and paid through its square
ledger plus high-conductor Cauchy.  The former `v = min N 1` path remains only
as an explicitly named compatibility wrapper.
-/

namespace AnalyticNumberTheory.LargeSieve

open Classical Finset Filter
open scoped BigOperators ArithmeticFunction Topology

noncomputable section

/-- The block-local `d / φ(d)` first moment, with the exact production prefix
amplitude. -/
def blockWeightedPrimitiveMean
    (a : ℤ → ℂ) (N : ℕ) (S : Finset ℕ) : ℝ :=
  ∑ d ∈ S, ((d : ℝ) / (d.totient : ℝ)) *
    ∑ ψ : PrimitiveCharacter d, primitivePrefixAmplitude a N d ψ

lemma blockWeightedPrimitiveMean_nonneg
    (a : ℤ → ℂ) (N : ℕ) (S : Finset ℕ) :
    0 ≤ blockWeightedPrimitiveMean a N S := by
  unfold blockWeightedPrimitiveMean
  exact Finset.sum_nonneg fun d hd =>
    mul_nonneg (div_nonneg (by positivity) (by positivity))
      (Finset.sum_nonneg fun ψ hψ => primitivePrefixAmplitude_nonneg _ _ _ _)

/-- Exact pointwise normalization payment on a positive conductor block. -/
theorem apNormalizedPrimitiveMeanOn_le_inv_mul_blockWeighted
    (a : ℤ → ℂ) (N L : ℕ) (S : Finset ℕ) (hL : 0 < L)
    (hlevels : ∀ d ∈ S, L ≤ d) :
    apNormalizedPrimitiveMeanOn a N S ≤
      (1 / (L : ℝ)) * blockWeightedPrimitiveMean a N S := by
  unfold apNormalizedPrimitiveMeanOn blockWeightedPrimitiveMean
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro d hd
  have hd0 : 0 < d := hL.trans_le (hlevels d hd)
  have hφ : (0 : ℝ) < d.totient := by
    exact_mod_cast Nat.totient_pos.mpr hd0
  have hsum : 0 ≤ ∑ ψ : PrimitiveCharacter d,
      primitivePrefixAmplitude a N d ψ :=
    Finset.sum_nonneg fun ψ hψ => primitivePrefixAmplitude_nonneg _ _ _ _
  have hinv : (1 / (d : ℝ)) ≤ 1 / (L : ℝ) :=
    one_div_le_one_div_of_le (by exact_mod_cast hL)
      (by exact_mod_cast hlevels d hd)
  calc
    ((d.totient : ℝ)⁻¹) * ∑ ψ : PrimitiveCharacter d,
        primitivePrefixAmplitude a N d ψ =
        (1 / (d : ℝ)) * (((d : ℝ) / (d.totient : ℝ)) *
          ∑ ψ : PrimitiveCharacter d, primitivePrefixAmplitude a N d ψ) := by
      field_simp
    _ ≤ (1 / (L : ℝ)) * (((d : ℝ) / (d.totient : ℝ)) *
          ∑ ψ : PrimitiveCharacter d, primitivePrefixAmplitude a N d ψ) := by
      exact mul_le_mul_of_nonneg_right hinv
        (mul_nonneg (div_nonneg (by positivity) (by positivity)) hsum)

/-- Exact finite reindexing through a disjoint block partition. -/
theorem apNormalizedPrimitiveMeanOn_eq_sum_blocks
    (a : ℤ → ℂ) (N Q C : ℕ)
    (G : ProductionConductorBlockGeometry N Q C) :
    apNormalizedPrimitiveMeanOn a N (highConductorSet N Q C) =
      ∑ i ∈ G.index, apNormalizedPrimitiveMeanOn a N (G.cell i) := by
  unfold apNormalizedPrimitiveMeanOn
  rw [← G.cover]
  exact Finset.sum_biUnion G.pairwise

/-- The complete finite block-L¹ consumer.  A block estimate at the classical
`N + (2i)²√N` scale pays the AP mean by `1/i`; summing uses exactly the two
geometric ledgers and nothing analytic. -/
theorem blockWeightedPrimitiveMean_to_highMean
    (a : ℤ → ℂ) (N Q C loss : ℕ) (P K : ℝ)
    (G : ProductionConductorBlockGeometry N Q C)
    (hP : 0 ≤ P) (hK : 0 ≤ K)
    (hblock : ∀ i ∈ G.index,
      P * blockWeightedPrimitiveMean a N (G.cell i) ≤
        K * Real.log (N : ℝ) ^ loss *
          ((N : ℝ) + (2 * (i : ℝ)) ^ 2 * Real.sqrt N)) :
    P * apNormalizedPrimitiveMeanOn a N (highConductorSet N Q C) ≤
      K * Real.log (N : ℝ) ^ loss *
        (2 * (N : ℝ) / (logConductorThreshold N C : ℝ) +
          8 * (Q : ℝ) * Real.sqrt N) := by
  rw [apNormalizedPrimitiveMeanOn_eq_sum_blocks a N Q C G, Finset.mul_sum]
  calc
    _ ≤ ∑ i ∈ G.index,
        (1 / (i : ℝ)) * (K * Real.log (N : ℝ) ^ loss *
          ((N : ℝ) + (2 * (i : ℝ)) ^ 2 * Real.sqrt N)) := by
      apply Finset.sum_le_sum
      intro i hi
      have hLi := apNormalizedPrimitiveMeanOn_le_inv_mul_blockWeighted
        a N i (G.cell i) (G.lower_pos i hi) (G.levels i hi)
      calc
        P * apNormalizedPrimitiveMeanOn a N (G.cell i) ≤
            P * ((1 / (i : ℝ)) * blockWeightedPrimitiveMean a N (G.cell i)) :=
          mul_le_mul_of_nonneg_left hLi hP
        _ = (1 / (i : ℝ)) *
            (P * blockWeightedPrimitiveMean a N (G.cell i)) := by ring
        _ ≤ (1 / (i : ℝ)) * (K * Real.log (N : ℝ) ^ loss *
            ((N : ℝ) + (2 * (i : ℝ)) ^ 2 * Real.sqrt N)) := by
          exact mul_le_mul_of_nonneg_left (hblock i hi) (by positivity)
    _ = K * Real.log (N : ℝ) ^ loss *
        ((N : ℝ) * (∑ i ∈ G.index, (i : ℝ)⁻¹) +
          4 * Real.sqrt N * (∑ i ∈ G.index, (i : ℝ))) := by
      have hi0 : ∀ i ∈ G.index, (i : ℝ) ≠ 0 := fun i hi =>
        (by exact_mod_cast (G.lower_pos i hi).ne')
      calc
        _ = ∑ i ∈ G.index, K * Real.log (N : ℝ) ^ loss *
            ((N : ℝ) * (i : ℝ)⁻¹ + 4 * Real.sqrt N * (i : ℝ)) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [one_div]
          field_simp [hi0 i hi]
          ring
        _ = K * Real.log (N : ℝ) ^ loss *
            (∑ i ∈ G.index,
              ((N : ℝ) * (i : ℝ)⁻¹ + 4 * Real.sqrt N * (i : ℝ))) := by
          rw [Finset.mul_sum]
        _ = _ := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ K * Real.log (N : ℝ) ^ loss *
        ((N : ℝ) * (2 / (logConductorThreshold N C : ℝ)) +
          4 * Real.sqrt N * (2 * (Q : ℝ))) := by
      gcongr
      · exact G.inv_lower_sum_le
      · exact G.lower_sum_le
    _ = _ := by ring

/-- Exact production Type-I specialization of the generic finite consumer. -/
theorem productionTypeI_blockWeighted_to_highMean
    (N Q C u v loss : ℕ) (P K : ℝ)
    (G : ProductionConductorBlockGeometry N Q C)
    (hP : 0 ≤ P) (hK : 0 ≤ K)
    (hblock : ∀ i ∈ G.index,
      P * blockWeightedPrimitiveMean
        (vaughanTypeICoeff vaughanUnitIntegerCoeff u v) N (G.cell i) ≤
        K * Real.log (N : ℝ) ^ loss *
          ((N : ℝ) + (2 * (i : ℝ)) ^ 2 * Real.sqrt N)) :
    P * highConductorVaughanTypeIMean N Q C u v ≤
      K * Real.log (N : ℝ) ^ loss *
        (2 * (N : ℝ) / (logConductorThreshold N C : ℝ) +
          8 * (Q : ℝ) * Real.sqrt N) := by
  exact blockWeightedPrimitiveMean_to_highMean _ N Q C loss P K G hP hK hblock

/-- Exact production Type-II specialization, retaining the production
hyperbolic Vaughan coefficient. -/
theorem productionTypeII_blockWeighted_to_highMean
    (N Q C u v loss : ℕ) (P K : ℝ)
    (G : ProductionConductorBlockGeometry N Q C)
    (hP : 0 ≤ P) (hK : 0 ≤ K)
    (hblock : ∀ i ∈ G.index,
      P * blockWeightedPrimitiveMean
        (vaughanTypeIICoeff vaughanUnitIntegerCoeff u v) N (G.cell i) ≤
        K * Real.log (N : ℝ) ^ loss *
          ((N : ℝ) + (2 * (i : ℝ)) ^ 2 * Real.sqrt N)) :
    P * highConductorVaughanTypeIIMean N Q C u v ≤
      K * Real.log (N : ℝ) ^ loss *
        (2 * (N : ℝ) / (logConductorThreshold N C : ℝ) +
          8 * (Q : ℝ) * Real.sqrt N) := by
  exact blockWeightedPrimitiveMean_to_highMean _ N Q C loss P K G hP hK hblock

/-- Chosen exponents for paying a fixed block/shell logarithmic loss. -/
def standardBVBlockL1ConductorExponent (A loss : ℕ) : ℕ :=
  2 * (A + loss + 1)

def standardBVBlockL1ModulusExponent (A loss : ℕ) : ℕ :=
  max (A + 3) (A + loss)

lemma standardBVBlockL1_margin_B (A loss : ℕ) :
    A + 3 ≤ standardBVBlockL1ModulusExponent A loss := le_max_left _ _

lemma standardBVBlockL1_loss_le_C (A loss : ℕ) :
    A + loss ≤ standardBVBlockL1ConductorExponent A loss := by
  unfold standardBVBlockL1ConductorExponent
  omega

lemma standardBVBlockL1_loss_le_B (A loss : ℕ) :
    A + loss ≤ standardBVBlockL1ModulusExponent A loss := le_max_right _ _

private theorem blockL1_logPower_le_threshold_eventually (A loss : ℕ) :
    ∀ᶠ N : ℕ in Filter.atTop,
      Real.log (N : ℝ) ^ (A + loss) ≤
        (logConductorThreshold N (standardBVBlockL1ConductorExponent A loss) : ℝ) := by
  filter_upwards [eventually_ge_atTop (9 : ℕ)] with N hN
  let x : ℝ := Real.log (N : ℝ)
  let t : ℕ := A + loss
  have hx2 : 2 ≤ x := by
    dsimp [x]
    have h9 : Real.exp 2 < (9 : ℝ) := by
      rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
      nlinarith [Real.exp_one_lt_d9, Real.exp_pos (1 : ℝ)]
    exact (Real.lt_log_iff_exp_lt (by positivity : (0 : ℝ) < N)).2
      (h9.trans_le (by exact_mod_cast hN)) |>.le
  have hx0 : 0 ≤ x := by linarith
  have hbig : 2 ≤ x ^ (2 * (t + 1)) := by
    have hxpow2 : 2 ≤ x ^ 2 := by nlinarith [sq_nonneg (x - 2)]
    rw [show 2 * (t + 1) = 2 * t + 2 by omega, pow_add]
    have hb : 1 ≤ x ^ (2 * t) := one_le_pow₀ (by linarith)
    nlinarith [pow_nonneg hx0 (2 * t)]
  have hfloor := Nat.sub_one_lt_floor (x ^ (2 * (t + 1)))
  have hhalf : x ^ t ≤ x ^ (2 * (t + 1)) - 1 := by
    have hxt : 1 ≤ x ^ t := one_le_pow₀ (by linarith)
    have hfac : 2 ≤ x ^ (t + 2) := by
      have hpow : x ≤ x ^ (t + 2) := by
        simpa only [pow_one] using
          (pow_le_pow_right₀ (show 1 ≤ x by linarith)
            (show 1 ≤ t + 2 by omega))
      exact hx2.trans hpow
    have hm : 2 * x ^ t ≤ x ^ t * x ^ (t + 2) := by
      simpa [mul_comm] using
        (mul_le_mul_of_nonneg_left hfac (pow_nonneg hx0 t))
    calc
      x ^ t ≤ 2 * x ^ t - 1 := by linarith
      _ ≤ x ^ t * x ^ (t + 2) - 1 := by linarith
      _ = x ^ (2 * (t + 1)) - 1 := by
        rw [← pow_add]
        congr 2
        omega
  have hcast : x ^ t ≤ (Nat.floor (x ^ (2 * (t + 1))) : ℝ) :=
    hhalf.trans hfloor.le
  simpa [logConductorThreshold, standardBVBlockL1ConductorExponent, x, t] using hcast

/-- Scalar payment for the block analytic input.  The choices satisfy both
`C ≥ A+loss` and `B ≥ A+loss`; after the geometric block sum the two physical
scales are bounded by `10 N/log(N)^A`. -/
theorem standardBVBlockL1_scales_payable (A loss : ℕ) :
    ∀ᶠ N : ℕ in Filter.atTop,
      let C := standardBVBlockL1ConductorExponent A loss
      let B := standardBVBlockL1ModulusExponent A loss
      let R := logConductorThreshold N C
      let Q := MathlibNt.SieveTheory.LiuWeight.panModulusCutoff N (B : ℝ)
      Real.log (N : ℝ) ^ loss *
          (2 * (N : ℝ) / (R : ℝ) + 8 * (Q : ℝ) * Real.sqrt N) ≤
        10 * (N : ℝ) / Real.log (N : ℝ) ^ A := by
  filter_upwards [blockL1_logPower_le_threshold_eventually A loss,
    eventually_ge_atTop (9 : ℕ)] with N hR hN
  let C := standardBVBlockL1ConductorExponent A loss
  let B := standardBVBlockL1ModulusExponent A loss
  let R := logConductorThreshold N C
  let Q := MathlibNt.SieveTheory.LiuWeight.panModulusCutoff N (B : ℝ)
  let x : ℝ := Real.log (N : ℝ)
  have hx : 0 < x := by
    dsimp [x]
    exact Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hR' : x ^ (A + loss) ≤ (R : ℝ) := by simpa [R, x] using hR
  have hRpos : (0 : ℝ) < R := (pow_pos hx _).trans_le hR'
  have hB : A + loss ≤ B := by
    dsimp [B]
    exact standardBVBlockL1_loss_le_B A loss
  have hlog1 : 1 ≤ x := by
    have : 2 ≤ x := by
      have h9 : Real.exp 2 < (9 : ℝ) := by
        rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
        nlinarith [Real.exp_one_lt_d9, Real.exp_pos (1 : ℝ)]
      exact (Real.lt_log_iff_exp_lt (by positivity : (0 : ℝ) < N)).2
        (h9.trans_le (by exact_mod_cast hN)) |>.le
    linarith
  have hQ : (Q : ℝ) ≤ Real.sqrt N / x ^ (A + loss) := by
    calc
      (Q : ℝ) ≤ (N : ℝ) ^ (1 / 2 : ℝ) / Real.log N ^ (B : ℝ) := by
        exact Nat.floor_le (by positivity)
      _ ≤ (N : ℝ) ^ (1 / 2 : ℝ) / Real.log N ^ ((A + loss : ℕ) : ℝ) := by
        apply div_le_div_of_nonneg_left (Real.rpow_nonneg (by positivity) _)
          (Real.rpow_pos_of_pos hx _)
        exact Real.rpow_le_rpow_of_exponent_le hlog1 (by exact_mod_cast hB)
      _ = Real.sqrt N / x ^ (A + loss) := by
        rw [Real.sqrt_eq_rpow, Real.rpow_natCast]
  have hfirst : x ^ loss * (2 * (N : ℝ) / R) ≤
      2 * (N : ℝ) / x ^ A := by
    rw [show x ^ loss * (2 * (N : ℝ) / R) =
      (x ^ loss * (2 * (N : ℝ))) / R by ring]
    apply (div_le_div_iff₀ hRpos (pow_pos hx A)).2
    calc
      x ^ loss * (2 * (N : ℝ)) * x ^ A =
          2 * (N : ℝ) * x ^ (A + loss) := by rw [pow_add]; ring
      _ ≤ 2 * (N : ℝ) * R := by gcongr
  have hsecond : x ^ loss * (8 * (Q : ℝ) * Real.sqrt N) ≤
      8 * (N : ℝ) / x ^ A := by
    have hden : 0 < x ^ (A + loss) := pow_pos hx _
    have hQ' : (Q : ℝ) * x ^ (A + loss) ≤ Real.sqrt N :=
      (le_div_iff₀ hden).mp hQ
    apply (le_div_iff₀ (pow_pos hx A)).2
    calc
      x ^ loss * (8 * (Q : ℝ) * Real.sqrt N) * x ^ A =
          8 * Real.sqrt N * ((Q : ℝ) * x ^ (A + loss)) := by
        rw [pow_add]
        ring
      _ ≤ 8 * Real.sqrt N * Real.sqrt N := by gcongr
      _ = 8 * (N : ℝ) := by rw [mul_assoc, Real.mul_self_sqrt (by positivity)]
  dsimp [C, B, R, Q]
  calc
    x ^ loss * (2 * (N : ℝ) / (logConductorThreshold N
        (standardBVBlockL1ConductorExponent A loss) : ℝ) +
        8 * (MathlibNt.SieveTheory.LiuWeight.panModulusCutoff N
          (standardBVBlockL1ModulusExponent A loss : ℝ) : ℝ) * Real.sqrt N) =
      x ^ loss * (2 * (N : ℝ) / R) +
        x ^ loss * (8 * (Q : ℝ) * Real.sqrt N) := by ring
    _ ≤ 2 * (N : ℝ) / x ^ A + 8 * (N : ℝ) / x ^ A :=
      add_le_add hfirst hsecond
    _ = 10 * (N : ℝ) / x ^ A := by ring

/-- Canonical envelope-free production Type-I block mean-value predicate.
The analytic source controls the literal block mean; the elementary
Abel/conductor envelope is paid only by the downstream consumer. -/
def ProductionTypeIBlockMeanValueBare
    (N u v loss : ℕ) (K : ℝ) {Q C : ℕ}
    (G : ProductionConductorBlockGeometry N Q C) : Prop :=
  ∀ i ∈ G.index,
    blockWeightedPrimitiveMean
      (vaughanTypeICoeff vaughanUnitIntegerCoeff u v) N (G.cell i) ≤
      K * Real.log (N : ℝ) ^ loss *
        ((N : ℝ) + (2 * (i : ℝ)) ^ 2 * Real.sqrt N)

/-- Canonical envelope-free production Type-II block mean-value predicate. -/
def ProductionTypeIIBlockMeanValueBare
    (N u v loss : ℕ) (K : ℝ) {Q C : ℕ}
    (G : ProductionConductorBlockGeometry N Q C) : Prop :=
  ∀ i ∈ G.index,
    blockWeightedPrimitiveMean
      (vaughanTypeIICoeff vaughanUnitIntegerCoeff u v) N (G.cell i) ≤
      K * Real.log (N : ℝ) ^ loss *
        ((N : ℝ) + (2 * (i : ℝ)) ^ 2 * Real.sqrt N)

/-- Legacy compatibility predicate with the Abel/conductor envelope already
multiplied into the analytic hypothesis. -/
def ProductionTypeIBlockMeanValue
    (N u v loss : ℕ) (P K : ℝ) {Q C : ℕ}
    (G : ProductionConductorBlockGeometry N Q C) : Prop :=
  ∀ i ∈ G.index,
    P * blockWeightedPrimitiveMean
      (vaughanTypeICoeff vaughanUnitIntegerCoeff u v) N (G.cell i) ≤
      K * Real.log (N : ℝ) ^ loss *
        ((N : ℝ) + (2 * (i : ℝ)) ^ 2 * Real.sqrt N)

/-- The parallel production Type-II block mean-value theorem, retaining the
existing exact hyperbolic Vaughan coefficient. -/
def ProductionTypeIIBlockMeanValue
    (N u v loss : ℕ) (P K : ℝ) {Q C : ℕ}
    (G : ProductionConductorBlockGeometry N Q C) : Prop :=
  ∀ i ∈ G.index,
    P * blockWeightedPrimitiveMean
      (vaughanTypeIICoeff vaughanUnitIntegerCoeff u v) N (G.cell i) ≤
      K * Real.log (N : ℝ) ^ loss *
        ((N : ℝ) + (2 * (i : ℝ)) ^ 2 * Real.sqrt N)

/-- Legacy `v = min N 1` block source, retained only for compatibility with
callers of the former degenerate small-lane assembler. -/
def StandardBVProductionBlockL1WeightedLegacySource (loss : ℕ) : Prop :=
  ∀ A : ℕ,
    let B := standardBVBlockL1ModulusExponent A loss
    let C := standardBVBlockL1ConductorExponent A loss
    ∃ u : ℕ → ℕ, ∃ K₁ K₂ : ℝ, 0 < K₁ ∧ 0 < K₂ ∧
      ∀ᶠ N : ℕ in Filter.atTop,
        let Q := MathlibNt.SieveTheory.LiuWeight.panModulusCutoff N (B : ℝ)
        let P := 4 * discreteAbelAmplifierPrefixMax N * conductorHarmonicFactor Q ^ 2
        ∀ hR : 0 < logConductorThreshold N C,
          let G := productionConductorBlockGeometry N Q C hR
          ProductionTypeIBlockMeanValue N (u N)
              (standardBVChosenSmallCutoff N) loss P K₁ G ∧
            ProductionTypeIIBlockMeanValue N (u N)
              (standardBVChosenSmallCutoff N) loss P K₂ G

/-- Exact block analytic input on the canonical production dyadic geometry.
Type-I and Type-II use the same moving `u,v`, and the production `v` is the
balanced cube-root cutoff.  No finite partition or geometric-ledger premise is
exposed. -/
def StandardBVProductionBlockL1WeightedSource (loss : ℕ) : Prop :=
  ∀ A : ℕ,
    let B := standardBVBlockL1ModulusExponent A loss
    let C := standardBVBlockL1ConductorExponent A loss
    ∃ u v : ℕ → ℕ, v = standardBVBalancedSmallCutoff ∧
      ∃ K₁ K₂ : ℝ, 0 < K₁ ∧ 0 < K₂ ∧
        ∀ᶠ N : ℕ in Filter.atTop,
          let Q := MathlibNt.SieveTheory.LiuWeight.panModulusCutoff N (B : ℝ)
          let P := 4 * discreteAbelAmplifierPrefixMax N * conductorHarmonicFactor Q ^ 2
          ∀ hR : 0 < logConductorThreshold N C,
            let G := productionConductorBlockGeometry N Q C hR
            ProductionTypeIBlockMeanValue N (u N) (v N) loss P K₁ G ∧
              ProductionTypeIIBlockMeanValue N (u N) (v N) loss P K₂ G

/-- Compatibility assembler for the former degenerate `v = min N 1` source.
New production code must use
`standardBVHighTypeITypeIIHybridChosenSource_of_blockL1Weighted`. -/
theorem standardBVHighTypeITypeIIHybridChosenSource_of_blockL1Weighted_legacy
    {loss : ℕ} (hblock : StandardBVProductionBlockL1WeightedLegacySource loss) :
    StandardBVHighTypeITypeIIHybridChosenSource := by
  intro A
  let B := standardBVBlockL1ModulusExponent A loss
  let C := standardBVBlockL1ConductorExponent A loss
  obtain ⟨u, K₁, K₂, hK₁, hK₂, hsource⟩ := hblock A
  let v : ℕ → ℕ := standardBVChosenSmallCutoff
  refine ⟨B, C, by simpa [B] using standardBVBlockL1_margin_B A loss,
    u, v, 10 * (K₁ + K₂), by positivity, ?_⟩
  filter_upwards [hsource, standardBVBlockL1_scales_payable A loss,
    eventually_ge_atTop (9 : ℕ)] with N hN hpay hN9
  dsimp only at hN hpay ⊢
  let Q := MathlibNt.SieveTheory.LiuWeight.panModulusCutoff N (B : ℝ)
  let P := 4 * discreteAbelAmplifierPrefixMax N * conductorHarmonicFactor Q ^ 2
  have hR : 0 < logConductorThreshold N C := by
    unfold logConductorThreshold
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
    have ha : 0 ≤ discreteAbelAmplifierPrefixMax N := by
      have h0 : 0 ≤ discreteAbelAmplifier 0 := by
        unfold discreteAbelAmplifier
        positivity
      exact h0.trans (by
        unfold discreteAbelAmplifierPrefixMax
        exact Finset.le_max' _ _ (Finset.mem_image.mpr ⟨0, by simp, rfl⟩))
    positivity
  have hI := productionTypeI_blockWeighted_to_highMean
    N Q C (u N) (v N) loss P K₁ G hP hK₁.le hIblock
  have hII := productionTypeII_blockWeighted_to_highMean
    N Q C (u N) (v N) loss P K₂ G hP hK₂.le hIIblock
  have hsmall : highConductorVaughanSmallMean N Q C (v N) = 0 := by
    dsimp [v]
    unfold highConductorVaughanSmallMean
    rw [standardBVChosenSmallCoeff_eq_zero]
    unfold apNormalizedPrimitiveMeanOn
    have hpref (d : ℕ) (ψ : PrimitiveCharacter d) :
        primitivePrefixAmplitude 0 N d ψ = 0 := by
      unfold primitivePrefixAmplitude
      have hz : primitiveCharacterPrefixMaxSquare 0 0 N d ψ = 0 := by
        apply le_antisymm
        · unfold primitiveCharacterPrefixMaxSquare
          apply Finset.max'_le
          intro z hz
          rcases Finset.mem_image.mp hz with ⟨y, hy, rfl⟩
          simp [primitiveCharacterPrefixSquare]
        · exact primitiveCharacterPrefixMaxSquare_nonneg 0 0 N d ψ
      rw [hz]
      simp
    simp_rw [hpref]
    simp
  rw [hsmall, add_zero]
  have hsum : P * (highConductorVaughanTypeIMean N Q C (u N) (v N) +
      highConductorVaughanTypeIIMean N Q C (u N) (v N)) ≤
      (K₁ + K₂) * Real.log (N : ℝ) ^ loss *
        (2 * (N : ℝ) / (logConductorThreshold N C : ℝ) +
          8 * (Q : ℝ) * Real.sqrt N) := by
    rw [mul_add]
    exact (add_le_add hI hII).trans_eq (by ring)
  exact hsum.trans (by
    have hp := hpay
    change Real.log (N : ℝ) ^ loss *
        (2 * (N : ℝ) / (logConductorThreshold N C : ℝ) +
          8 * (Q : ℝ) * Real.sqrt N) ≤
      10 * (N : ℝ) / Real.log (N : ℝ) ^ A at hp
    calc
      (K₁ + K₂) * Real.log (N : ℝ) ^ loss *
          (2 * (N : ℝ) / (logConductorThreshold N C : ℝ) +
            8 * (Q : ℝ) * Real.sqrt N) =
        (K₁ + K₂) * (Real.log (N : ℝ) ^ loss *
          (2 * (N : ℝ) / (logConductorThreshold N C : ℝ) +
            8 * (Q : ℝ) * Real.sqrt N)) := by ring
      _ ≤ (K₁ + K₂) * (10 * (N : ℝ) / Real.log (N : ℝ) ^ A) := by gcongr
      _ = 10 * (K₁ + K₂) * (N : ℝ) / Real.log (N : ℝ) ^ A := by ring)

private lemma highConductorSet_eq_interval_blockL1 (N Q C : ℕ)
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

/-- Production block-L¹ chosen assembler.  Type-I and Type-II use one shared
pair `u,v`, with `v = standardBVBalancedSmallCutoff`; their block first moments
are paid by the block geometry, while the retained balanced small mean is paid
by `standardBVChosenSmall_squareLedger_payable` followed by the existing
high-conductor weighted Cauchy inequality. -/
theorem standardBVHighTypeITypeIIHybridChosenSource_of_blockL1Weighted
    {loss : ℕ} (hblock : StandardBVProductionBlockL1WeightedSource loss) :
    StandardBVHighTypeITypeIIHybridChosenSource := by
  intro A
  let B := standardBVBlockL1ModulusExponent A loss
  let C := standardBVBlockL1ConductorExponent A loss
  obtain ⟨u, v, hv, K₁, K₂, hK₁, hK₂, hsource⟩ := hblock A
  obtain ⟨K₀, hK₀, hsmallSource⟩ :=
    standardBVChosenSmall_squareLedger_payable A 0 B C
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
    have ha : 0 ≤ discreteAbelAmplifierPrefixMax N := by
      have h0 : 0 ≤ discreteAbelAmplifier 0 := by
        unfold discreteAbelAmplifier
        positivity
      exact h0.trans (by
        unfold discreteAbelAmplifierPrefixMax
        exact Finset.le_max' _ _ (Finset.mem_image.mpr ⟨0, by simp, rfl⟩))
    positivity
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
  rw [← highConductorSet_eq_interval_blockL1 N Q C (by simpa only [R] using hRone)] at hsmallCauchy
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
        simpa only [hv, Nat.add_zero] using hsmallPay
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

/-- The production Abel/conductor envelope costs at most five logarithms.
The proof actually gives a quadratic logarithm; exponent five is frozen as a
stable reserve for canonical bare block sources. -/
theorem productionAbelConductorEnvelope_le_logPow_five (B : ℕ) :
    ∀ᶠ N : ℕ in Filter.atTop,
      let Q := MathlibNt.SieveTheory.LiuWeight.panModulusCutoff N (B : ℝ)
      4 * discreteAbelAmplifierPrefixMax N * conductorHarmonicFactor Q ^ 2 ≤
        48 * Real.log (N : ℝ) ^ 5 := by
  filter_upwards [eventually_ge_atTop (3 : ℕ)] with N hN
  dsimp only
  let Q := MathlibNt.SieveTheory.LiuWeight.panModulusCutoff N (B : ℝ)
  have hlog : 1 ≤ Real.log (N : ℝ) := by
    have he1 : Real.exp 1 < (3 : ℝ) :=
      Real.exp_one_lt_d9.trans (by norm_num)
    exact (Real.lt_log_iff_exp_lt (by positivity : (0 : ℝ) < N)).2
      (he1.trans_le (by exact_mod_cast hN)) |>.le
  have habel : discreteAbelAmplifierPrefixMax N ≤ 3 := by
    refine (discreteAbelAmplifierPrefixMax_le_two_inv_log_two N).trans ?_
    have htwo : (2 / 3 : ℝ) < Real.log 2 := by
      linarith [Real.log_two_gt_d9]
    rw [mul_inv_le_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))]
    linarith
  by_cases hQ0 : Q = 0
  · simp [Q, hQ0, conductorHarmonicFactor]
    exact pow_nonneg (zero_le_one.trans hlog) 5
  · have hQpos : 0 < Q := Nat.pos_of_ne_zero hQ0
    have hQsq : Q ^ 2 ≤ N := by
      simpa [Q] using MathlibNt.SieveTheory.LiuWeight.panModulusCutoff_sq_le
        N (B : ℝ) (by omega) (by positivity : 0 ≤ (B : ℝ))
    have hQle : Q ≤ N := by
      calc
        Q = Q * 1 := by simp
        _ ≤ Q * Q := Nat.mul_le_mul_left Q (Nat.succ_le_iff.mpr hQpos)
        _ = Q ^ 2 := by ring
        _ ≤ N := hQsq
    have hlogQ : Real.log (Q : ℝ) ≤ Real.log (N : ℝ) :=
      Real.log_le_log (by exact_mod_cast hQpos) (by exact_mod_cast hQle)
    have hH : conductorHarmonicFactor Q ≤ 2 * Real.log (N : ℝ) :=
      (conductorHarmonicFactor_le Q).trans (by linarith)
    have hH0 : 0 ≤ conductorHarmonicFactor Q := conductorHarmonicFactor_nonneg Q
    have hPquad :
        4 * discreteAbelAmplifierPrefixMax N * conductorHarmonicFactor Q ^ 2 ≤
          48 * Real.log (N : ℝ) ^ 2 := by
      calc
        _ ≤ 4 * 3 * (2 * Real.log (N : ℝ)) ^ 2 := by
          gcongr
        _ = 48 * Real.log (N : ℝ) ^ 2 := by ring
    have hpows : Real.log (N : ℝ) ^ 2 ≤ Real.log (N : ℝ) ^ 5 := by
      rw [show 5 = 2 + 3 by omega, pow_add]
      exact le_mul_of_one_le_right (pow_nonneg (by positivity) 2)
        (one_le_pow₀ hlog)
    exact hPquad.trans (mul_le_mul_of_nonneg_left hpows (by norm_num))

/-- Canonical bare block source.  Its analytic hypotheses contain no
Abel/conductor factor.  The selected exponents reserve the fixed five-log
consumer payment. -/
def StandardBVProductionBlockL1BareSource (loss : ℕ) : Prop :=
  ∀ A : ℕ,
    let paidLoss := loss + 5
    let B := standardBVBlockL1ModulusExponent A paidLoss
    let C := standardBVBlockL1ConductorExponent A paidLoss
    ∃ u v : ℕ → ℕ, v = standardBVBalancedSmallCutoff ∧
      ∃ K₁ K₂ : ℝ, 0 < K₁ ∧ 0 < K₂ ∧
        ∀ᶠ N : ℕ in Filter.atTop,
          let Q := MathlibNt.SieveTheory.LiuWeight.panModulusCutoff N (B : ℝ)
          ∀ hR : 0 < logConductorThreshold N C,
            let G := productionConductorBlockGeometry N Q C hR
            ProductionTypeIBlockMeanValueBare N (u N) (v N) loss K₁ G ∧
              ProductionTypeIIBlockMeanValueBare N (u N) (v N) loss K₂ G

/-- Multiplying a bare Type-I block estimate by an envelope bounded by five
logarithms shifts the loss by exactly five. -/
theorem productionTypeIBlockMeanValue_of_bare_logPow_five
    (N u v loss : ℕ) (P K : ℝ) {Q C : ℕ}
    (G : ProductionConductorBlockGeometry N Q C)
    (hP : P ≤ 48 * Real.log (N : ℝ) ^ 5)
    (hbare : ProductionTypeIBlockMeanValueBare N u v loss K G) :
    ProductionTypeIBlockMeanValue N u v (loss + 5) P (48 * K) G := by
  intro i hi
  have hW0 := blockWeightedPrimitiveMean_nonneg
    (vaughanTypeICoeff vaughanUnitIntegerCoeff u v) N (G.cell i)
  calc
    P * blockWeightedPrimitiveMean
        (vaughanTypeICoeff vaughanUnitIntegerCoeff u v) N (G.cell i) ≤
      (48 * Real.log (N : ℝ) ^ 5) * blockWeightedPrimitiveMean
        (vaughanTypeICoeff vaughanUnitIntegerCoeff u v) N (G.cell i) :=
      mul_le_mul_of_nonneg_right hP hW0
    _ ≤ (48 * Real.log (N : ℝ) ^ 5) *
        (K * Real.log (N : ℝ) ^ loss *
          ((N : ℝ) + (2 * (i : ℝ)) ^ 2 * Real.sqrt N)) :=
      mul_le_mul_of_nonneg_left (hbare i hi) (by positivity)
    _ = (48 * K) * Real.log (N : ℝ) ^ (loss + 5) *
        ((N : ℝ) + (2 * (i : ℝ)) ^ 2 * Real.sqrt N) := by
      rw [pow_add]
      ring

/-- Type-II version of the fixed five-log consumer payment. -/
theorem productionTypeIIBlockMeanValue_of_bare_logPow_five
    (N u v loss : ℕ) (P K : ℝ) {Q C : ℕ}
    (G : ProductionConductorBlockGeometry N Q C)
    (hP : P ≤ 48 * Real.log (N : ℝ) ^ 5)
    (hbare : ProductionTypeIIBlockMeanValueBare N u v loss K G) :
    ProductionTypeIIBlockMeanValue N u v (loss + 5) P (48 * K) G := by
  intro i hi
  have hW0 := blockWeightedPrimitiveMean_nonneg
    (vaughanTypeIICoeff vaughanUnitIntegerCoeff u v) N (G.cell i)
  calc
    P * blockWeightedPrimitiveMean
        (vaughanTypeIICoeff vaughanUnitIntegerCoeff u v) N (G.cell i) ≤
      (48 * Real.log (N : ℝ) ^ 5) * blockWeightedPrimitiveMean
        (vaughanTypeIICoeff vaughanUnitIntegerCoeff u v) N (G.cell i) :=
      mul_le_mul_of_nonneg_right hP hW0
    _ ≤ (48 * Real.log (N : ℝ) ^ 5) *
        (K * Real.log (N : ℝ) ^ loss *
          ((N : ℝ) + (2 * (i : ℝ)) ^ 2 * Real.sqrt N)) :=
      mul_le_mul_of_nonneg_left (hbare i hi) (by positivity)
    _ = (48 * K) * Real.log (N : ℝ) ^ (loss + 5) *
        ((N : ℝ) + (2 * (i : ℝ)) ^ 2 * Real.sqrt N) := by
      rw [pow_add]
      ring

/-- Consumer-side bridge: a canonical bare source becomes the balanced weighted
source after the fixed loss translation. -/
theorem standardBVProductionBlockL1WeightedSource_of_bare
    {loss : ℕ} (hbare : StandardBVProductionBlockL1BareSource loss) :
    StandardBVProductionBlockL1WeightedSource (loss + 5) := by
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

/-- The canonical envelope-free block source is connected to the chosen high
Standard-BV node; all envelope loss is paid in the consumer above. -/
theorem standardBVHighTypeITypeIIHybridChosenSource_of_blockL1Bare
    {loss : ℕ} (hbare : StandardBVProductionBlockL1BareSource loss) :
    StandardBVHighTypeITypeIIHybridChosenSource :=
  standardBVHighTypeITypeIIHybridChosenSource_of_blockL1Weighted
    (standardBVProductionBlockL1WeightedSource_of_bare hbare)

end
end AnalyticNumberTheory.LargeSieve
