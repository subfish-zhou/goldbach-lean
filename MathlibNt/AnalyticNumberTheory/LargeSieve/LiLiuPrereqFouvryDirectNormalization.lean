import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryDirectLocalScaleFrequency
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryGramAggregateBound
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvrySeparatedCorrelation

/-!
# Reciprocal normalization, keeping the long interval term

Exact local algebra precedes any global enlargement. The last theorem is
explicitly conditional only on numeric outer-mass and energy estimates;
it is not a claimed proof of C.2, nor a new cancellation hypothesis.
-/

noncomputable section
open Classical Finset

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

/-- Inclusive interval length, including the natural subtraction convention. -/
theorem directNormalization_span_le (R S M Z : ℝ) (K : WExtractedKey)
    (j cap : Fin 5 → ℕ) (L : WGramLabel) :
    (wGramSpan R S M Z K j cap L : ℝ) ≤ 2 * (2 : ℝ) ^ j 1 := by
  have hu : wKSectionGridUpper R S K j cap ≤ 2 ^ (j 1 + 1) - 1 :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hp : 0 < (2 : ℕ) ^ (j 1 + 1) := by positivity
  have hs : wGramSpan R S M Z K j cap L ≤ 2 ^ (j 1 + 1) := by
    unfold wGramSpan
    omega
  have hr : (wGramSpan R S M Z K j cap L : ℝ) ≤ (2 : ℝ) ^ (j 1 + 1) := by
    exact_mod_cast hs
  simpa only [pow_succ, mul_comm] using hr

/-- Exact q^(1/2+epsilon) split. The span/q contribution does not disappear. -/
theorem directNormalization_cost_split
    (ε C : ℝ) (a : ℤ) (R S M Z : ℝ) (K : WExtractedKey)
    (j cap : Fin 5 → ℕ) (L : WGramLabel) (hq : 0 < wGramModulus L) :
    wBlockAmplitude K j * wGramFouvryCost ε C a R S M Z K j cap L =
      C * (a.natAbs.divisors.card : ℝ) *
        Real.sqrt ((wGramModulus L).gcd (wGramNumerator K a L).natAbs : ℝ) *
        (wGramModulus L : ℝ) ^ ε *
        (wBlockAmplitude K j * (K.D' : ℝ) * Real.sqrt (wGramModulus L : ℝ) +
          wBlockAmplitude K j * (wGramSpan R S M Z K j cap L : ℝ) /
            Real.sqrt (wGramModulus L : ℝ)) := by
  have hqr : (0 : ℝ) < wGramModulus L := by exact_mod_cast hq
  have hs : Real.sqrt (wGramModulus L : ℝ) ≠ 0 := (Real.sqrt_pos.2 hqr).ne'
  have he : (wGramModulus L : ℝ) ^ (1 / 2 + ε : ℝ) =
      Real.sqrt (wGramModulus L : ℝ) * (wGramModulus L : ℝ) ^ ε := by
    rw [Real.rpow_add hqr, Real.sqrt_eq_rpow]
  unfold wGramFouvryCost
  rw [he]
  have hsq := Real.sq_sqrt hqr.le
  field_simp
  rw [hsq]
  ring

/-- The inclusive span bound cancels k only after its true reciprocal factor. -/
theorem directNormalization_long_factor_le
    (R S M Z : ℝ) (K : WExtractedKey) (j cap : Fin 5 → ℕ)
    (L : WGramLabel) (hD : 0 < K.D) (hq : 0 < wGramModulus L) :
    wBlockAmplitude K j * (wGramSpan R S M Z K j cap L : ℝ) /
        Real.sqrt (wGramModulus L : ℝ) ≤
      2 / ((K.D : ℝ) * 2 ^ j 3 * 2 ^ j 4 * Real.sqrt (wGramModulus L : ℝ)) := by
  have hDr : (0 : ℝ) < K.D := by exact_mod_cast hD
  have hqr : (0 : ℝ) < wGramModulus L := by exact_mod_cast hq
  have hs := Real.sqrt_pos.2 hqr
  calc
    _ ≤ wBlockAmplitude K j * (2 * (2 : ℝ) ^ j 1) /
        Real.sqrt (wGramModulus L : ℝ) := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (directNormalization_span_le R S M Z K j cap L)
          (by unfold wBlockAmplitude; positivity)) hs.le
    _ = _ := by unfold wBlockAmplitude; field_simp

/-- The local denominator cancels the true floor frequency, before enlargement. -/
theorem directNormalization_floor_frequency_paid
    {M Z : ℝ} (hM : 0 < M) (hZ : 0 ≤ Z) {N Q : Finset ℕ}
    (hN : ∀ n ∈ N, 0 < n) (hQ : ∀ q ∈ Q, 0 < q)
    {a : ℤ} {P : WOriginalTuple → Prop} {R S ξ : ℝ} {b : ℕ}
    {K : WExtractedKey} {j : Fin 5 → ℕ} {positive : Bool}
    {t : WExtractedTuple × ℤ}
    (ht : t ∈ wAnalyticDyadicBlock
      (wExtractedKeyFiber (wFloorCutoff M Z) N Q a P R S ξ b K) j positive) :
    wBlockAmplitude K j * (2 : ℝ) ^ j 0 ≤ 8 * Z / M := by
  have hD := (wExtractedKeyFiber_positive hN hQ (mem_filter.mp ht).1).1
  have hDr : (0 : ℝ) < K.D := by exact_mod_cast hD
  calc
    _ ≤ wBlockAmplitude K j *
        (8 * ((K.D : ℝ) * 2 ^ j 1 * 2 ^ j 3 * 2 ^ j 4) / M * Z) :=
      mul_le_mul_of_nonneg_left (directLocalScale_floor_frequency_le hM hZ hN hQ ht)
        (by unfold wBlockAmplitude; positivity)
    _ = _ := by unfold wBlockAmplitude; field_simp

/-- The ceiling analogue honestly retains the reciprocal unit-frequency cost. -/
theorem directNormalization_ceil_frequency_paid
    {M Z : ℝ} (hM : 0 < M) (hZ : 0 ≤ Z) {N Q : Finset ℕ}
    (hN : ∀ n ∈ N, 0 < n) (hQ : ∀ q ∈ Q, 0 < q)
    {a : ℤ} {P : WOriginalTuple → Prop} {R S ξ : ℝ} {b : ℕ}
    {K : WExtractedKey} {j : Fin 5 → ℕ} {positive : Bool}
    {t : WExtractedTuple × ℤ}
    (ht : t ∈ wAnalyticDyadicBlock
      (wExtractedKeyFiber (wUniformCutoff M Z) N Q a P R S ξ b K) j positive) :
    wBlockAmplitude K j * (2 : ℝ) ^ j 0 ≤ 8 * Z / M + wBlockAmplitude K j := by
  have hD := (wExtractedKeyFiber_positive hN hQ (mem_filter.mp ht).1).1
  have hDr : (0 : ℝ) < K.D := by exact_mod_cast hD
  calc
    _ ≤ wBlockAmplitude K j *
        (8 * ((K.D : ℝ) * 2 ^ j 1 * 2 ^ j 3 * 2 ^ j 4) / M * Z + 1) :=
      mul_le_mul_of_nonneg_left (directLocalScale_ceil_frequency_lt hM hZ hN hQ ht).le
        (by unfold wBlockAmplitude; positivity)
    _ = _ := by unfold wBlockAmplitude; field_simp

/-- General monomial payment; the exponent p-1 is retained on the local denominator. -/
theorem directNormalization_rpow_payment {A H B p : ℝ}
    (hA : 0 < A) (hH : 0 ≤ H) (hB : 0 ≤ B) (hp : 0 ≤ p) (hHB : H ≤ A * B) :
    A⁻¹ * H ^ p ≤ A ^ (p - 1) * B ^ p := by
  calc
    _ ≤ A⁻¹ * (A * B) ^ p :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hH hHB hp) (inv_nonneg.mpr hA.le)
    _ = A ^ (p - 1) * B ^ p := by
      rw [Real.mul_rpow hA.le hB, Real.rpow_sub hA, Real.rpow_one]
      ring

/-- Standard square-root split with both nonzero terms separately visible. -/
theorem directNormalization_sqrt_three {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    Real.sqrt (a + b + c) ≤ Real.sqrt a + Real.sqrt b + Real.sqrt c := by
  apply (Real.sqrt_le_left (by positivity)).2
  nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb, Real.sq_sqrt hc,
    mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b),
    mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg c),
    mul_nonneg (Real.sqrt_nonneg b) (Real.sqrt_nonneg c)]

/-- Conditional A/B consumer on the literal signed arithmetic carrier.
Only numeric mass and three energy bounds are inputs. No C.2-sized target
is assumed; all three contributions and the exact reciprocal stay visible. -/
theorem directNormalization_actual_cauchy_three
    {H : ℕ → ℕ → ℕ} {N Q : Finset ℕ}
    (hN : ∀ n ∈ N, 0 < n) (hQ : ∀ q ∈ Q, 0 < q)
    {a : ℤ} {x η R S : ℝ} {b : ℕ} {K : WExtractedKey}
    {U : Finset (WExtractedTuple × ℤ)}
    (hU : U ⊆ wExtractedKeyFiber H N Q a (c2FiveSmallMask x η)
      R S (highOmegaCutoff x) b K)
    (c : Finset (ℕ × ℕ)) (j : Fin 5 → ℕ) (β c₁ γ ζ : ℕ → ℝ)
    {B Ezero Eshort Elong : ℝ} (hB : 0 ≤ B) (hz : 0 ≤ Ezero) (hs : 0 ≤ Eshort)
    (hl : 0 ≤ Elong)
    (hMass : wCorrelationOuterMass x N S U c K β c₁ γ ≤ B)
    (hEnergy : wSeparatedCorrelationEnergy x N S U c K β ζ a ≤ Ezero + Eshort + Elong) :
    wBlockAmplitude K j *
      ‖∑ t ∈ wCoprimeFiber x N S U c,
        (wExtractedCoefficient β c₁ γ ζ t.1 : ℂ) * wExtractedArithmeticPhase a t.2 t.1‖ ≤
      wBlockAmplitude K j * Real.sqrt B *
        (Real.sqrt Ezero + Real.sqrt Eshort + Real.sqrt Elong) := by
  have he0 := wSeparatedCorrelationEnergy_nonneg hN hQ hU c β ζ
  have hh := (wCoprimeFiber_separated_cauchy hN hQ hU c β c₁ γ ζ).trans
    (mul_le_mul hMass hEnergy he0 hB)
  have hroot := Real.sqrt_le_sqrt hh
  rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_mul hB] at hroot
  have hfinal := hroot.trans (mul_le_mul_of_nonneg_left
    (directNormalization_sqrt_three hz hs hl) (Real.sqrt_nonneg B))
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hfinal
    (show 0 ≤ wBlockAmplitude K j by unfold wBlockAmplitude; positivity)

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
