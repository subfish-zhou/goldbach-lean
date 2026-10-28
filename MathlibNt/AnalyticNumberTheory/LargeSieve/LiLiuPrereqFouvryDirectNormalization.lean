import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryDirectLocalScaleFrequency
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryGramAggregateBound

/-!
# Reciprocal normalization, keeping the long interval term

Exact local algebra precedes any global enlargement. The last theorem is
explicitly conditional only on numeric outer-mass and energy estimates;
it is not a claimed proof of C.2, nor a new cancellation hypothesis.
-/

noncomputable section
open Classical Finset

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry


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
