import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryDirectPayZeroGeometry

noncomputable section
open Classical Finset
namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

/-- Both literal resonance bases have polynomial size; no divisor envelope input. -/
theorem directPayZero_envelope
    {x T ε : ℝ} (hx : 4 ≤ x) (_hT : 0 ≤ T) (hTx : T ≤ x) (hε : 0 ≤ ε)
    (K : WExtractedKey) (F : ℕ) (j : Fin 5 → ℕ)
    (hF : (F : ℝ) ≤ 2 * T) (hn : (2 : ℝ)^j 2 ≤ 2*T)
    (hs : (2 : ℝ)^j 4 ≤ x) (hd : (K.1.2.1 : ℝ) ≤ x)
    (hH : (2 : ℝ)^j 0 ≤ x^10) :
    wGramResonanceScaleEnvelope K F j ε ≤ x ^ (44 * ε) := by
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hf : ((F / K.1.1 : ℕ) : ℝ) ≤ 2*x :=
    (Nat.cast_le.mpr (Nat.div_le_self F K.1.1)).trans (hF.trans (by linarith))
  have hp : (wGramResonanceScaleProductMax K F j : ℝ) ≤ x^14 := by
    unfold wGramResonanceScaleProductMax
    push_cast
    simp only [pow_succ]
    calc
      _ ≤ (x^10*2)*(2*x)*(x*2) := by gcongr
      _ = 8*x^12 := by ring
      _ ≤ x^2*x^12 := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        nlinarith
      _ = _ := by ring
  have hp2 : x^2 ≤ x^14 := by exact pow_le_pow_right₀ hx1 (by omega)
  have hq : (wGramResonanceScaleDivisorMax K F j : ℝ) ≤ x^16 := by
    unfold wGramResonanceScaleDivisorMax
    push_cast
    calc
      _ ≤ x*((2*x)*2)+x^14 := by
        rw [pow_succ]
        gcongr
        exact hn.trans (by linarith)
      _ = 4*x^2+x^14 := by ring
      _ ≤ 5*x^14 := by linarith
      _ ≤ x^2*x^14 := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        nlinarith
      _ = _ := by ring
  calc
    _ ≤ (x^14 : ℝ)^(2*ε) * (x^16 : ℝ)^ε := by
      unfold wGramResonanceScaleEnvelope
      exact mul_le_mul (Real.rpow_le_rpow (by positivity) hp (by positivity))
        (Real.rpow_le_rpow (by positivity) hq hε) (by positivity) (by positivity)
    _ = x^(44*ε) := by
      rw [← Real.rpow_natCast x 14, ← Real.rpow_natCast x 16,
        ← Real.rpow_mul hx0.le, ← Real.rpow_mul hx0.le, ← Real.rpow_add hx0]
      congr 1
      ring

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
