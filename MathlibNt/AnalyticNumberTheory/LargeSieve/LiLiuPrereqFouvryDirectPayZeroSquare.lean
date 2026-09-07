import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryDirectPayZeroEnvelope

noncomputable section
open Classical Finset
namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

/-- Literal mass and zero term, with all local geometry paid before taking roots. -/
theorem directPayZero_square
    {ε ρ Czero Ccoeff Couter x T Z R S : ℝ}
    (hCz : 0 ≤ Czero) (_hCc : 0 ≤ Ccoeff) (hCo : 0 ≤ Couter)
    (hx : 0 < x) (hT : 0 < T) (hZ : 0 ≤ Z) (hR : 0 ≤ R) (hS : 0 ≤ S)
    (K : WExtractedKey) (F : ℕ) (j : Fin 5 → ℕ)
    (hD : 0 < K.D) (hF : (F : ℝ) ≤ 2*T) (hn : (2 : ℝ)^j 2 ≤ 2*T)
    (hk : (2 : ℝ)^j 1 ≤ R*S) (hr : (2 : ℝ)^j 3 ≤ R)
    (hfreq : (2 : ℝ)^j 0 ≤
      32*((K.D : ℝ)*2^j 1*2^j 3*2^j 4)*Z*T/x) :
    (wBlockAmplitude K j * Real.sqrt (directJoinedMass ρ Couter x T j) *
      Real.sqrt (directJoinedZero ε ρ Czero Ccoeff x K F j) / T^2)^2 ≤
    1024 * (Ccoeff^4*Couter*Czero) * x^(5*ρ) *
      wGramResonanceScaleEnvelope K F j ε * Z * (R^2*S/x) := by
  have hd : (1 : ℝ) ≤ K.D := by exact_mod_cast hD
  have hf : ((F / K.1.1 : ℕ) : ℝ) ≤ 2*T :=
    (Nat.cast_le.mpr (Nat.div_le_self F K.1.1)).trans hF
  have hh := directPayZero_scalar hd (by positivity) (by positivity) (by positivity)
    (by positivity) (by positivity) (Nat.cast_nonneg (F/K.1.1)) hT hx hZ hR hS
    hfreq hn hf hk hr
  have hm : 0 ≤ directJoinedMass ρ Couter x T j := by
    unfold directJoinedMass
    positivity
  have hz : 0 ≤ directJoinedZero ε ρ Czero Ccoeff x K F j := by
    unfold directJoinedZero
    exact mul_nonneg (by positivity) (wGramResonanceScaleEnvelope_nonneg K F j ε)
  rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt hm, Real.sq_sqrt hz]
  have hp : (x^ρ)^5 = x^(5*ρ) := by
    rw [← Real.rpow_natCast (x^ρ) 5, ← Real.rpow_mul hx.le]
    congr 1
    ring
  calc
    _ = (Ccoeff^4*Couter*Czero) * x^(5*ρ) * wGramResonanceScaleEnvelope K F j ε *
      (((K.D : ℝ)*2^j 1*2^j 3*2^j 4)⁻¹ ^ 2 * (8*2^j 1*2^j 3*T) *
        (2^j 1*(2^j 3*2^j 2*2^j 0*(F/K.1.1 : ℕ)*2^j 4)) / (T^2)^2) := by
      unfold directJoinedMass directJoinedZero wGramResonanceScaleBoxCard wBlockAmplitude
      push_cast
      rw [← hp]
      ring
    _ ≤ (Ccoeff^4*Couter*Czero) * x^(5*ρ) * wGramResonanceScaleEnvelope K F j ε *
      (1024*Z*(R^2*S/x)) :=
      mul_le_mul_of_nonneg_left hh (mul_nonneg (by positivity)
        (wGramResonanceScaleEnvelope_nonneg K F j ε))
    _ = _ := by ring

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
