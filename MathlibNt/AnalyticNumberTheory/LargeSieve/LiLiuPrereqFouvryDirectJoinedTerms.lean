import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryDirectJoinedPrefix

/-! # The explicit terms of the joined retained-prefix estimate
These are exactly the mass and three expressions in
`direct_retained_prefix_three_terms`, exposed for separate scalar payment.
-/
noncomputable section
namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

def directJoinedMass (ρ Couter x T : ℝ) (j : Fin 5 → ℕ) : ℝ :=
  Couter * x ^ ρ * (8 * (2 : ℝ) ^ j 1 * (2 : ℝ) ^ j 3 * T)

def directJoinedZero (ε ρ Czero Ccoeff x : ℝ) (K : WExtractedKey)
    (F : ℕ) (j : Fin 5 → ℕ) : ℝ :=
  ((Ccoeff * x ^ ρ) * (Ccoeff * x ^ ρ)) ^ 2 * (2 ^ j 1 : ℕ) * Czero *
    (wGramResonanceScaleBoxCard K F j : ℝ) * wGramResonanceScaleEnvelope K F j ε

def directJoinedSecondary (κ δ ρ Cnonzero Csecondary Ccoeff x : ℝ)
    (a : ℤ) (R S : ℝ) (K : WExtractedKey) (F : ℕ) (j cap : Fin 5 → ℕ) : ℝ :=
  wGramSecondaryBaseCountBound K F j *
    ((((Ccoeff * x ^ ρ) * (Ccoeff * x ^ ρ)) ^ 2) *
      wGramSecondaryScaleEnvelope κ δ Cnonzero Csecondary a R S K F j cap)

def directJoinedMain (κ δ ρ Cnonzero Cτ Cjoint Ca Ccoeff x : ℝ)
    (a : ℤ) (R S : ℝ) (K : WExtractedKey) (F : ℕ) (j cap : Fin 5 → ℕ) : ℝ :=
  ((Ccoeff * x ^ ρ) * (Ccoeff * x ^ ρ)) ^ 2 *
    wGramDirectMainSubpowerFactor κ δ Cnonzero Ca a R S K j cap *
      wGramMainJointMean δ Cτ Cjoint a K F j

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
