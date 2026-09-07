import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryDirectPaySecondaryGrowth

noncomputable section
open Classical Finset
namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

/-- All arithmetic excess factors, but no structural powers or section length. -/
def directPaySecondaryWeight (κ δ ρ C Csec Ccoeff x : ℝ) (a : ℤ)
    (K : WExtractedKey) (F : ℕ) (j : Fin 5 → ℕ) : ℝ :=
  C * (Ccoeff * x ^ ρ) ^ 4 *
    (1 + Real.log (2 * (2 : ℝ) ^ j 0)) * (a.natAbs.divisors.card : ℝ) *
    (16 * (2 : ℝ) ^ j 2 * (2 : ℝ) ^ j 3 * (2 : ℝ) ^ j 4 * (2 : ℝ) ^ j 4) ^ κ *
    Real.sqrt (Csec * (wGramSecondaryNumeratorMax a K F j : ℝ) ^ δ)

theorem directPaySecondary_weight_nonneg {κ δ ρ C Csec Ccoeff x : ℝ}
    (hC : 0 ≤ C) (a : ℤ) (K : WExtractedKey) (F : ℕ) (j : Fin 5 → ℕ) :
    0 ≤ directPaySecondaryWeight κ δ ρ C Csec Ccoeff x a K F j := by
  have hlog : 0 ≤ Real.log (2 * (2 : ℝ) ^ j 0) := by
    apply Real.log_nonneg
    have hp : (1 : ℝ) ≤ 2 ^ j 0 := one_le_pow₀ (by norm_num)
    linarith
  unfold directPaySecondaryWeight
  positivity

/-- Actual energy, not a hypothesis. Both q contributions remain literal. -/
theorem directPaySecondary_energy_local
    {κ δ ρ C Csec Ccoeff x T : ℝ} (hκ : 0 ≤ κ) (hC : 0 ≤ C)
    (hCsec : 0 ≤ Csec) (_hT : 0 ≤ T) (a : ℤ) (R S : ℝ)
    (K : WExtractedKey) (F : ℕ) (j cap : Fin 5 → ℕ) (hF : (F : ℝ) ≤ 2 * T) :
    directJoinedSecondary κ δ ρ C Csec Ccoeff x a R S K F j cap ≤
      (256 * Real.sqrt 8) * directPaySecondaryWeight κ δ ρ C Csec Ccoeff x a K F j *
        (2 : ℝ) ^ j 0 * ((2 : ℝ) ^ j 2) ^ 2 * T ^ 2 *
        (2 : ℝ) ^ j 3 * Real.sqrt ((2 : ℝ) ^ j 3) * ((2 : ℝ) ^ j 4) ^ 3 *
        ((K.D' : ℝ) + 2 * (2 : ℝ) ^ j 1 /
          ((2 : ℝ) ^ j 2 * (2 : ℝ) ^ j 3 * (2 : ℝ) ^ j 4 * (2 : ℝ) ^ j 4)) := by
  have hbase : 0 ≤ wGramSecondaryBaseCountBound K F j := by
    rw [directPaySecondary_count]
    have hl : 0 ≤ Real.log (2 * (2 : ℝ) ^ j 0) := by
      apply Real.log_nonneg
      have hp : (1 : ℝ) ≤ 2 ^ j 0 := one_le_pow₀ (by norm_num)
      linarith
    positivity
  have hh := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left (directPaySecondary_envelope (δ := δ) (Cτ := Csec) hκ hC a R S K F j cap)
      (sq_nonneg ((Ccoeff * x ^ ρ) * (Ccoeff * x ^ ρ)))) hbase
  change directJoinedSecondary κ δ ρ C Csec Ccoeff x a R S K F j cap ≤ _ at hh
  rw [directPaySecondary_count] at hh
  have halg := directPaySecondary_root_algebra
    (show 0 < (2 : ℝ) ^ j 2 by positivity)
    (show 0 < (2 : ℝ) ^ j 3 by positivity)
    (show 0 < (2 : ℝ) ^ j 4 by positivity)
    (show 0 ≤ Csec * (wGramSecondaryNumeratorMax a K F j : ℝ) ^ δ by positivity) κ
  have hfrac : ((F / K.1.1 : ℕ) : ℝ) ≤ 2 * T :=
    (Nat.cast_le.mpr (Nat.div_le_self _ _)).trans hF
  have hsq : (((F / K.1.1 : ℕ) : ℝ)) ^ 2 ≤ 4 * T ^ 2 := by
    nlinarith [sq_nonneg (2 * T - ((F / K.1.1 : ℕ) : ℝ))]
  calc
    _ ≤ _ := hh
    _ = (64 * Real.sqrt 8) * directPaySecondaryWeight κ δ ρ C Csec Ccoeff x a K F j *
        (2 : ℝ) ^ j 0 * ((2 : ℝ) ^ j 2) ^ 2 * (((F / K.1.1 : ℕ) : ℝ)) ^ 2 *
        (2 : ℝ) ^ j 3 * Real.sqrt ((2 : ℝ) ^ j 3) * ((2 : ℝ) ^ j 4) ^ 3 *
        ((K.D' : ℝ) + 2 * (2 : ℝ) ^ j 1 /
          ((2 : ℝ) ^ j 2 * (2 : ℝ) ^ j 3 * (2 : ℝ) ^ j 4 * (2 : ℝ) ^ j 4)) := by
      unfold directPaySecondaryWeight
      linear_combination
        8 * (2 : ℝ) ^ j 0 * (2 : ℝ) ^ j 2 * (((F / K.1.1 : ℕ) : ℝ)) ^ 2 *
          (2 : ℝ) ^ j 4 * (1 + Real.log (2 * (2 : ℝ) ^ j 0)) *
          (Ccoeff * x ^ ρ) ^ 4 * C * (a.natAbs.divisors.card : ℝ) *
          ((K.D' : ℝ) + 2 * (2 : ℝ) ^ j 1 /
            ((2 : ℝ) ^ j 2 * (2 : ℝ) ^ j 3 * (2 : ℝ) ^ j 4 * (2 : ℝ) ^ j 4)) * halg
    _ ≤ _ := by
      have hw := directPaySecondary_weight_nonneg (κ := κ) (δ := δ) (ρ := ρ)
        (Csec := Csec) (Ccoeff := Ccoeff) (x := x) hC a K F j
      calc
        _ ≤ (64 * Real.sqrt 8) * directPaySecondaryWeight κ δ ρ C Csec Ccoeff x a K F j *
          (2 : ℝ) ^ j 0 * ((2 : ℝ) ^ j 2) ^ 2 * (4 * T ^ 2) *
          (2 : ℝ) ^ j 3 * Real.sqrt ((2 : ℝ) ^ j 3) * ((2 : ℝ) ^ j 4) ^ 3 *
          ((K.D' : ℝ) + 2 * (2 : ℝ) ^ j 1 /
            ((2 : ℝ) ^ j 2 * (2 : ℝ) ^ j 3 * (2 : ℝ) ^ j 4 * (2 : ℝ) ^ j 4)) := by
            gcongr
        _ = _ := by ring

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
