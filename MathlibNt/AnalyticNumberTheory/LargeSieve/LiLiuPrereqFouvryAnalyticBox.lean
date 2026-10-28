import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryEffectiveAnalytic
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryDyadicCoordinates
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvrySlowFactorDifference

/-!
# Concrete normalized slow-phase parameters on actual dyadic W blocks

The parameter bound is derived from a member of the actual floor-retained
carrier. It therefore applies to the entire continuous normalized rectangle
without mistaking an arbitrary key-box member for positive canonical data.
-/

noncomputable section
open Classical Finset

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
open _root_.LiLiuPrereqFouvry

theorem normalizedWeight_eq_fourierChar (A B : ℝ) (v : Fin 5 → ℝ) :
    SlowFactor.normalizedWeight A B v =
      (((v 1 * v 3 * v 4)⁻¹ : ℝ) : ℂ) *
        (Real.fourierChar (A * v 0 / (v 1 * v 3 * v 4) +
          B * v 0 / (v 1 * v 2 * v 3 * v 4)) : ℂ) := by
  unfold SlowFactor.normalizedWeight
  rw [Real.fourierChar_apply]
  congr 2
  push_cast
  ring

def wBlockAmplitude (K : WExtractedKey) (j : Fin 5 → ℕ) : ℝ :=
  ((K.D : ℝ) * (2 : ℝ) ^ j 1 * (2 : ℝ) ^ j 3 * (2 : ℝ) ^ j 4)⁻¹

def wBlockPhaseA (K : WExtractedKey) (j : Fin 5 → ℕ) (positive : Bool) (u : ℝ) : ℝ :=
  -(if positive then 1 else -1) * (2 : ℝ) ^ j 0 * u /
    ((K.D : ℝ) * (2 : ℝ) ^ j 1 * (2 : ℝ) ^ j 3 * (2 : ℝ) ^ j 4)

def wBlockPhaseB (K : WExtractedKey) (j : Fin 5 → ℕ) (positive : Bool) (a : ℤ) : ℝ :=
  (if positive then 1 else -1) * (2 : ℝ) ^ j 0 * (a : ℝ) /
    ((2 : ℝ) ^ j 2 * (2 : ℝ) ^ j 1 * (2 : ℝ) ^ j 3 * (2 : ℝ) ^ j 4 * K.D')

/-- Exact transport to the concrete weight whose mixed derivatives and
rectangular increments have been proved, including the frequency sign. -/
theorem wAnalyticWeight_eq_normalized_block
    {U : Finset (WExtractedTuple × ℤ)} {j : Fin 5 → ℕ} {positive : Bool}
    {t : WExtractedTuple × ℤ} (ht : t ∈ wAnalyticDyadicBlock U j positive)
    (K : WExtractedKey) (a : ℤ) (u : ℝ) :
    let v := wGCDTuple (wExtractedOriginal t.1)
    wAnalyticWeight K.D K.D' a u t.2 v.k₁ v.n₁ t.1.1.2.1 t.1.1.2.2 =
      (wBlockAmplitude K j : ℂ) *
        SlowFactor.normalizedWeight (wBlockPhaseA K j positive u)
          (wBlockPhaseB K j positive a) (wAnalyticUnitCoordinates j t) := by
  have hc (i : Fin 5) :
      (2 : ℝ) ^ j i * wAnalyticUnitCoordinates j t i = (wAnalyticCoordinates t i : ℝ) := by
    unfold wAnalyticUnitCoordinates
    field_simp
  have hf : ((if positive then 1 else -1) * (2 : ℝ) ^ j 0) *
      wAnalyticUnitCoordinates j t 0 = (t.2 : ℝ) := by
    rw [mul_assoc, hc, wAnalyticDyadicBlock_frequency ht]
  have he := wAnalyticWeight_normalize K.D K.D' a u
    ((if positive then 1 else -1) * (2 : ℝ) ^ j 0)
    ((2 : ℝ) ^ j 1) ((2 : ℝ) ^ j 2) ((2 : ℝ) ^ j 3) ((2 : ℝ) ^ j 4)
    (wAnalyticUnitCoordinates j t)
  rw [hf, hc 1, hc 2, hc 3, hc 4] at he
  change wAnalyticWeight K.D K.D' a u t.2
    (wGCDTuple (wExtractedOriginal t.1)).k₁ (wGCDTuple (wExtractedOriginal t.1)).n₁
    t.1.1.2.1 t.1.1.2.2 = _ at he
  rw [normalizedWeight_eq_fourierChar]
  dsimp only
  rw [he]
  simp only [wBlockAmplitude, wBlockPhaseA, wBlockPhaseB, neg_mul, mul_assoc,
    Complex.ofReal_inv, Complex.ofReal_mul]

theorem wBlockPhase_abs (K : WExtractedKey) (j : Fin 5 → ℕ) (positive : Bool)
    (hD : 0 < K.D) (hD' : 0 < K.D') (u : ℝ) (a : ℤ) :
    |wBlockPhaseA K j positive u| + |wBlockPhaseB K j positive a| =
      (2 : ℝ) ^ j 0 *
        (|u| / ((K.D : ℝ) * (2 : ℝ) ^ j 1 * (2 : ℝ) ^ j 3 * (2 : ℝ) ^ j 4) +
          |(a : ℝ)| /
            ((2 : ℝ) ^ j 2 * (2 : ℝ) ^ j 1 * (2 : ℝ) ^ j 3 * (2 : ℝ) ^ j 4 * K.D')) := by
  have hDr : (0 : ℝ) < K.D := by exact_mod_cast hD
  have hD'r : (0 : ℝ) < K.D' := by exact_mod_cast hD'
  cases positive <;>
    simp only [wBlockPhaseA, wBlockPhaseB, Bool.false_eq_true, ↓reduceIte,
      neg_neg, one_mul, neg_mul, abs_neg, abs_mul, abs_div,
      abs_of_pos (pow_pos (by norm_num : (0 : ℝ) < 2) _),
      abs_of_pos hDr, abs_of_pos hD'r] <;> ring


end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
