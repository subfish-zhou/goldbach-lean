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

/-- The actual large-residue assumptions bound the two reference
coefficients by `112 Z`, independently of every changing arithmetic
parameter. The continuous normalized weight may now be estimated on
all of `[1,2]^5`, keeping its own explicit coordinate constants. -/
theorem wAnalyticDyadicBlock_parameter_budget
    {M T x Z y : ℝ} (hM : 0 < M) (hT : 0 < T) (hZ : 0 ≤ Z)
    (hx : x = 4 * M * T) (hy : y ∈ Set.Icc (1 / 2 : ℝ) 3)
    {N Q : Finset ℕ} (hN : ∀ n ∈ N, T ≤ (n : ℝ))
    (hQ : ∀ q ∈ Q, 0 < q) {a : ℤ} (ha : |(a : ℝ)| ≤ x)
    {P : WOriginalTuple → Prop} {R S ξ : ℝ} {b : ℕ} {K : WExtractedKey}
    {j : Fin 5 → ℕ} {positive : Bool} {t : WExtractedTuple × ℤ}
    (ht : t ∈ wAnalyticDyadicBlock
      (wExtractedKeyFiber (wFloorCutoff M Z) N Q a P R S ξ b K) j positive) :
    |wBlockPhaseA K j positive (M * y)| + |wBlockPhaseB K j positive a| ≤ 112 * Z := by
  have hNpos : ∀ n ∈ N, 0 < n := fun n hn =>
    Nat.cast_pos.mp (hT.trans_le (hN n hn))
  have htf := (mem_filter.mp ht).1
  obtain ⟨hD, hD', _, _, hk, hn, hr, hs, _⟩ :=
    wExtractedKeyFiber_positive hNpos hQ htf
  have hb := wAnalyticDyadicBlock_bounds hNpos hQ ht
  have hb₀ : (2 : ℝ) ^ j 0 ≤ |(t.2 : ℝ)| := by
    simpa only [wAnalyticCoordinates, Matrix.cons_val_zero, Nat.cast_natAbs, Int.cast_abs]
      using (hb 0).1
  have hb₁ : ((wGCDTuple (wExtractedOriginal t.1)).k₁ : ℝ) ≤ 2 * (2 : ℝ) ^ j 1 :=
    (hb 1).2.le
  have hb₂ : ((wGCDTuple (wExtractedOriginal t.1)).n₁ : ℝ) ≤ 2 * (2 : ℝ) ^ j 2 :=
    (hb 2).2.le
  have hb₃ : (t.1.1.2.1 : ℝ) ≤ 2 * (2 : ℝ) ^ j 3 := (hb 3).2.le
  have hb₄ : (t.1.1.2.2 : ℝ) ≤ 2 * (2 : ℝ) ^ j 4 := (hb 4).2.le
  have href := wAnalytic_reference_budget
    (D := K.D) (D' := K.D') (h := t.2)
    (k := (wGCDTuple (wExtractedOriginal t.1)).k₁)
    (n := (wGCDTuple (wExtractedOriginal t.1)).n₁)
    (r := t.1.1.2.1) (s := t.1.1.2.2)
    (by exact_mod_cast hD) (by exact_mod_cast hD')
    (by exact_mod_cast hk) (by exact_mod_cast hn) (by exact_mod_cast hr) (by exact_mod_cast hs)
    (pow_pos (by norm_num) (j 1)) (pow_pos (by norm_num) (j 2))
    (pow_pos (by norm_num) (j 3)) (pow_pos (by norm_num) (j 4))
    (show (0 : ℝ) ≤ 2 ^ j 0 by positivity) hb₀ hb₁ hb₂ hb₃ hb₄ (M * y) a
  have hp := wExtractedFloorKey_phase_budget hM hT hZ hx hy hN hQ ha htf
  rw [wBlockPhase_abs K j positive hD hD']
  exact href.trans ((mul_le_mul_of_nonneg_left hp (by norm_num : (0 : ℝ) ≤ 16)).trans
    (by ring_nf; rfl))

/-- The actual source parameters now satisfy the full five-variable
mixed-derivative bound, not an assumed derivative or variation estimate. -/
theorem wAnalyticDyadicBlock_mixedDeriv_bound
    {M T x Z y : ℝ} (hM : 0 < M) (hT : 0 < T) (hZ : 0 ≤ Z)
    (hx : x = 4 * M * T) (hy : y ∈ Set.Icc (1 / 2 : ℝ) 3)
    {N Q : Finset ℕ} (hN : ∀ n ∈ N, T ≤ (n : ℝ))
    (hQ : ∀ q ∈ Q, 0 < q) {a : ℤ} (ha : |(a : ℝ)| ≤ x)
    {P : WOriginalTuple → Prop} {R S ξ : ℝ} {b : ℕ} {K : WExtractedKey}
    {j : Fin 5 → ℕ} {positive : Bool} {t : WExtractedTuple × ℤ}
    (ht : t ∈ wAnalyticDyadicBlock
      (wExtractedKeyFiber (wFloorCutoff M Z) N Q a P R S ξ b K) j positive)
    (js : List (Fin 5)) (hjs : js.Nodup) (v : Fin 5 → ℝ)
    (hv : ∀ i, 1 ≤ v i ∧ v i ≤ 2) :
    ‖SlowFactor.mixedDeriv js
      (SlowFactor.normalizedWeight (wBlockPhaseA K j positive (M * y))
        (wBlockPhaseB K j positive a)) v‖ ≤
      64 * (6 + 2 * Real.pi) ^ 5 * (1 + 112 * Z) ^ 5 :=
  SlowFactor.norm_mixedDeriv_normalizedWeight_le _ _ _
    (wAnalyticDyadicBlock_parameter_budget hM hT hZ hx hy hN hQ ha ht) js hjs v hv

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
