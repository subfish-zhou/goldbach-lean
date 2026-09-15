import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuFouvryKFloorPhase
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryAnalyticBox
noncomputable section
open Classical Finset
namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
theorem wAnalyticDyadicBlock_parameter_budget_kscale
    {Cscale M T x Z y : ℝ} (hC : 1 ≤ Cscale) (hM : 0 < M) (hT : 0 < T) (hZ : 0 ≤ Z)
    (hx : x = 4 * M * T) (hy : y ∈ Set.Icc (1 / 2 : ℝ) 3)
    {N Q : Finset ℕ} (hN : ∀ n ∈ N, T ≤ (n : ℝ))
    (hQ : ∀ q ∈ Q, 0 < q) {a : ℤ} (ha : |(a : ℝ)| ≤ Cscale*x)
    {P : WOriginalTuple → Prop} {R S ξ : ℝ} {b : ℕ} {K : WExtractedKey}
    {j : Fin 5 → ℕ} {positive : Bool} {t : WExtractedTuple × ℤ}
    (ht : t ∈ wAnalyticDyadicBlock
      (wExtractedKeyFiber (wFloorCutoff M Z) N Q a P R S ξ b K) j positive) :
    |wBlockPhaseA K j positive (M * y)| + |wBlockPhaseB K j positive a| ≤ 112 * (Cscale*Z) := by
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
  have hp := wExtractedFloorKey_phase_budget_kscale hC hM hT hZ hx hy hN hQ ha htf
  rw [wBlockPhase_abs K j positive hD hD']
  exact href.trans ((mul_le_mul_of_nonneg_left hp (by norm_num : (0 : ℝ) ≤ 16)).trans
    (by nlinarith [mul_nonneg (sub_nonneg.mpr hC) hZ]))


end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
