import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuFouvryKPhase
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryEffectiveAnalytic
noncomputable section
open Classical Finset
namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
theorem wExtractedFloorKey_phase_budget_kscale
    {Cscale M T x Z y : ℝ} (hC : 1 ≤ Cscale) (hM : 0 < M) (hT : 0 < T) (hZ : 0 ≤ Z)
    (hx : x = 4 * M * T) (hy : y ∈ Set.Icc (1 / 2 : ℝ) 3)
    {N Q : Finset ℕ} (hN : ∀ n ∈ N, T ≤ (n : ℝ))
    (hQ : ∀ q ∈ Q, 0 < q) {a : ℤ} (ha : |(a : ℝ)| ≤ Cscale*x)
    {P : WOriginalTuple → Prop} {R S ξ : ℝ} {b : ℕ} {K : WExtractedKey}
    {t : WExtractedTuple × ℤ}
    (ht : t ∈ wExtractedKeyFiber (wFloorCutoff M Z) N Q a P R S ξ b K) :
    let v := wGCDTuple (wExtractedOriginal t.1)
    |(t.2 : ℝ)| *
        (|M * y| / ((K.D : ℝ) * v.k₁ * t.1.1.2.1 * t.1.1.2.2) +
          |(a : ℝ)| / ((v.n₁ : ℝ) * v.k₁ * t.1.1.2.1 * t.1.1.2.2 * K.D')) ≤
      (3+4*Cscale) * Z := by
  have hNpos : ∀ n ∈ N, 0 < n := fun n hn =>
    Nat.cast_pos.mp (hT.trans_le (hN n hn))
  have hf := (mem_filter.mp (mem_wExtractedKeyFiber_iff.mp ht).1).1
  obtain ⟨hz, hlo, hhi⟩ := mem_wExtractedFrequencies_iff.mp hf
  have hm := mem_wFactorExtractionTuples_iff.mp hz
  obtain ⟨hv, _⟩ := wExtractedOriginal_valid hNpos hQ hz
  have hmem : (wExtractedOriginal t.1).2.1 ∈ N := hm.2.2.2.2.2.2.2.1
  have hu : |M * y| ≤ 3 * M := by
    rw [abs_of_nonneg (mul_nonneg hM.le (by linarith [hy.1]))]
    nlinarith [hy.2]
  have hb := wAnalytic_phase_budget_kscale hv hC hM.le hT (hN _ hmem) hx ha hu t.2
  have hl : 0 < (wExtractedOriginal t.1).1.1.lcm (wExtractedOriginal t.1).1.2 := by
    rw [hv.lcm_eq]
    exact Nat.mul_pos (Nat.mul_pos hv.D_pos hv.k₁_pos) hv.k₂_pos
  have hs := wFloorCutoff_mem_Icc_scale hM hZ hl (mem_Icc.mpr ⟨hlo, hhi⟩)
  have hp := hb.trans (show
      (3+4*Cscale) * M * |(t.2 : ℝ)| /
          ((wExtractedOriginal t.1).1.1.lcm (wExtractedOriginal t.1).1.2 : ℝ) ≤
        (3+4*Cscale) * Z from by
      calc
        _ = (3+4*Cscale) * (M * |(t.2 : ℝ)| /
          ((wExtractedOriginal t.1).1.1.lcm (wExtractedOriginal t.1).1.2 : ℝ)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hs (by positivity))
  have hk := wExtracted_k₂_eq hNpos hQ hz
  have hmods := wExtractedKeyFiber_moduli ht
  simpa only [hk, Nat.cast_mul, mul_assoc, hmods.1, hmods.2] using hp


end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
