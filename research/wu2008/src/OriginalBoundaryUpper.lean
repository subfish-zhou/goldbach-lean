import OriginalBoundaryGeometry
open MeasureTheory Set
open scoped BigOperators Interval
noncomputable section
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
open MathlibNt.SieveTheory.LiuWeight
namespace OriginalU8.Weighted
variable {a : ℝ}
theorem upperIntegrand_eq_of_mem {n : ℕ} {h : ℝ} (hn : 0 < n)
    {q : Fin n × Fin n} (hq : q ∈ cells a n h)
    {x : ℝ × ℝ} (hx : x ∈ goldbachB9LogGridCell n q) :
    upperIntegrand a n h x =
      fouvryG9RelaxedIntegralCorner n 0 q * liuLogDensity x := by
  classical
  unfold upperIntegrand
  rw [Finset.sum_eq_single q]
  · rw [indicator_of_mem hx]
  · intro r _ hrq
    have hnot : x ∉ goldbachB9LogGridCell n r := fun hxr =>
      Set.disjoint_left.mp
        (goldbachB9LogGridCell_pairwiseDisjoint hn (mem_univ q) (mem_univ r) hrq.symm)
        hx hxr
    rw [indicator_of_notMem hnot, mul_zero]
  · exact fun h => (h hq).elim

theorem upperIntegrand_eq_zero {n : ℕ} {h : ℝ} {x : ℝ × ℝ}
    (hx : x ∉ region a n h) : upperIntegrand a n h x = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro q hq
  have hnot : x ∉ goldbachB9LogGridCell n q :=
    fun h => hx (Set.mem_iUnion₂.mpr ⟨q, hq, h⟩)
  rw [indicator_of_notMem hnot, mul_zero]

theorem upperIntegrand_le {n : ℕ} (hn : 0 < n) {h : ℝ}
    {x : ℝ × ℝ} (hx : x ∈ region a n h) :
    upperIntegrand a n h x ≤ 1500 := by
  obtain ⟨q, hq, hxq⟩ := Set.mem_iUnion₂.mp hx
  rw [upperIntegrand_eq_of_mem hn hq hxq, fouvryG9RelaxedIntegralCorner_zero]
  have hc : (goldbachB9AlphaGridPoint n (q.1+1), goldbachB9BetaGridPoint n (q.2+1)) ∈
      goldbachB9LogAmbientBox :=
    goldbachB9LogGridCell_subset_ambientBox hn q
      ⟨⟨goldbachB9AlphaGridPoint_lt_succ hn, le_rfl⟩,
        ⟨goldbachB9BetaGridPoint_lt_succ hn, le_rfl⟩⟩
  have hk := fouvryG9Weighted_kernel_bounds hc
  have hd := goldbachB9LogDensity_bounds (goldbachB9LogGridCell_subset_ambientBox hn q hxq)
  have ht := mul_le_mul hk.2 hd.2 hd.1 (by norm_num : (0 : ℝ) ≤ 9)
  dsimp at hk ht
  nlinarith

theorem upperIntegrand_le_integrand_add {n : ℕ} (hn : 0 < n) {h : ℝ}
    {x : ℝ × ℝ} (hx : x ∈ region a n h) :
    upperIntegrand a n h x ≤ (9/5 : ℝ)*fouvryG9WeightedIntegrand x + 20000/n := by
  obtain ⟨q, hq, hxq⟩ := Set.mem_iUnion₂.mp hx
  rw [upperIntegrand_eq_of_mem hn hq hxq, fouvryG9RelaxedIntegralCorner_zero,
    fouvryG9WeightedIntegrand_eq]
  have hb := goldbachB9LogGridCell_subset_ambientBox hn q hxq
  have ha := goldbachB9AlphaGridStep_pos hn
  have hv := goldbachB9BetaGridStep_pos hn
  have hk := fouvryG9RelaxedIntegral_continuous_corner_error
    (by linarith [hb.1.1] : 0 ≤ x.1) (by linarith [hb.2.1] : 0 ≤ x.2)
    hxq.1.2 hxq.2.2 (goldbachB9AlphaGridPoint_succ_le_end hn q.1.isLt)
    (goldbachB9BetaGridPoint_succ_le_end hn q.2.isLt)
    (add_nonneg ha.le hv.le)
    (by rw [goldbachB9AlphaGridPoint_succ]; linarith [hxq.1.1] :
      goldbachB9AlphaGridPoint n (q.1+1)-x.1 ≤ goldbachB9AlphaGridStep n+goldbachB9BetaGridStep n)
    (by rw [goldbachB9BetaGridPoint_succ]; linarith [hxq.2.1] :
      goldbachB9BetaGridPoint n (q.2+1)-x.2 ≤ goldbachB9AlphaGridStep n+goldbachB9BetaGridStep n)
  have hd := goldbachB9LogDensity_bounds hb
  have hm := mul_le_mul_of_nonneg_right hk hd.1
  have he := mul_le_mul_of_nonneg_left hd.2
    (show 0 ≤ 243*(goldbachB9AlphaGridStep n+goldbachB9BetaGridStep n) by positivity)
  have herr : (9/5 : ℝ)*243*(goldbachB9AlphaGridStep n+goldbachB9BetaGridStep n)*80 ≤ 20000/n := by
    unfold goldbachB9AlphaGridStep goldbachB9BetaGridStep goldbachB9AlphaGridWidth goldbachB9BetaGridWidth
    have hnr : (0 : ℝ) < n := by exact_mod_cast hn
    field_simp
    norm_num
  nlinarith


end OriginalU8.Weighted
