import MathlibNt.SieveTheory.LiLiuFouvryG9RelaxedIntegral

noncomputable section
open scoped BigOperators Topology
open Filter Finset
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
open MathlibNt.SieveTheory.LiuWeight
open PrimeReciprocalLogRectangle PrimeReciprocalLogScale
local instance fouvryG9IntegralFiniteDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- Corner denominators stay positive uniformly, including coarse grids. -/
theorem fouvryG9RelaxedIntegral_corner_pos {n : ℕ} (hn : 0 < n)
    {δ : ℝ} (hδ : δ ≤ 1/4) (q : Fin n × Fin n) :
    0 < fouvryG9RelaxedIntegralCorner n δ q := by
  have hg := goldbachB9LogGridCell_cornerGap_pos hn q
  have ha := goldbachB9AlphaGridPoint_succ_le_end hn q.1.isLt
  unfold fouvryG9RelaxedIntegralCorner
  apply one_div_pos.mpr
  exact mul_pos hg (by linarith)

/-- The true moving kernel is bounded by a fixed upper-corner weight. -/
theorem fouvryG9RelaxedIntegral_term_le_corner {n N : ℕ} (hn : 0 < n)
    {ρ δ : ℝ} (hN : 2 ≤ N) (hρ : 1 < ρ) (hδ : δ ≤ 1/4)
    (q : Fin n × Fin n) (rs : ℕ × ℕ)
    (hrect : LiuPairInLogRectangle N
      (goldbachB9AlphaGridPoint n q.1) (goldbachB9AlphaGridPoint n (q.1+1))
      (goldbachB9BetaGridPoint n q.2) (goldbachB9BetaGridPoint n (q.2+1)) rs)
    (hr : rs.1.Prime) (hs : rs.2.Prime) :
    1 / ((rs.1 : ℝ)*rs.2*(1+3*Real.log ρ/Real.log (N : ℝ)-
      primeLogExponent N rs.1-primeLogExponent N rs.2)*
      ((5/9 : ℝ)*(1-primeLogExponent N rs.1)-δ)) ≤
    fouvryG9RelaxedIntegralCorner n δ q * (1/((rs.1 : ℝ)*rs.2)) := by
  have hrp : (0 : ℝ) < rs.1 := by exact_mod_cast hr.pos
  have hsp : (0 : ℝ) < rs.2 := by exact_mod_cast hs.pos
  have hln : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hw : 0 ≤ 3*Real.log ρ/Real.log (N : ℝ) := by
    exact div_nonneg (mul_nonneg (by norm_num) (Real.log_pos hρ).le) hln.le
  have hg := goldbachB9LogGridCell_cornerGap_pos hn q
  have ha := goldbachB9AlphaGridPoint_succ_le_end hn q.1.isLt
  have ht : 0 < (5/9 : ℝ)*(1-goldbachB9AlphaGridPoint n (q.1+1))-δ := by linarith
  have hgap : 1-goldbachB9AlphaGridPoint n (q.1+1)-goldbachB9BetaGridPoint n (q.2+1) ≤
      1+3*Real.log ρ/Real.log (N : ℝ)-primeLogExponent N rs.1-primeLogExponent N rs.2 := by
    linarith [hrect.2.1, hrect.2.2.2]
  have hweight : (5/9 : ℝ)*(1-goldbachB9AlphaGridPoint n (q.1+1))-δ ≤
      (5/9 : ℝ)*(1-primeLogExponent N rs.1)-δ := by linarith [hrect.2.1]
  have hd := mul_le_mul hgap hweight ht.le (hg.le.trans hgap)
  calc
    _ ≤ 1 / (((rs.1 : ℝ)*rs.2)*
        ((1-goldbachB9AlphaGridPoint n (q.1+1)-goldbachB9BetaGridPoint n (q.2+1))*
        ((5/9 : ℝ)*(1-goldbachB9AlphaGridPoint n (q.1+1))-δ))) := by
      apply one_div_le_one_div_of_le (by positivity)
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hd (mul_pos hrp hsp).le
    _ = _ := by
      unfold fouvryG9RelaxedIntegralCorner
      simp only [one_div, mul_inv]
      ring

/-- Source membership is used only for primality when enlarging to a rectangle. -/
theorem fouvryG9RelaxedIntegral_rectangle_subset {N : ℕ} (hN : 2 ≤ N)
    (ρ a₀ a₁ b₀ b₁ : ℝ) :
    (fouvryG9RelaxedPairs N ρ).filter (LiuPairInLogRectangle N a₀ a₁ b₀ b₁) ⊆
      primeLogRectanglePairs N a₀ a₁ b₀ b₁ := by
  intro rs hrs
  obtain ⟨hsource, hrect⟩ := Finset.mem_filter.mp hrs
  have hp := (Finset.mem_filter.mp hsource).2
  have hrBounds := (primeLogExponent_mem_interval_iff
    (show 1 < N by omega) hp.1.pos a₀ a₁).mp ⟨hrect.1, hrect.2.1⟩
  have hsBounds := (primeLogExponent_mem_interval_iff
    (show 1 < N by omega) hp.2.1.pos b₀ b₁).mp ⟨hrect.2.2.1, hrect.2.2.2⟩
  rw [primeLogRectanglePairs, Finset.mem_product]
  constructor
  · exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (Nat.lt_succ_iff.mpr (by
        simpa [rpowFloor] using Nat.le_floor hrBounds.2)), hp.1, hrBounds⟩
  · exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (Nat.lt_succ_iff.mpr (by
        simpa [rpowFloor] using Nat.le_floor hsBounds.2)), hp.2.1, hsBounds⟩

/-- Named finite bridge: the actual relaxed kernel is bounded by a fixed finite
prime-reciprocal grid. No asymptotic premise or integral bound is assumed. -/
theorem fouvryG9RelaxedIntegral_kernel_le_grid (n N : ℕ) (hn : 0 < n) (hN : 2 ≤ N)
    {ρ h δ : ℝ} (hρ : 1 < ρ) (hδ : δ ≤ 1/4) (hh : h ≤ 1/20)
    (hw : 1+3*Real.log ρ/Real.log (N : ℝ) ≤ 1+h) :
    fouvryG9RelaxedPairKernel N ρ δ ≤ fouvryG9RelaxedIntegralGrid n N h δ := by
  classical
  let rect := fun (q : Fin n × Fin n) => LiuPairInLogRectangle N
    (goldbachB9AlphaGridPoint n q.1) (goldbachB9AlphaGridPoint n (q.1+1))
    (goldbachB9BetaGridPoint n q.2) (goldbachB9BetaGridPoint n (q.2+1))
  have hfirst : fouvryG9RelaxedPairKernel N ρ δ ≤
      ∑ rs ∈ fouvryG9RelaxedPairs N ρ, ∑ q ∈ fouvryG9RelaxedIntegralCells n h,
        if rect q rs then fouvryG9RelaxedIntegralCorner n δ q * (1/((rs.1 : ℝ)*rs.2)) else 0 := by
    apply Finset.sum_le_sum
    intro rs hrs
    obtain ⟨q, hq, hrect⟩ := fouvryG9RelaxedIntegral_cover n N hn hN hρ hh hw hrs
    have hp := (Finset.mem_filter.mp hrs).2
    have hc := fouvryG9RelaxedIntegral_term_le_corner hn hN hρ hδ q rs hrect hp.1 hp.2.1
    have hsingle := Finset.single_le_sum (s := fouvryG9RelaxedIntegralCells n h)
      (f := fun q => if rect q rs then fouvryG9RelaxedIntegralCorner n δ q *
        (1/((rs.1 : ℝ)*rs.2)) else 0) (fun q _ => by
          split_ifs
          · exact mul_nonneg (fouvryG9RelaxedIntegral_corner_pos hn hδ q).le (by positivity)
          · exact le_rfl) hq
    rw [if_pos hrect] at hsingle
    exact hc.trans hsingle
  apply hfirst.trans
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro q _
  change (∑ rs ∈ fouvryG9RelaxedPairs N ρ, if rect q rs then _ else 0) ≤ _
  rw [← Finset.sum_filter]
  rw [← Finset.mul_sum]
  apply (mul_le_mul_of_nonneg_left _ (fouvryG9RelaxedIntegral_corner_pos hn hδ q).le)
  rw [← sum_primeLogRectanglePairs_eq_primeReciprocalLogRectangle]
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (fouvryG9RelaxedIntegral_rectangle_subset hN ρ _ _ _ _) (fun _ _ _ => by positivity)

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
