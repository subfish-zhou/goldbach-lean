import OriginalBoundaryIntegral
noncomputable section
open scoped BigOperators Topology
open Filter Finset
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
open MathlibNt.SieveTheory.LiuWeight
open MathlibNt.SieveTheory.PrimeReciprocalLogRectangle
open MathlibNt.SieveTheory.PrimeReciprocalLogScale
namespace OriginalU8.Weighted
local instance originalBoundaryDecidable (p : Prop) : Decidable p := Classical.propDecidable p
theorem original_log_geometry {N : ℕ} {ρ : ℝ}
    (hN : 2 ≤ N) (hρ : 1 < ρ) {rs : ℕ × ℕ}
    (hrs : rs ∈ relaxedPairs N ρ) :
    (100/1327 : ℝ) ≤ primeLogExponent N rs.1 ∧
    primeLogExponent N rs.1 < (1/10 : ℝ) ∧
    (1/3 : ℝ) ≤ primeLogExponent N rs.2 ∧
    primeLogExponent N rs.1 + 2*primeLogExponent N rs.2 ≤
      1+3*Real.log ρ/Real.log (N : ℝ) := by
  obtain ⟨_, hr, hs, hcut, hrupper, hslower, hprod⟩ := Finset.mem_filter.mp hrs
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hln : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hrp : (0 : ℝ) < rs.1 := by exact_mod_cast hr.pos
  have hsp : (0 : ℝ) < rs.2 := by exact_mod_cast hs.pos
  have hρp : 0 < ρ := by linarith
  have hcutlog := Real.log_le_log (Real.rpow_pos_of_pos hNp _) hcut
  have hrlog := Real.log_lt_log hrp hrupper
  have hslog := Real.log_le_log (Real.rpow_pos_of_pos hNp _) hslower
  rw [Real.log_rpow hNp] at hcutlog hrlog hslog
  have hprodlog := Real.log_le_log (mul_pos hrp (pow_pos hsp 2)) hprod
  rw [Real.log_mul hrp.ne' (pow_ne_zero 2 hsp.ne'), Real.log_pow,
    Real.log_mul (pow_ne_zero 3 hρp.ne') hNp.ne', Real.log_pow] at hprodlog
  refine ⟨(le_div_iff₀ hln).mpr hcutlog, (div_lt_iff₀ hln).mpr hrlog,
    (le_div_iff₀ hln).mpr hslog, ?_⟩
  unfold primeLogExponent
  apply (le_of_mul_le_mul_right ?_ hln)
  field_simp
  norm_num at hprodlog
  linarith

theorem original_cover (n N : ℕ) (hn : 0 < n) (hN : 2 ≤ N)
    {ρ h : ℝ} (hρ : 1 < ρ) (hh : h ≤ 1/20)
    (hw : 1+3*Real.log ρ/Real.log (N : ℝ) ≤ 1+h)
    {rs : ℕ × ℕ} (hrs : rs ∈ relaxedPairs N ρ) :
    ∃ q ∈ cells (100/1327) n h,
      LiuPairInLogRectangle N
        (goldbachB9AlphaGridPoint n q.1) (goldbachB9AlphaGridPoint n (q.1+1))
        (goldbachB9BetaGridPoint n q.2) (goldbachB9BetaGridPoint n (q.2+1)) rs := by
  obtain ⟨hlow, hfirst, hsecond, htriangle⟩ := original_log_geometry hN hρ hrs
  have halow : (1/20 : ℝ) < primeLogExponent N rs.1 := by linarith
  have hblow : (1/4 : ℝ) < primeLogExponent N rs.2 := by linarith
  have haup : primeLogExponent N rs.1 ≤ 1/20+(n : ℝ)*goldbachB9AlphaGridStep n := by
    rw [← goldbachB9AlphaGridPoint_eq_step, goldbachB9AlphaGridPoint_end hn]
    linarith
  have hbup : primeLogExponent N rs.2 ≤ 1/4+(n : ℝ)*goldbachB9BetaGridStep n := by
    rw [← goldbachB9BetaGridPoint_eq_step, goldbachB9BetaGridPoint_end hn]
    linarith
  obtain ⟨i, hi, hail, haiu⟩ := exists_nat_cell n (goldbachB9AlphaGridStep_pos hn) halow haup
  obtain ⟨j, hj, hbjl, hbju⟩ := exists_nat_cell n (goldbachB9BetaGridStep_pos hn) hblow hbup
  have hal : goldbachB9AlphaGridPoint n i < primeLogExponent N rs.1 := by
    simpa only [goldbachB9AlphaGridPoint_eq_step] using hail
  have hau : primeLogExponent N rs.1 ≤ goldbachB9AlphaGridPoint n (i+1) := by
    simpa only [goldbachB9AlphaGridPoint_eq_step] using haiu
  have hbl : goldbachB9BetaGridPoint n j < primeLogExponent N rs.2 := by
    simpa only [goldbachB9BetaGridPoint_eq_step] using hbjl
  have hbu : primeLogExponent N rs.2 ≤ goldbachB9BetaGridPoint n (j+1) := by
    simpa only [goldbachB9BetaGridPoint_eq_step] using hbju
  refine ⟨(⟨i, hi⟩, ⟨j, hj⟩), ?_, ⟨hal, hau, hbl, hbu⟩⟩
  classical
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_univ _, hlow.trans hau, hal.trans hfirst, hsecond.trans hbu, by dsimp; linarith⟩

theorem original_rectangle_subset {N : ℕ} (hN : 2 ≤ N)
    (ρ a₀ a₁ b₀ b₁ : ℝ) :
    (relaxedPairs N ρ).filter (LiuPairInLogRectangle N a₀ a₁ b₀ b₁) ⊆
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
theorem original_kernel_le_grid (n N : ℕ) (hn : 0 < n) (hN : 2 ≤ N)
    {ρ h δ : ℝ} (hρ : 1 < ρ) (hδ : δ ≤ 1/4) (hh : h ≤ 1/20)
    (hw : 1+3*Real.log ρ/Real.log (N : ℝ) ≤ 1+h) :
    relaxedPairKernel N ρ δ ≤ grid (100/1327) n N h δ := by
  classical
  let rect := fun (q : Fin n × Fin n) => LiuPairInLogRectangle N
    (goldbachB9AlphaGridPoint n q.1) (goldbachB9AlphaGridPoint n (q.1+1))
    (goldbachB9BetaGridPoint n q.2) (goldbachB9BetaGridPoint n (q.2+1))
  have hfirst : relaxedPairKernel N ρ δ ≤
      ∑ rs ∈ relaxedPairs N ρ, ∑ q ∈ cells (100/1327) n h,
        if rect q rs then fouvryG9RelaxedIntegralCorner n δ q * (1/((rs.1 : ℝ)*rs.2)) else 0 := by
    apply Finset.sum_le_sum
    intro rs hrs
    obtain ⟨q, hq, hrect⟩ := original_cover n N hn hN hρ hh hw hrs
    have hp := (Finset.mem_filter.mp hrs).2
    have hc := fouvryG9RelaxedIntegral_term_le_corner hn hN hρ hδ q rs hrect hp.1 hp.2.1
    have hsingle := Finset.single_le_sum (s := cells (100/1327) n h)
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
  change (∑ rs ∈ relaxedPairs N ρ, if rect q rs then _ else 0) ≤ _
  rw [← Finset.sum_filter]
  rw [← Finset.mul_sum]
  apply (mul_le_mul_of_nonneg_left _ (fouvryG9RelaxedIntegral_corner_pos hn hδ q).le)
  rw [← sum_primeLogRectanglePairs_eq_primeReciprocalLogRectangle]
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (original_rectangle_subset hN ρ _ _ _ _) (fun _ _ _ => by positivity)


end OriginalU8.Weighted
