import LowComplementRest
import LowComplementLow

namespace LowComplement
open Finset Real Wu2008DoubleSieve MixedSixth Filter
open scoped Classical Topology
noncomputable section

theorem rest_weighted_lower {δ ε : ℝ} (hδ : 0 < δ) (hδhi : δ < 1/100)
    (hε : 0 < ε) (n : ℕ) :
    ∀ᶠ N : ℕ in atTop,
      (truncatedSixthClosureSum false δ n-ε)*truncatedSixthMassScale N ≤
        truncatedSixthLowerNormalizedMain N δ 0 (rest N n δ) := by
  let W := ∑ j ∈ truncatedSixthClosureInner false δ n, truncatedSixthClosureWeight false δ n j
  have hW : 0 ≤ W := sum_nonneg (fun j _ => (truncatedSixthClosure_weight_bounds hδ hδhi false n j).1)
  let e := ε/(W+1)
  have he : 0 < e := div_pos hε (by linarith)
  have herr : e*W ≤ ε := by
    change ε/(W+1)*W ≤ ε
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (show 0 < W+1 by linarith)).mpr
    nlinarith only [hε]
  have hall : ∀ᶠ N : ℕ in atTop, ∀ j ∈ truncatedSixthClosureInner false δ n,
      (truncatedSixthClosureRcoef δ n j-e)*truncatedSixthMassScale N ≤
        ∑ p ∈ coarsePairs N n j, truncatedSixthLowerClassicalTheta N δ p := by
    apply (eventually_all_finset _).mpr
    intro j hj
    have hg := truncatedSixthClosure_inner_geometry hj
    exact truncatedSixthClosure_classical_theta_sharp
      (truncatedSixthClosure_lo_lt_hi n j.1).le (truncatedSixthClosure_lo_lt_hi n j.2).le
      hg.1 hg.2.1 hg.2.2 he
  filter_upwards [hall,eventually_ge_atTop (4:ℕ)] with N hN hN4
  have hs := sum_le_sum (fun j hj => mul_le_mul_of_nonneg_left (hN j hj)
    (truncatedSixthClosure_weight_bounds hδ hδhi false n j).1)
  have heq : (∑ j ∈ truncatedSixthClosureInner false δ n,
      truncatedSixthClosureWeight false δ n j *
        ((truncatedSixthClosureRcoef δ n j-e)*truncatedSixthMassScale N)) =
      (truncatedSixthClosureSum false δ n-e*W)*truncatedSixthMassScale N := by
    unfold truncatedSixthClosureSum W
    simp only [sub_mul,mul_sub,← mul_assoc]
    rw [sum_sub_distrib,← sum_mul,← sum_mul,← sum_mul]
    ring
  rw [heq] at hs
  exact (mul_le_mul_of_nonneg_right (by linarith only [herr])
    (truncatedSixthClosure_scale_nonneg hN4)).trans (hs.trans (classical_grid_le_rest hN4 hδ hδhi))

/-- Fixed arbitrary original grid, actual B; no counting theorem enters. -/
theorem B_grid_lower {δ ε : ℝ} (hδ : 0 < δ) (hδhi : δ < 1/100)
    (hε : 0 < ε) (n : ℕ) :
    ∀ᶠ N : ℕ in atTop,
      (truncatedSixthClosureSum false δ n+truncatedSixthClosureSum true δ n-ε)*
        truncatedSixthMassScale N ≤ B N n δ := by
  filter_upwards [rest_weighted_lower hδ hδhi (half_pos hε) n,
    low_weighted_lower hδ hδhi (half_pos hε) n,eventually_ge_atTop (4:ℕ)] with N hr hl hN
  rw [B_eq_rest_low (by omega) hδ.le]
  linarith only [hr,hl]

/-- Stronger than the old existential sum_sufficient: every sufficiently fine grid works. -/
theorem sum_eventually_sufficient {δ ε : ℝ} (hδ : 0 < δ) (hδhi : δ < 1/100)
    (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, truncatedSixthLowerFdelta δ+truncatedSixthLowerHadmdelta δ-ε <
      truncatedSixthClosureSum false δ n+truncatedSixthClosureSum true δ n := by
  have hlim := ((truncatedSixthClosure_integral_tendsto hδ hδhi false).const_mul 4).add
    ((truncatedSixthClosure_integral_tendsto hδ hδhi true).const_mul 4)
  have hid : 4*(∫ v : ℝ × ℝ, truncatedSixthClosureKernel false δ v) +
      4*(∫ v : ℝ × ℝ, truncatedSixthClosureKernel true δ v) =
      truncatedSixthLowerFdelta δ+truncatedSixthLowerHadmdelta δ := by
    simp only [truncatedSixthClosure_kernel_eq hδ.le,Bool.false_eq_true,if_false,if_true]
    exact (truncatedSixthMass_literal_disjoint_integral hδ hδhi).symm
  rw [hid] at hlim
  filter_upwards [hlim.eventually_const_lt (sub_lt_self _ hε)] with n hn
  apply hn.trans_le
  apply add_le_add
  all_goals
    rw [truncatedSixthClosure_step_integral,mul_sum]
    exact sum_le_sum (fun j hj => truncatedSixthClosure_density_mass_le hδ hδhi hj)

/-- Nested eventual quantifiers keep n independent of N and cofinal in the original grids. -/
theorem B_delta_normalization {δ ε : ℝ} (hδ : 0 < δ) (hδhi : δ < 1/100)
    (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ᶠ N : ℕ in atTop,
      (truncatedSixthLowerFdelta δ+truncatedSixthLowerHadmdelta δ-ε)*
        truncatedSixthMassScale N ≤ B N n δ := by
  filter_upwards [sum_eventually_sufficient hδ hδhi (half_pos hε)] with n hn
  filter_upwards [B_grid_lower hδ hδhi (half_pos hε) n,eventually_ge_atTop (4:ℕ)] with N hN hN4
  exact (mul_le_mul_of_nonneg_right (by linarith only [hn])
    (truncatedSixthClosure_scale_nonneg hN4)).trans hN

end
end LowComplement
