import MathlibNt.SieveTheory.LiLiuGoldbachG12BoundaryOutputBudget
import MathlibNt.SieveTheory.LiLiuGoldbachG12SafeGridTerminal
import MathlibNt.SieveTheory.LiLiuGoldbachG12AuthorLowHigh

noncomputable section
open Classical Finset
open scoped BigOperators
open MathlibNt.SieveTheory
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
namespace G12AuthorOutput

/-- A mesh simultaneously legal for the paid boundary and the safe C2 grid. -/
theorem admitted_boundary_mesh (τ : ℝ) (hτ : 0 < τ) :
    ∃ ρ : ℝ, 1 < ρ ∧ ρ ≤ 3/2 ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 2/15 →
      ∃ K : ℕ, 4 ≤ K ∧ ∀ N ≥ K, Even N →
        G12BandOutput.boundaryOutput ρ N ε ≤ τ*G12BandOutput.HN N := by
  let C := G12BandOutput.outputConstant
  have hC : 0 < C := G12BandOutput.outputConstant_pos
  let d : ℝ := min (1/2) (τ/(2*C))
  have hd : 0 < d := lt_min (by norm_num) (by positivity)
  have hdu : d ≤ 1/2 := min_le_left _ _
  have hpay : C*d ≤ τ/2 := by
    calc
      C*d ≤ C*(τ/(2*C)) := mul_le_mul_of_nonneg_left (min_le_right _ _) hC.le
      _ = τ/2 := by field_simp
  refine ⟨1+d/2,by linarith,by linarith,?_⟩
  intro ε he heu
  obtain ⟨K,hK,hb⟩ := G12BandOutput.fixed_grid_boundaryOutput_budget
    (by linarith : 1 < 1+d/2) (by linarith : 1+d/2 < 1+d)
    (by linarith : 1+d ≤ 2) he heu (τ/2) (half_pos hτ)
  refine ⟨K,hK,?_⟩
  intro N hN hEven
  have h := hb N hN hEven
  have hh := mul_le_mul_of_nonneg_right hpay (G12BandOutput.HN_nonneg N)
  change G12BandOutput.boundaryOutput (1+d/2) N ε ≤ C*((1+d)-1)*G12BandOutput.HN N + (τ/2)*G12BandOutput.HN N at h
  linarith only [h,hh]

theorem one_le_authorWeight {N : ℕ} (hN : 4 ≤ N) (r : ℕ) :
    1 ≤ goldbachG12AuthorPrimeWeight N r := by
  have hlr : 0 ≤ Real.log (r : ℝ) := by
    by_cases hr : r = 0
    · simp [hr]
    · exact Real.log_nonneg (by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hr))
  have hln : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  have hu : 0 ≤ min (Real.log (r : ℝ)/Real.log N) (1/10 : ℝ) :=
    le_min (div_nonneg hlr hln) (by norm_num)
  have hv := min_le_right (Real.log (r : ℝ)/Real.log N) (1/10 : ℝ)
  unfold goldbachG12AuthorPrimeWeight goldbachG11AuthorWeight
  apply (le_div_iff₀ (by linarith : 0 < 5*(1-min (Real.log (r : ℝ)/Real.log N) (1/10 : ℝ)))).mpr
  linarith

theorem safe_subset_mother {N : ℕ} (hN : 1 ≤ N) (ρ ε : ℝ) :
    G12SafeGridBudget.safeUnion ρ N ε ⊆ G12FlexibleRectangle.mother N ε := by
  intro p hp
  obtain ⟨k,_,hk⟩ := mem_biUnion.mp hp
  exact (mem_filter.mp (G12FineGrid.safe_subset ρ hN ε k hk)).1

theorem safe_authorMass_le {N : ℕ} (hN : 4 ≤ N) (ρ ε : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    (∑ p ∈ G12SafeGridBudget.safeUnion ρ N ε, goldbachG12NormalizedCoefficient N p.1*
      (goldbachG11AuthorWeight (Real.log p.2/Real.log N)+t)) ≤
      (1+t)*goldbachG12AuthorLowMotherMass N ε := by
  have hsub := safe_subset_mother (by omega : 1 ≤ N) ρ ε
  calc
    _ ≤ ∑ p ∈ G12FlexibleRectangle.mother N ε, goldbachG12NormalizedCoefficient N p.1*
        (goldbachG11AuthorWeight (Real.log p.2/Real.log N)+t) :=
      sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => mul_nonneg
        (goldbachG12NormalizedCoefficient_bounds N p.1).1
        (add_nonneg (goldbachG11AuthorWeight_nonneg _) ht))
    _ ≤ _ := by
      unfold goldbachG12AuthorLowMotherMass
      rw [mul_sum]
      apply sum_le_sum
      intro p _
      have hw := one_le_authorWeight hN p.2
      have hh : goldbachG12AuthorPrimeWeight N p.2+t ≤ (1+t)*goldbachG12AuthorPrimeWeight N p.2 := by nlinarith
      have h := mul_le_mul_of_nonneg_left hh (goldbachG12NormalizedCoefficient_bounds N p.1).1
      dsimp only [goldbachG12AuthorPrimeWeight] at h ⊢
      nlinarith only [h]

theorem highMass_nonneg (N : ℕ) (ε : ℝ) : 0 ≤ G12ClippedWindow.highMass N ε :=
  sum_nonneg (fun m _ => mul_nonneg (goldbachG12NormalizedCoefficient_bounds N m).1 (Nat.cast_nonneg _))

/-- Fixed scalar loss, chosen before all analytic and mesh thresholds. -/
theorem choose_loss (B τ : ℝ) (hτ : 0 < τ) :
    ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧ (1+t)*(B+t)+3*t ≤ B+τ := by
  let C := |B|+5
  have hC : 0 < C := by dsimp [C]; positivity
  let t : ℝ := min 1 (τ/(2*C))
  have ht : 0 < t := lt_min zero_lt_one (by positivity)
  have htu : t ≤ 1 := min_le_left _ _
  have hc : C*t ≤ τ/2 := by
    calc
      C*t ≤ C*(τ/(2*C)) := mul_le_mul_of_nonneg_left (min_le_right _ _) hC.le
      _ = τ/2 := by field_simp
  have hb := mul_le_mul_of_nonneg_left (le_abs_self B) ht.le
  have hs := mul_nonneg ht.le (sub_nonneg.mpr htu)
  refine ⟨t,ht,htu,?_⟩
  dsimp [C] at hc
  nlinarith only [hc,hb,hs,hτ]

end G12AuthorOutput
