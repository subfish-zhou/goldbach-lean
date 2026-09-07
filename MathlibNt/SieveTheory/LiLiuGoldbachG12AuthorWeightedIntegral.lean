import MathlibNt.SieveTheory.LiLiuGoldbachG12AuthorWeightedSource
import MathlibNt.SieveTheory.LiLiuGoldbachG12PrimeKernelIntegralBound
import MathlibNt.SieveTheory.LiLiuGoldbachG12BuchstabMajorant

open scoped BigOperators Topology
open Classical Finset Filter LiLiuPrereqBuchstab
noncomputable section
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- Uniform weighted rough-mother bound; no output prime test is imposed. -/
theorem goldbachG12WeightedRough_le_kernel (h : ℝ → ℝ)
    (hh : ∀ x, 0 ≤ h x) (η : ℝ) (hη : 0 < η) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N ≥ N₀,
      Real.log (N : ℝ) / N * goldbachG12WeightedRough N
        (fun r => h (Real.log (r : ℝ) / Real.log (N : ℝ))) ≤
          ((564383/1000000 : ℝ)+η) * goldbachG12PrimeKernel h N := by
  obtain ⟨K,hK,hb⟩ := goldbachG12_rough_upper_buchstab η hη
  refine ⟨K,hK,?_⟩
  intro N hN
  have hN4 : 4 ≤ N := hK.trans hN
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  unfold goldbachG12WeightedRough goldbachG12PrimeKernel
  rw [mul_sum,mul_sum]
  apply sum_le_sum
  intro v hv
  have hg := goldbachG12PrimeKernel_logGeometry hN4 hv
  have hbv := hb N hN v hv
  have hu : 3 ≤ Real.log ((N : ℝ)/goldbachG11LabelProd v) / Real.log (v.2.2.2 : ℝ) := by
    rcases v with ⟨t,s,r,q⟩
    have hm : t ∈ goldbachClosedPrimes N ((N : ℝ)^(4/33 : ℝ)) ((N : ℝ)^(3/11 : ℝ)) ∧
        s ∈ goldbachClosedPrimes N ((N : ℝ)^(4/53 : ℝ)) ((N : ℝ)^(4/33 : ℝ)) ∧
        r ∈ goldbachClosedPrimes N ((N : ℝ)^(4/53 : ℝ)) (s : ℝ) ∧
        q ∈ goldbachClosedPrimes N (r : ℝ) (s : ℝ) := by
      simpa only [goldbachG12Labels, mem_sigma] using hv
    exact (goldbachG12_canonical_logQuotient_bounds (by omega) hm.1 hm.2.1 hm.2.2.1 hm.2.2.2).1
  have hw := LiLiuGoldbachG12BuchstabMajorant.buchstab_le_564383 hu
  have hmass : (roughCount ((N : ℝ)/goldbachG11LabelProd v) v.2.2.2 : ℝ) ≤
      ((564383/1000000 : ℝ)+η) * ((N : ℝ)/goldbachG11LabelProd v) /
        Real.log (v.2.2.2 : ℝ) := by
    apply hbv.trans
    unfold goldbachG11BuchstabMass
    calc
      _ ≤ ((N : ℝ)/goldbachG11LabelProd v) * (564383/1000000 : ℝ) /
          Real.log (v.2.2.2 : ℝ) + η*((N : ℝ)/goldbachG11LabelProd v) /
            Real.log (v.2.2.2 : ℝ) := by gcongr
      _ = _ := by ring
  calc
    _ ≤ Real.log (N : ℝ)/N * (h (Real.log (v.2.2.1 : ℝ)/Real.log (N : ℝ)) *
        (((564383/1000000 : ℝ)+η)*((N : ℝ)/goldbachG11LabelProd v)/
          Real.log (v.2.2.2 : ℝ))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmass (hh _))
        (div_nonneg hlog hNp.le)
    _ = (((564383/1000000 : ℝ)+η) *
        (h (Real.log (v.2.2.1 : ℝ)/Real.log (N : ℝ))*Real.log (N : ℝ)/
          ((goldbachG11LabelProd v : ℝ)*Real.log (v.2.2.2 : ℝ)))) * ((N : ℝ)/N) := by ring
    _ = _ := by rw [div_self hNp.ne',mul_one]

/-- Consumes the proved continuous author-weight quadrature on the ORIGINAL cross. -/
theorem goldbachG12AuthorRough_integral_budget (δ : ℝ) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N ≥ N₀,
      Real.log (N : ℝ)/N * goldbachG12WeightedRough N (goldbachG12AuthorPrimeWeight N) ≤
        (564383/1000000 : ℝ)*goldbachG12PrimeIntegral goldbachG11AuthorWeight + δ := by
  let W : ℝ := 564383/1000000
  let I := goldbachG12PrimeIntegral goldbachG11AuthorWeight
  have hc : ContinuousAt (fun t : ℝ => (W+t)*(I+t)) 0 := by fun_prop
  obtain ⟨r,hr,hs⟩ := Metric.continuousAt_iff.mp hc δ hδ
  let η := r/2
  have hη : 0 < η := half_pos hr
  have he : (W+η)*(I+η) ≤ W*I+δ := by
    have hdist : dist η 0 < r := by
      simp only [Real.dist_eq,sub_zero,abs_of_pos hη]
      dsimp [η]
      linarith
    have hh := hs hdist
    rw [Real.dist_eq] at hh
    have := (abs_lt.mp hh).2
    nlinarith only [this]
  obtain ⟨N₁,hN₁,hb⟩ := goldbachG12WeightedRough_le_kernel goldbachG11AuthorWeight
    goldbachG11AuthorWeight_nonneg η hη
  obtain ⟨N₂,_,hk⟩ := goldbachG12PrimeKernel_author_le_integral_eventually η hη
  refine ⟨max N₁ N₂,hN₁.trans (le_max_left _ _),?_⟩
  intro N hN
  exact (hb N ((le_max_left _ _).trans hN)).trans
    ((mul_le_mul_of_nonneg_left (hk N ((le_max_right _ _).trans hN))
      (show 0 ≤ W+η by dsimp [W]; positivity)).trans he)

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
