import MathlibNt.Wu2008DoubleSieve.MotherPairGainApproximation

namespace Wu2008DoubleSieve.MotherPair
open Finset Set Real Filter MeasureTheory
open scoped Classical Topology

theorem gain_rectangle_H {p : SecondFunctionalParameters} {j : Term}
    (δ : ℝ) (r : GainRectangle p j) :
    gamma5GainH δ r.sample = wuImprovementLimit true δ r.sample :=
  congrArg (wuImprovementLimit true δ) (gamma5Gain_clip_eq ⟨r.sample_lower.le,r.sample_upper.le⟩)

theorem grid_summand_integrable {p : SecondFunctionalParameters} (h : AnalyticParameters p)
    (j : Term) (δ : ℝ) (n : ℕ) (i : ℕ × ℕ) :
    Integrable ((truncatedSixthClosureCell n i).indicator
      (fun v => gamma5GainH δ (gridSample p j n i) * gainSmooth p v)) := by
  apply IntegrableOn.integrable_indicator _ (truncatedSixthClosure_cell_measurable n i)
  exact (((continuous_const.mul (gain_smooth_continuous h)).continuousOn.integrableOn_compact
    (isCompact_Icc.prod isCompact_Icc)).mono_set
      (Set.prod_mono Ico_subset_Icc_self Ico_subset_Icc_self))

theorem grid_integral_sum {p : SecondFunctionalParameters} (h : AnalyticParameters p)
    (j : Term) (δ : ℝ) (n : ℕ) :
    (∫ v : ℝ × ℝ, gridApprox p j δ n v) =
      ∑ r ∈ gridFamily p j n, wuImprovementLimit true δ r.sample *
        rectIntegral r.A r.B r.C r.D := by
  unfold gridFamily
  rw [Finset.sum_image (grid_rectangle_injective p j n).injOn]
  unfold gridApprox
  rw [integral_finsetSum _ (fun i _ => grid_summand_integrable h j δ n i)]
  rw [← Finset.sum_attach]
  change (∑ i : {i // i ∈ gridInner p j n}, _) = _
  apply sum_congr rfl
  intro i _
  let r := gridRectangle p j n i
  have heq : (truncatedSixthClosureCell n i.val).indicator
      (fun v => gamma5GainH δ (gridSample p j n i.val) * gainSmooth p v) =
      fun v => gamma5GainH δ r.sample *
        (Ico r.A r.B ×ˢ Ico r.C r.D).indicator (gainSmooth p) v := by
    funext v
    change (truncatedSixthClosureCell n i.val).indicator
      (fun v => gamma5GainH δ r.sample * gainSmooth p v) v =
        gamma5GainH δ r.sample * (truncatedSixthClosureCell n i.val).indicator (gainSmooth p) v
    by_cases hv : v ∈ truncatedSixthClosureCell n i.val
    · simp only [Set.indicator_of_mem hv]
    · simp only [Set.indicator_of_notMem hv,mul_zero]
  rw [heq,integral_const_mul,gain_smooth_indicator h r,gain_rectangle_H]

/-- An explicit mesh level supplies arbitrarily sufficient actual H-weighted mass. -/
theorem sufficient_grid {p : SecondFunctionalParameters} (h : AnalyticParameters p)
    (j : Term) {δ ε : ℝ} (hδ : 0 < δ) (hδhi : δ < 1/2) (hε : 0 < ε) :
    ∃ n : ℕ, gainIntegral p j δ - ε <
      ∑ r ∈ gridFamily p j n, wuImprovementLimit true δ r.sample *
        rectIntegral r.A r.B r.C r.D := by
  obtain ⟨n,hn⟩ := ((grid_integral_tendsto h j hδ hδhi).eventually
    (lt_mem_nhds (sub_lt_self _ hε))).exists
  exact ⟨n,by rwa [grid_integral_sum h j δ n] at hn⟩

/-- A genuine finite, geometrically disjoint, strictly internal sufficient family.
No full-H domain assumption, positivity of the area, or H continuity is imposed. -/
theorem sufficient_family {p : SecondFunctionalParameters} (h : AnalyticParameters p)
    (j : Term) {δ ε : ℝ} (hδ : 0 < δ) (hδhi : δ < 1/2) (hε : 0 < ε) :
    ∃ F : Finset (GainRectangle p j),
      (↑F : Set (GainRectangle p j)).Pairwise (fun r s =>
        Disjoint (Ico r.A r.B ×ˢ Ico r.C r.D) (Ico s.A s.B ×ˢ Ico s.C s.D)) ∧
      gainIntegral p j δ - ε < ∑ r ∈ F,
        wuImprovementLimit true δ r.sample * rectIntegral r.A r.B r.C r.D := by
  obtain ⟨n,hn⟩ := sufficient_grid h j hδ hδhi hε
  exact ⟨gridFamily p j n,grid_family_pairwise p j n,hn⟩

end Wu2008DoubleSieve.MotherPair
