import MathlibNt.Wu2008DoubleSieve.MotherPairGainKernel
import MathlibNt.Wu2008DoubleSieve.TruncatedSixthMassContinuity

namespace Wu2008DoubleSieve.MotherPair
open Set Real Filter MeasureTheory
open scoped Classical Topology Interval

theorem gain_upperP_le_upperQ {p : SecondFunctionalParameters} (h : AnalyticParameters p)
    (j : Term) : upperP p j ≤ upperQ p j := by
  obtain ⟨_, _, hbc, hce, _, _⟩ := parameter_order h
  cases j <;> simp only [upperP,upperQ] <;> linarith

theorem pairRegion_iff {p : SecondFunctionalParameters} (h : AnalyticParameters p)
    (j : Term) (t u : ℝ) : PairRegion p j t u ↔
    t ∈ Icc (1/p.S) (upperP p j) ∧ u ∈ Icc (max (lowerQ p j) t) (upperQ p j) := by
  obtain ⟨_, hab, hbc, _, _, _⟩ := parameter_order h
  cases j <;> simp only [PairRegion,upperP,lowerQ,upperQ,mem_Icc,max_le_iff]
  all_goals
    constructor
    · rintro ⟨ht,htB,huL,huD⟩
      exact ⟨⟨ht,htB⟩,⟨⟨by linarith,by linarith⟩,huD⟩⟩
    · rintro ⟨⟨ht,htB⟩,⟨⟨hCu,htu⟩,huD⟩⟩
      exact ⟨ht,htB,by linarith,huD⟩

theorem gain_start_bounds {p : SecondFunctionalParameters} (h : AnalyticParameters p)
    (j : Term) {t : ℝ} (ht : t ∈ Icc (1/p.S) (upperP p j)) :
    lowerQ p j ≤ min (upperQ p j) (max (lowerQ p j) t) ∧
    t ≤ min (upperQ p j) (max (lowerQ p j) t) ∧
    min (upperQ p j) (max (lowerQ p j) t) ≤ upperQ p j := by
  have hCD := (gain_endpoint_order h j).2.2.2.2.1
  have htD := ht.2.trans (gain_upperP_le_upperQ h j)
  rw [min_eq_right (max_le hCD htD)]
  exact ⟨le_max_left _ _,le_max_right _ _,max_le hCD htD⟩

theorem pairRegion_iff_slice {p : SecondFunctionalParameters} (h : AnalyticParameters p)
    (j : Term) {t : ℝ} (ht : t ∈ Icc (1/p.S) (upperP p j)) (u : ℝ) :
    PairRegion p j t u ↔ u ∈ Icc (min (upperQ p j) (max (lowerQ p j) t)) (upperQ p j) := by
  rw [pairRegion_iff h j, and_iff_right ht,
    min_eq_right (max_le (gain_endpoint_order h j).2.2.2.2.1
      (ht.2.trans (gain_upperP_le_upperQ h j)))]

theorem gain_slice_support {p : SecondFunctionalParameters} (h : AnalyticParameters p)
    (j : Term) (δ t : ℝ) : Function.support (fun u => gainKernel p j δ (t,u)) ⊆
    Icc (min (upperQ p j) (max (lowerQ p j) t)) (upperQ p j) := by
  intro u hu
  by_cases hv : (t,u) ∈ gainRegion p j
  · have hr := (pairRegion_iff h j t u).mp hv.1
    exact ⟨(min_le_right _ _).trans hr.2.1,hr.2.2⟩
  · exact False.elim (hu (by simp [gainKernel,hv]))

theorem gain_inner_integrable {p : SecondFunctionalParameters} (h : AnalyticParameters p)
    (j : Term) {δ t : ℝ} (hδ : 0 < δ) (hδhi : δ < 1/2)
    (ht : t ∈ Icc (1/p.S) (upperP p j)) :
    IntervalIntegrable (gainLiteral p j δ t) volume
      (min (upperQ p j) (max (lowerQ p j) t)) (upperQ p j) := by
  apply (gain_slice_integrable h j hδ hδhi t).intervalIntegrable.congr
  intro u hu
  apply gain_kernel_eq_literal h j
  apply (pairRegion_iff_slice h j ht u).mpr
  simpa only [uIcc_of_le (gain_start_bounds h j ht).2.2] using uIoc_subset_uIcc hu

theorem gain_inner_eq {p : SecondFunctionalParameters} (h : AnalyticParameters p)
    (j : Term) {δ t : ℝ} (ht : t ∈ Icc (1/p.S) (upperP p j)) :
    (∫ u, gainKernel p j δ (t,u)) =
    ∫ u in (min (upperQ p j) (max (lowerQ p j) t))..(upperQ p j), gainLiteral p j δ t u := by
  rw [truncatedSixthMass_integral_eq_interval (min_le_left _ _)
    (gain_slice_support h j δ t)]
  apply intervalIntegral.integral_congr
  intro u hu
  apply gain_kernel_eq_literal h j
  apply (pairRegion_iff_slice h j ht u).mpr
  simpa only [uIcc_of_le (gain_start_bounds h j ht).2.2] using hu

theorem gain_outer_integrable {p : SecondFunctionalParameters} (h : AnalyticParameters p)
    (j : Term) {δ : ℝ} (hδ : 0 < δ) (hδhi : δ < 1/2) :
    IntervalIntegrable (fun t => ∫ u in (min (upperQ p j) (max (lowerQ p j) t))..(upperQ p j),
      gainLiteral p j δ t u) volume (1/p.S) (upperP p j) := by
  apply (gain_kernel_integrable h j hδ hδhi).integral_prod_left.intervalIntegrable.congr
  intro t ht
  exact gain_inner_eq h j
    (by simpa only [uIcc_of_le (gain_endpoint_order h j).2.1] using uIoc_subset_uIcc ht)

theorem gain_integral_eq {p : SecondFunctionalParameters} (h : AnalyticParameters p)
    (j : Term) {δ : ℝ} (hδ : 0 < δ) (hδhi : δ < 1/2) :
    gainIntegral p j δ = ∫ v : ℝ × ℝ, gainKernel p j δ v := by
  have hs : Function.support (fun t => ∫ u, gainKernel p j δ (t,u)) ⊆
      Icc (1/p.S) (upperP p j) := by
    intro t ht
    by_contra hn
    apply ht
    change (∫ u, gainKernel p j δ (t,u)) = 0
    have he : (fun u => gainKernel p j δ (t,u)) = 0 := by
      funext u
      have hh : (t,u) ∉ gainRegion p j := fun hv => hn ((pairRegion_iff h j t u).mp hv.1).1
      simp [gainKernel,hh]
    rw [he]
    simp
  rw [show (∫ v : ℝ × ℝ, gainKernel p j δ v) = ∫ t, ∫ u, gainKernel p j δ (t,u) from
    integral_prod _ (gain_kernel_integrable h j hδ hδhi),
    truncatedSixthMass_integral_eq_interval (gain_endpoint_order h j).2.1 hs]
  symm
  apply intervalIntegral.integral_congr
  intro t ht
  exact gain_inner_eq h j (by simpa only [uIcc_of_le (gain_endpoint_order h j).2.1] using ht)

theorem gain_integral_literal_prod {p : SecondFunctionalParameters} (h : AnalyticParameters p)
    (j : Term) {δ : ℝ} (hδ : 0 < δ) (hδhi : δ < 1/2) :
    (∫ v : ℝ × ℝ, gainKernel p j δ v) =
    ∫ t in (1/p.S)..(upperP p j),
      ∫ u in (min (upperQ p j) (max (lowerQ p j) t))..(upperQ p j),
        if gamma5GainLegal t u then
          wuImprovementLimit true δ (Hratio p j t u)/(t*u*(1-t-u)) else 0 :=
  (gain_integral_eq h j hδ hδhi).symm

end Wu2008DoubleSieve.MotherPair
