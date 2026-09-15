import R2OmegaHighLowerLocal

noncomputable section
namespace WuPaper.R2OmegaHigh
open Wu2008DoubleSieve WuSource.SrcSingle HighBoxRecovery HighO2Terminal
open Finset Real Filter
open scoped Classical Topology Interval BigOperators

theorem omega2_lower {δ ε : ℝ} (hd : 0 < δ) (hh : δ ≤ 1 / 100) (heps : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N → ∀ j : Fin 4,
      lowerIntegral j * theta j N δ - ε * truncatedSixthMassScale N ≤
        ∑ p ∈ psiPrimes (index j) N,
          wuOmega2 N p δ (psiNode (index j)) (psiTop (index j)) := by
  let e : ℝ := min 1 (ε / 39360)
  have he : 0 < e := lt_min (by norm_num) (by positivity)
  have he1 : e ≤ 1 := min_le_left _ _
  have heb : 19680 * e ≤ ε / 2 := by
    have := min_le_right (1 : ℝ) (ε / 39360)
    dsimp [e]
    linarith
  obtain ⟨T0, hT04, hl⟩ := actual_atom_lower hd hh he he1
  obtain ⟨T1, _, hq⟩ := selected_fibre_integral he
  obtain ⟨T2, _, ha⟩ := actual_AP_paid hd (half_pos heps)
  obtain ⟨T3, _, hm⟩ := theta_total_mass hd hh
  refine ⟨max T0 (max T1 (max T2 T3)), hT04.trans (le_max_left _ _), ?_⟩
  intro N hN hEven j
  have hN4 : 4 ≤ N := hT04.trans (by omega)
  have hN2 : 2 ≤ N := by omega
  let P : ℕ → Finset ℕ := fun p =>
    primeWindow (p * N) (wuLocalCutoff N δ p (psiTop (index j)))
      (wuLocalCutoff N δ p (psiNode (index j)))
  let F : ℕ → ℕ → ℝ := fun p q =>
    logCoefficient e (ratio N p q δ (psiTop (index j))) /
      (((q : ℝ) - 2) * (1 - log (q : ℝ) / log ((N : ℝ) ^ (1 / 2 - δ) / p)))
  let E : ℕ → ℕ → ℝ := fun p q => apAtom N (convolutionModulusCutoff N δ) (p * q)
  have hg := geometry j
  have hslack := log_integral_slack he.le hg.1 hg.2.2.2.2.1 hg.2.2.1
    hg.2.2.2.1 hg.2.2.2.2.2.1
  have hpoint (p : ℕ) (hp : p ∈ psiPrimes (index j) N) :
      (lowerIntegral j - 41 * e) * HighSix.thetaAtom N δ p - ∑ q ∈ P p, E p q ≤
        wuOmega2 N p δ (psiNode (index j)) (psiTop (index j)) := by
    have hs := outer_support j hN2 hd hh hp
    have hquad := hq N (by omega) p hs.1 hs.2.1 _ hs.2.2.1 (logCoefficient e)
      ((logCoefficient_monotone e).monotoneOn _) (logCoefficient_bounded he.le he1)
      _ _ hg.1 hg.2.2.2.2.1 hg.2.2.1 hg.2.2.2.1
    have hJ : lowerIntegral j - 41 * e ≤ ∑ q ∈ P p, F p q := by
      have h' := (abs_le.mp hquad).1
      change _ ≤ (∑ q ∈ P p, F p q) - _ at h'
      change lowerIntegral j - 40 * e ≤ _ at hslack
      linarith only [h', hslack]
    have hfinite : HighSix.thetaAtom N δ p * (∑ q ∈ P p, F p q) -
        (∑ q ∈ P p, E p q) ≤
        wuOmega2 N p δ (psiNode (index j)) (psiTop (index j)) := by
      rw [mul_sum, ← sum_sub_distrib]
      apply le_trans (sum_le_sum (fun q hqp => hl N (by omega) hEven j p hp q hqp))
      apply sum_le_sum_of_subset_of_nonneg (selected_subset_original N p _ _)
      intro q _ _
      exact Nat.cast_nonneg _
    have hweighted := mul_le_mul_of_nonneg_right hJ (theta_atom_nonneg j hN2 hd hh hp)
    nlinarith only [hweighted, hfinite]
  have hsum := sum_le_sum hpoint
  rw [sum_sub_distrib, ← mul_sum, ← theta_sum] at hsum
  have hAP :
      (∑ p ∈ psiPrimes (index j) N, ∑ q ∈ P p, E p q) ≤
        convolutionAPError N (convolutionModulusCutoff N δ)
          (Fin.cons (apPrimeCover N) (windows j N)) := by
    rw [HighSix.double_AP_expansion]
    change _ ≤ ∑ p ∈ psiPrimes (index j) N, ∑ q ∈ apPrimeCover N, E p q
    apply sum_le_sum
    intro p hp
    apply sum_le_sum_of_subset_of_nonneg
    · intro q hqp
      have hqN := selected_subset_original N p _ _ hqp
      have hinner := inner_geometry j hN2 hd hh hp hqN
      have hqm := mem_primeWindow.mp hqN
      exact mem_primeWindow.mpr ⟨hqm.1, hqm.2.1, hinner.1, by linarith [hinner.2.1]⟩
    · intro q _ _
      exact apAtom_nonneg _ _ _
  have hap := hAP.trans (ha N (by omega) j).2
  have hmass := (hm N (by omega) hEven j).2
  have hfee : 41 * e * theta j N δ ≤ (ε / 2) * truncatedSixthMassScale N := by
    calc
      _ ≤ 41 * e * (480 * truncatedSixthMassScale N) :=
        mul_le_mul_of_nonneg_left hmass (by positivity)
      _ = (19680 * e) * truncatedSixthMassScale N := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right heb (scale_nonneg hN2)
  nlinarith only [hsum, hap, hfee]

#check @WuPaper.R2OmegaHigh.omega2_lower
#print axioms WuPaper.R2OmegaHigh.omega2_lower
end WuPaper.R2OmegaHigh
