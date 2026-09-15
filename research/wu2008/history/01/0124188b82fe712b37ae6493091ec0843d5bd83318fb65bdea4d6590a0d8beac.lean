import R2GammaHighLowerLocal

noncomputable section
namespace WuPaper.R2GammaHigh
open Wu2008DoubleSieve WuSource.SrcSingle HighTheta HighBoxRecovery HighO2Terminal
open Real Finset
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418
open scoped Classical Interval

theorem selected_ap_le {N Q : ℕ} {δ s t : ℝ} (j : Fin 3)
    (hN : 2 ≤ N) (hd : 0 < δ) (hh : δ ≤ 1 / 100)
    (hs : 2 ≤ s) (ht : 3 ≤ t) (ht5 : t ≤ 5) :
    (∑ d ∈ boxConvolutionSupport (windows j N), (convolutionCoeff (windows j N) d : ℝ)*
      ∑ p ∈ primeWindow (d*N) (wuLocalCutoff N δ d t) (wuLocalCutoff N δ d s),
        apAtom N Q (d*p)) ≤
      convolutionAPError N Q (Fin.cons (apPrimeCover N) (windows j N)) := by
  rw [convolutionAPError_eq_support_sum]
  change _ ≤ ∑ m ∈ boxConvolutionSupport (Fin.cons (apPrimeCover N) (windows j N)),
    (convolutionCoeff (Fin.cons (apPrimeCover N) (windows j N)) m : ℝ)*apAtom N Q m
  rw [boxConvolution_sum_cons]
  apply sum_le_sum
  intro d hm
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply sum_le_sum_of_subset_of_nonneg
  · intro p hp
    have hpN := selected_subset_original N d _ _ hp
    rw [support_eq] at hm
    have hg := inserted_geometry j hN hd hh hm hs ht ht5 hpN
    have hp' := mem_primeWindow.mp hpN
    exact mem_primeWindow.mpr ⟨hp'.1, hp'.2.1, hg.1, by linarith [hg.2.1]⟩
  · intro p _ _
    exact apAtom_nonneg _ _ _

theorem prime_lower {δ ε : ℝ}
    (hd : 0 < δ) (hh : δ ≤ 1 / 100) (heps : 0 < ε) (heps1 : ε ≤ 1) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N → ∀ j : Fin 3,
      ∀ s t : ℝ, 2 ≤ s → 3 ≤ t → t ≤ 5 → 2 ≤ t-t/s →
      reboxingPrimeSum true N δ s t (windows j N)
        (fun d p => logCoefficient ε (ratio N d p δ t)) -
        convolutionAPError N (convolutionModulusCutoff N δ)
          (Fin.cons (apPrimeCover N) (windows j N)) ≤
        wuOmega2Sum N δ s t (windows j N) := by
  obtain ⟨T, hT4, hlocal⟩ := atom_lower hd hh heps heps1
  refine ⟨T, hT4, ?_⟩
  intro N hN he j s t hs ht ht5 hc
  let W := windows j N
  let P := fun d => primeWindow (d*N) (wuLocalCutoff N δ d t) (wuLocalCutoff N δ d s)
  let A := fun d p : ℕ => (4*logarithmicIntegral N)*(wuSingularSeries (d*N)/((Nat.totient d : ℝ)*
    log ((N : ℝ)^(1/2-δ)/d)))*(logCoefficient ε (ratio N d p δ t)/
    (((p : ℝ)-2)*(1-log (p : ℝ)/log ((N : ℝ)^(1/2-δ)/d))))
  let E := fun d p : ℕ => apAtom N (convolutionModulusCutoff N δ) (d*p)
  have ha : ∀ d ∈ boxConvolutionSupport W, ∀ p ∈ P d,
      A d p-E d p ≤ (sourceSieveCount N (d*p) (d*N) (wuLocalCutoff N δ d t) : ℝ) := by
    intro d hm
    rw [support_eq] at hm
    exact hlocal N hN he j s t hs ht ht5 hc d hm
  have hsum : (∑ d ∈ boxConvolutionSupport W, (convolutionCoeff W d : ℝ)*
      ∑ p ∈ P d, (A d p-E d p)) ≤ wuOmega2Sum N δ s t W := by
    apply sum_le_sum
    intro d hm
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    apply le_trans (sum_le_sum (ha d hm))
    apply sum_le_sum_of_subset_of_nonneg (selected_subset_original N d _ _)
    intro p _ _
    exact Nat.cast_nonneg _
  have hmain : reboxingPrimeSum true N δ s t W (fun d p => logCoefficient ε (ratio N d p δ t)) =
      ∑ d ∈ boxConvolutionSupport W, (convolutionCoeff W d : ℝ)*∑ p ∈ P d, A d p := by
    unfold reboxingPrimeSum
    simp only [if_true, mul_sum]
    apply sum_congr rfl
    intro d _
    apply sum_congr rfl
    intro p _
    dsimp [A]
    ring
  have hap := selected_ap_le (N := N) (Q := convolutionModulusCutoff N δ) j
    (by omega) hd hh hs ht ht5
  rw [hmain]
  apply le_trans (sub_le_sub_left hap _)
  simpa only [sum_sub_distrib, mul_sub] using hsum

theorem omega_lower {δ ε : ℝ}
    (hd : 0 < δ) (hh : δ ≤ 1 / 100) (heps : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N → ∀ j : Fin 3,
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → 3 ≤ t → t ≤ 5 → 2 ≤ t-t/s →
      (fourthRowClassicalJ s t - ε) * theta j N δ -
        ε * truncatedSixthMassScale N ≤ wuOmega2Sum N δ s t (windows j N) := by
  let e : ℝ := min 1 (ε/41)
  have he : 0 < e := lt_min (by norm_num) (by positivity)
  have he1 : e ≤ 1 := min_le_left _ _
  have heps' : 41*e ≤ ε := by
    have h := min_le_right (1 : ℝ) (ε/41)
    dsimp [e]
    linarith
  obtain ⟨T0, hT04, hcount⟩ := prime_lower hd hh he he1
  obtain ⟨T1, _, hquad⟩ := selected_integral hd hh he
  obtain ⟨T2, _, hAP⟩ := ap_small hd hh heps
  refine ⟨max T0 (max T1 T2), hT04.trans (le_max_left _ _), ?_⟩
  intro N hN hEven j s t hs hst ht ht5 hc
  have hfinite := hcount N (by omega) hEven j s t hs ht ht5 hc
  have hquadrature := hquad N (by omega) j (logCoefficient e)
    ((logCoefficient_monotone e).monotoneOn _) (logCoefficient_bounded he.le he1)
    s t hs hst ht ht5
  have hap := (hAP N (by omega) j).2
  have htheta := theta_nonneg (N := N) j (by omega) hd hh
  have hlocal := mul_le_mul_of_nonneg_right
    (log_integral_slack he.le hs hst ht ht5 hc) htheta
  have hbudget := mul_le_mul_of_nonneg_right heps' htheta
  have hq := (abs_le.mp hquadrature).1
  change ((∫ u in (1-1/s)..(1-1/t), log (t*u-1)/(u*(1-u)))-ε)*
    theta j N δ - ε*truncatedSixthMassScale N ≤ _
  nlinarith only [hfinite, hap, hlocal, hbudget, hq]

theorem gamma_negative_identities (j : Fin 3) (N : ℕ) (δ : ℝ) :
    gamma j N δ 2 = wuOmega2Sum N δ (Wu04RemainingCore.row j).s
      (Wu04RemainingCore.row j).S (windows j N) ∧
    gamma j N δ 3 = wuOmega2Sum N δ (Wu04RemainingCore.row j).kappa2
      (Wu04RemainingCore.row j).S (windows j N) ∧
    gamma j N δ 4 = wuOmega2Sum N δ (Wu04RemainingCore.row j).kappa3
      (Wu04RemainingCore.row j).S (windows j N) := by
  exact ⟨rfl, rfl, rfl⟩

theorem three_negative_lower {δ ε : ℝ}
    (hd : 0 < δ) (hh : δ ≤ 1 / 100) (heps : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N → ∀ j : Fin 3,
      (fourthRowClassicalJ (Wu04RemainingCore.row j).s (Wu04RemainingCore.row j).S - ε) *
        theta j N δ - ε * truncatedSixthMassScale N ≤ gamma j N δ 2 ∧
      (fourthRowClassicalJ (Wu04RemainingCore.row j).kappa2 (Wu04RemainingCore.row j).S - ε) *
        theta j N δ - ε * truncatedSixthMassScale N ≤ gamma j N δ 3 ∧
      (fourthRowClassicalJ (Wu04RemainingCore.row j).kappa3 (Wu04RemainingCore.row j).S - ε) *
        theta j N δ - ε * truncatedSixthMassScale N ≤ gamma j N δ 4 := by
  obtain ⟨T, hT4, homega⟩ := omega_lower hd hh heps
  refine ⟨T, hT4, ?_⟩
  intro N hN he j
  have hg := row_analytic j
  have hl := row_log_domains j
  have he3 := hg.mother.s_le_kappa3
  have h32 := hg.mother.kappa3_lt_kappa2.le
  have h21 := hg.mother.kappa2_lt_kappa1.le
  have h1S := hg.mother.kappa1_le_S
  have hi := gamma_negative_identities j N δ
  rw [hi.1, hi.2.1, hi.2.2]
  exact ⟨homega N hN he j _ _ hg.two_lt_s.le (he3.trans (h32.trans (h21.trans h1S)))
      hg.three_le_S hg.S_le_five hl.2.1,
    homega N hN he j _ _ (hg.two_lt_s.le.trans (he3.trans h32)) (h21.trans h1S)
      hg.three_le_S hg.S_le_five hl.2.2.1,
    homega N hN he j _ _ (hg.two_lt_s.le.trans he3) (h32.trans (h21.trans h1S))
      hg.three_le_S hg.S_le_five hl.2.2.2⟩

def signedClassical (j : Fin 3) : ℝ :=
  4 * wuUpperCoefficient (Wu04RemainingCore.row j).S +
    wuUpperCoefficient (Wu04RemainingCore.row j).kappa1 -
    fourthRowClassicalJ (Wu04RemainingCore.row j).s (Wu04RemainingCore.row j).S -
    fourthRowClassicalJ (Wu04RemainingCore.row j).kappa2 (Wu04RemainingCore.row j).S -
    fourthRowClassicalJ (Wu04RemainingCore.row j).kappa3 (Wu04RemainingCore.row j).S

theorem signed_four_actual_upper {δ ε : ℝ}
    (hd : 0 < δ) (hh : δ ≤ 1 / 100) (heps : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N → ∀ j : Fin 3,
      gamma j N δ 1 - gamma j N δ 2 - gamma j N δ 3 - gamma j N δ 4 ≤
        (signedClassical j + ε) * theta j N δ + ε * truncatedSixthMassScale N := by
  obtain ⟨TU, hTU4, hupper⟩ := gamma_one_upper hd hh (show 0 < ε/4 by positivity)
  obtain ⟨TL, _, hlower⟩ := three_negative_lower hd hh (show 0 < ε/4 by positivity)
  refine ⟨max TU TL, hTU4.trans (le_max_left _ _), ?_⟩
  intro N hN he j
  have hu := hupper N (by omega) he j
  have hl := hlower N (by omega) he j
  unfold signedClassical
  linarith only [hu, hl.1, hl.2.1, hl.2.2]

#check @selected_ap_le
#check @prime_lower
#check @omega_lower
#check @gamma_negative_identities
#check @three_negative_lower
#check @signedClassical
#check @signed_four_actual_upper
#print axioms selected_ap_le
#print axioms prime_lower
#print axioms omega_lower
#print axioms gamma_negative_identities
#print axioms three_negative_lower
#print axioms signedClassical
#print axioms signed_four_actual_upper
end WuPaper.R2GammaHigh
