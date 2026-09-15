import R2GammaHighPairUpper

noncomputable section
namespace WuPaper.R2GammaHigh
open Wu2008DoubleSieve WuSource.SrcSingle Real Finset MotherPair
open scoped Classical

theorem pair_row_upper (j : Fin 3) {δ ε : ℝ}
    (hd : 0 < δ) (hh : δ ≤ 1/100) (heps : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N → ∀ i : Term,
      gamma j N δ i.index ≤
        (classicalIntegral (Wu04RemainingCore.row j) i+ε)*theta j N δ +
          ε*truncatedSixthMassScale N := by
  let p := Wu04RemainingCore.row j
  have hp := row_analytic j
  let K : ℝ := 16*(1/(1-2*(1/p.kappa3)))
  have hg : 0 < 1-2*(1/p.kappa3) := by linarith [(classical_cap hp).cap_lt_half]
  have hK : 0 < K := by dsimp [K]; positivity
  let η : ℝ := min 1 (ε/(6*(K+1)))
  have heta : 0 < η := lt_min (by norm_num) (by positivity)
  have heta1 : η ≤ 1 := min_le_left _ _
  have hpay : 6*η*(K+1) ≤ ε := by
    have h := (le_div_iff₀ (show 0 < 6*(K+1) by positivity)).mp
      (min_le_right 1 (ε/(6*(K+1))))
    dsimp [η]
    nlinarith
  obtain ⟨TC, hTC, hcount⟩ := pair_mask_upper (classical_cap hp) hd hh heta heps
  obtain ⟨TM, _, hmass⟩ := term_mass hd hh (show 0 < ε/16 by positivity)
  refine ⟨max TC TM, hTC.trans (le_max_left _ _), ?_⟩
  intro N hN he i
  have hN4 : 4 ≤ N := by omega
  have hlabels := term_labels_subset_cap j i (by omega : 2 ≤ N) hd hh
  have hc := (termCount_le_fixedCount p i N δ (1/p.kappa3) (windows j N) _ hlabels).trans
    (hcount N (by omega) he j _ hlabels)
  have hm := (abs_le.mp (hmass N (by omega) j i)).2
  have htheta := theta_nonneg j hN4 hd hh
  have hI := classicalIntegral_bounds hp i
  have hb := classical_slack_budget heta heta1 heps hI.1 hI.2 hpay
  have hb' : (1+η)^2*(classicalIntegral p i+ε/16) ≤ classicalIntegral p i+ε := by
    linarith
  rw [term_count_original j i (by omega) hd hh] at hc
  apply hc.trans
  calc
    _ ≤ (1+η)^2*((classicalIntegral p i+ε/16)*theta j N δ) +
        ε*truncatedSixthMassScale N := by
      apply add_le_add _ le_rfl
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      change _ ≤ _ at hm
      dsimp [p]
      linarith only [hm]
    _ = ((1+η)^2*(classicalIntegral p i+ε/16))*theta j N δ +
        ε*truncatedSixthMassScale N := by ring
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_right hb' htheta) le_rfl

theorem gamma_pairs_upper {δ ε : ℝ}
    (hd : 0 < δ) (hh : δ ≤ 1/100) (heps : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N → ∀ j : Fin 3, ∀ i : Term,
      gamma j N δ i.index ≤
        (classicalIntegral (Wu04RemainingCore.row j) i+ε)*theta j N δ +
          ε*truncatedSixthMassScale N := by
  choose T hT h using (fun j => pair_row_upper j hd hh heps)
  refine ⟨4+univ.sup T, by omega, ?_⟩
  intro N hN he j i
  apply h j N _ he i
  have := le_sup (f := T) (mem_univ j)
  omega

def signedEight (j : Fin 3) (N : ℕ) (δ : ℝ) : ℝ :=
  gamma j N δ 1-gamma j N δ 2-gamma j N δ 3-gamma j N δ 4+
    gamma j N δ 5+gamma j N δ 6+gamma j N δ 7+gamma j N δ 8

def classicalEight (j : Fin 3) : ℝ :=
  signedClassical j+SecondFunctionalCoupledFeedback.classical (Wu04RemainingCore.row j)

theorem signed_eight_actual_upper {δ ε : ℝ}
    (hd : 0 < δ) (hh : δ ≤ 1/100) (heps : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N → ∀ j : Fin 3,
      signedEight j N δ ≤ (classicalEight j+ε)*theta j N δ + ε*truncatedSixthMassScale N := by
  obtain ⟨T1, hT14, hneg⟩ := signed_four_actual_upper hd hh (show 0 < ε/5 by positivity)
  obtain ⟨T2, _, hpos⟩ := gamma_pairs_upper hd hh (show 0 < ε/5 by positivity)
  refine ⟨max T1 T2, hT14.trans (le_max_left _ _), ?_⟩
  intro N hN he j
  have h0 := hneg N (by omega) he j
  have h5 := hpos N (by omega) he j .gammaFive
  have h6 := hpos N (by omega) he j .gammaSix
  have h7 := hpos N (by omega) he j .gammaSeven
  have h8 := hpos N (by omega) he j .gammaEight
  simp only [Term.index] at h5 h6 h7 h8
  unfold signedEight classicalEight SecondFunctionalCoupledFeedback.classical
  linarith only [h0, h5, h6, h7, h8]

def classicalGain (j : Fin 3) : ℝ :=
  -(2/5)*fourthRowClassicalL (Wu04RemainingCore.row j).S -
    (2/5)*fourthRowClassicalL (Wu04RemainingCore.row j).kappa1 -
    (1/5)*fourthRowClassicalL (Wu04RemainingCore.row j).kappa2 +
    (1/5)*fourthRowClassicalJ (Wu04RemainingCore.row j).s (Wu04RemainingCore.row j).S +
    (1/5)*fourthRowClassicalJ (Wu04RemainingCore.row j).kappa3 (Wu04RemainingCore.row j).kappa1

theorem classical_coefficient_identity (j : Fin 3) :
    classicalEight j = 5*(wuUpperCoefficient (Wu04RemainingCore.row j).s-classicalGain j) := by
  have hp := row_analytic j
  have he := hp.mother.s_le_kappa3
  have hc := hp.mother.kappa3_lt_kappa2.le
  have hb := hp.mother.kappa2_lt_kappa1.le
  have hS := hp.mother.kappa1_le_S
  have hid := SecondFunctionalClassicalAlgebra.coefficient_eq hp.two_lt_s.le hp.s_le_three
    (row_log_domains j).1 hS hp.S_le_five (hp.two_lt_s.trans_le (he.trans hc))
    (hb.trans hS) (hp.two_lt_s.trans_le he) (hc.trans hb)
  have ht := SecondFunctionalSignedCore.classical_eq_triangles hp
  unfold classicalEight signedClassical classicalGain
  rw [ht]
  linarith only [hid]

def unpaidThirteen (j : Fin 3) (N : ℕ) (δ : ℝ) : ℝ :=
  ∑ i ∈ Icc 9 21, gamma j N δ i

theorem mother_split_eight_thirteen (j : Fin 3) (N : ℕ) (δ : ℝ) :
    secondFunctionalMotherRHS (Wu04RemainingCore.row j) N δ (windows j N) =
      signedEight j N δ+unpaidThirteen j N δ := by
  have hs : (∑ i ∈ Icc 5 21, gamma j N δ i) =
      gamma j N δ 5+gamma j N δ 6+gamma j N δ 7+gamma j N δ 8+unpaidThirteen j N δ := by
    rw [sum_Icc_eq_sum_range]
    norm_num [sum_range_succ, unpaidThirteen, sum_Icc_eq_sum_range]
    ring
  have h1 := gamma_one_identity j N δ
  have hneg := gamma_negative_identities j N δ
  unfold secondFunctionalMotherRHS
  change _+∑ i ∈ Icc 5 21, gamma j N δ i = _
  rw [hs]
  unfold signedEight
  rw [h1, hneg.1, hneg.2.1, hneg.2.2]
  ring

theorem actual_count_partial_eight {δ ε : ℝ}
    (hd : 0 < δ) (hh : δ ≤ 1/100) (heps : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N → ∀ j : Fin 3,
      5*psiCount (j.castAdd 4) N ≤
        (classicalEight j+ε)*theta j N δ + ε*truncatedSixthMassScale N+unpaidThirteen j N δ := by
  obtain ⟨T, hT4, h⟩ := signed_eight_actual_upper hd hh heps
  refine ⟨T, hT4, ?_⟩
  intro N hN he j
  have hf := coupled_high_actual_finite j (by omega : 2 ≤ N) hd hh
  change _ ≤ secondFunctionalMotherRHS _ N δ (windows j N) at hf
  rw [mother_split_eight_thirteen] at hf
  exact hf.trans (add_le_add (h N hN he j) le_rfl)

#check @pair_row_upper
#check @gamma_pairs_upper
#check @signedEight
#check @classicalEight
#check @signed_eight_actual_upper
#check @classicalGain
#check @classical_coefficient_identity
#check @unpaidThirteen
#check @mother_split_eight_thirteen
#check @actual_count_partial_eight
#print axioms pair_row_upper
#print axioms gamma_pairs_upper
#print axioms signedEight
#print axioms classicalEight
#print axioms signed_eight_actual_upper
#print axioms classicalGain
#print axioms classical_coefficient_identity
#print axioms unpaidThirteen
#print axioms mother_split_eight_thirteen
#print axioms actual_count_partial_eight
end WuPaper.R2GammaHigh
