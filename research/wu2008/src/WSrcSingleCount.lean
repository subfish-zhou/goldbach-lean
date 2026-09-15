import WSrcSingleSevenPartition

noncomputable section
namespace WuSource.SrcSingle
open Wu2008DoubleSieve Wu08TerminalAlignment Real Set Finset
open scoped Classical Interval BigOperators

def signedSingleCount (N : ℕ) : ℝ :=
  (sieveCount N 1 N ((N : ℝ) ^ truncatedSixthLowerBeta) : ℝ) -
    (SingleUpperCounts.U N (1 / 3) : ℝ) -
    (SingleUpperCounts.U N truncatedSixthLowerSigma : ℝ)

def lowSingleSource (δ : ℝ) : ℝ := secondSource δ + fourthSource δ + fourthSource δ
def singleClassical (δ : ℝ) : ℝ :=
  secondClassical δ - SingleUpperClassicalLimit.Gdelta δ (1 / 3) -
    SingleUpperClassicalLimit.Gdelta δ truncatedSixthLowerSigma

theorem single_classical_zero : singleClassical 0 = secondMain - thirdMain - fourthMain := by
  rw [singleClassical, second_classical_zero]
  rfl

theorem low_source_fixed_count {δ ε : ℝ}
    (hd : 0 < δ) (hh : δ ≤ 1 / 100) (heps : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (singleClassical δ + lowSingleSource δ - ε) * truncatedSixthMassScale N ≤
        signedSingleCount N := by
  obtain ⟨T2, h2, hc2⟩ := second_source_actual_count hd hh (half_pos heps)
  obtain ⟨T34, _, hc34⟩ := TruncatedElevenHIntegralCount.actual_pair_integral_upper hd hh
    (half_pos heps)
  refine ⟨max T2 T34, h2.trans (le_max_left _ _), fun N hN he => ?_⟩
  have h2N := hc2 N (by omega) he
  have h34N := hc34 N (by omega) he
  simp only [SingleUpperHIntegral.gainH34, windowGain_eq_fourthSource] at h34N
  unfold signedSingleCount singleClassical lowSingleSource
  linarith only [h2N, h34N]

theorem full_Hh_one_psi_count {δ ε : ℝ}
    (hd : 0 < δ) (hh : δ ≤ 1 / 100) (heps : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (singleClassical δ + lowSingleSource δ +
        4 * firstFunctionalGainPsi δ HighSix.s HighSix.S * HighSix.primeIntegral δ - ε) *
          truncatedSixthMassScale N ≤ signedSingleCount N := by
  obtain ⟨T2, h2, hc2⟩ := second_source_actual_count hd hh (half_pos heps)
  obtain ⟨T34, _, hc34⟩ := pair_actual_with_full_H hd hh (half_pos heps)
  refine ⟨max T2 T34, h2.trans (le_max_left _ _), fun N hN he => ?_⟩
  have h2N := hc2 N (by omega) he
  have h34N := hc34 N (by omega) he
  unfold signedSingleCount singleClassical lowSingleSource
  linarith only [h2N, h34N]

theorem classical_common_radius {ε : ℝ} (heps : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 / 100 ∧ ∀ δ : ℝ, 0 < δ → δ < r →
      secondMain - thirdMain - fourthMain - ε < singleClassical δ := by
  obtain ⟨a, ha, haNear⟩ := Metric.continuousAt_iff.mp second_classical_continuous
    (ε / 3) (by positivity)
  obtain ⟨b, hb, _, hbNear⟩ := SingleUpperClassicalLimit.Gdelta_close
    (by norm_num [truncatedSixthLowerAlpha] : truncatedSixthLowerAlpha ≤ (1 / 3 : ℝ))
    le_rfl (show 0 < ε / 3 by positivity)
  obtain ⟨c, hc, _, hcNear⟩ := SingleUpperClassicalLimit.Gdelta_close
    (by norm_num [truncatedSixthLowerAlpha, truncatedSixthLowerSigma] :
      truncatedSixthLowerAlpha ≤ truncatedSixthLowerSigma)
    (by norm_num [truncatedSixthLowerAlpha, truncatedSixthLowerSigma] :
      truncatedSixthLowerSigma ≤ (1 / 3 : ℝ)) (show 0 < ε / 3 by positivity)
  let r := min a (min b (min c (1 / 100)))
  have hr : 0 < r := lt_min ha (lt_min hb (lt_min hc (by norm_num)))
  have hra : r ≤ a := min_le_left _ _
  have hrb : r ≤ b := (min_le_right _ _).trans (min_le_left _ _)
  have hrc : r ≤ c := ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_left _ _)
  have hrhi : r ≤ (1 / 100 : ℝ) :=
    ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_right _ _)
  refine ⟨r, hr, hrhi, fun δ hd hdr => ?_⟩
  have h2 := haNear (show dist δ 0 < a by
    simpa only [Real.dist_eq, sub_zero, abs_of_pos hd] using hdr.trans_le hra)
  rw [Real.dist_eq, second_classical_zero, abs_lt] at h2
  have h3 := (abs_lt.mp (hbNear δ hd (hdr.trans_le hrb))).2
  have h4 := (abs_lt.mp (hcNear δ hd (hdr.trans_le hrc))).2
  unfold singleClassical thirdMain fourthMain
  linarith only [h2.1, h3, h4]

theorem low_source_original_classical_count {ρ g ε : ℝ}
    (hρ : 0 < ρ)
    (hgain : ∀ δ : ℝ, 0 < δ → δ ≤ ρ → δ ≤ 1 / 100 → g ≤ lowSingleSource δ)
    (heps : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (secondMain - thirdMain - fourthMain + g - ε) * truncatedSixthMassScale N ≤
        signedSingleCount N := by
  obtain ⟨r, hr, hrhi, hnear⟩ := classical_common_radius (half_pos heps)
  let δ := min r ρ / 2
  have hd : 0 < δ := half_pos (lt_min hr hρ)
  have hdr : δ < r := (half_lt_self (lt_min hr hρ)).trans_le (min_le_left _ _)
  have hdρ : δ ≤ ρ := (half_lt_self (lt_min hr hρ)).le.trans (min_le_right _ _)
  have hdhi := hdr.le.trans hrhi
  obtain ⟨T, hT, hcount⟩ := low_source_fixed_count hd hdhi (half_pos heps)
  refine ⟨T, hT, fun N hN he => ?_⟩
  have hcoef : secondMain - thirdMain - fourthMain + g - ε ≤
      singleClassical δ + lowSingleSource δ - ε / 2 := by
    linarith only [hnear δ hd hdr, hgain δ hd hdρ hdhi]
  exact (mul_le_mul_of_nonneg_right hcoef
    (truncatedSixthClosure_scale_nonneg (hT.trans hN))).trans (hcount N hN he)

theorem original_Hh_input_to_count {ρ h22 ε : ℝ} {Hsmall : ℝ → ℝ} {Hnodes : ℕ → ℝ}
    (hρ : 0 < ρ)
    (hi : IntervalIntegrable (fun t => Hsmall t / t) MeasureTheory.volume (78 / 25) (16 / 5))
    (hnon : ∀ i ∈ Finset.Icc 14 29, 0 ≤ Hnodes i)
    (hsource : ∀ δ : ℝ, 0 < δ → δ ≤ ρ → δ ≤ 1 / 100 →
      h22 ≤ wuImprovementLimit false δ (21 / 5) ∧
      (∀ t ∈ Set.Icc (78 / 25 : ℝ) (16 / 5), Hsmall t ≤ wuImprovementLimit true δ t) ∧
      (∀ i ∈ Finset.Icc 14 29, Hnodes i ≤ wuImprovementLimit true δ (sourceNode i)))
    (heps : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (secondMain - thirdMain - fourthMain +
        8 * secondTransfer h22 Hsmall + 2 * fourthNodeSum Hnodes - ε) *
          truncatedSixthMassScale N ≤ signedSingleCount N := by
  have hgain : ∀ δ : ℝ, 0 < δ → δ ≤ ρ → δ ≤ 1 / 100 →
      8 * secondTransfer h22 Hsmall + 2 * fourthNodeSum Hnodes ≤ lowSingleSource δ := by
    intro δ hd hdρ hdhi
    have hs := hsource δ hd hdρ hdhi
    have h2 := second_transfer_to_source hd hdhi hs.1 hi hs.2.1
    have h4 := fourth_nodes_to_source hd hdhi hnon hs.2.2
    unfold lowSingleSource
    linarith only [h2, h4]
  simpa only [add_assoc] using low_source_original_classical_count hρ hgain heps

def sevenRawSource (N : ℕ) (δ : ℝ) : Fin 7 → ℝ :=
  Fin.addCases (m := 3) (n := 4)
    (fun j => secondFunctionalMotherRHS (Wu04RemainingCore.row j) N δ
      (fun _ : Fin 1 => psiPrimes (j.castAdd 4) N) / 5)
    (fun j => (∑ p ∈ psiPrimes (Fin.natAdd 3 j) N,
      (wuOmega1 N p δ (psiTop (Fin.natAdd 3 j)) -
        wuOmega2 N p δ (psiNode (Fin.natAdd 3 j)) (psiTop (Fin.natAdd 3 j)) +
        wuOmega3 N p δ (psiNode (Fin.natAdd 3 j)) (psiTop (Fin.natAdd 3 j)))) / 2)

theorem seven_raw_source_count {N : ℕ} {δ : ℝ}
    (hN : 2 ≤ N) (hd : 0 < δ) (hh : δ ≤ 1 / 100) (j : Fin 7) :
    psiCount j N ≤ sevenRawSource N δ j := by
  refine Fin.addCases (m := 3) (n := 4) (fun i => ?_) (fun i => ?_) j
  · simp only [sevenRawSource, Fin.addCases_left]
    linarith only [coupled_high_actual_finite i hN hd hh]
  · simp only [sevenRawSource, Fin.addCases_right]
    linarith only [seven_finite_omega_consumer (Fin.natAdd 3 i) hN hd hh]

theorem all_seven_raw_source_to_actual_pair {N : ℕ} {δ : ℝ}
    (hN : 2 ≤ N) (hd : 0 < δ) (hh : δ ≤ 1 / 100) :
    (SingleUpperCounts.U N (1 / 3) : ℝ) +
        (SingleUpperCounts.U N truncatedSixthLowerSigma : ℝ) ≤
      primeBlock N truncatedSixthLowerAlpha
        (1 / 2 - truncatedSixthLowerAlpha * sourceNode 9) +
        (SingleUpperCounts.U N truncatedSixthLowerSigma : ℝ) +
      ∑ j : Fin 7, sevenRawSource N δ j := by
  rw [third_fourth_finite_ledger hN]
  exact add_le_add le_rfl (sum_le_sum (fun j _ => seven_raw_source_count hN hd hh j))

#check @original_Hh_input_to_count
#check @full_Hh_one_psi_count
#check @all_seven_raw_source_to_actual_pair
#print axioms original_Hh_input_to_count
#print axioms full_Hh_one_psi_count
#print axioms all_seven_raw_source_to_actual_pair
end WuSource.SrcSingle
