import Wu18938Campaign.M4.HighNonunitErrors
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalLabelledRestriction
import MathlibNt.Wu2008DoubleSieve.Omega3SourceDensity
import HighO3Actual

noncomputable section
namespace Wu18938Campaign.M4
open Wu2008DoubleSieve WuPaper.R2GammaHigh HighNonunit Finset Real
open scoped Classical

theorem labelled_coprimePart_eq_restrict {α : Type*} {N : ℕ}
    (L : LabelledPhysical.Family α N) :
    L.coprimePart = L.restrictLabels (fun x => (L.cofactor x).Coprime N) := by
  unfold LabelledPhysical.Family.coprimePart LabelledPhysical.Family.restrictLabels
  congr 1
  ext c
  simp

theorem original_nonunit_prime_density {δ ρ ε : ℝ}
    (hd : 0 < δ) (hh : δ ≤ 1 / 100) (hrho : 0 < ρ) (heps : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N → ∀ j : Fin 3, ∀ high : Bool,
      let L := originalNonunitFamily j N δ high
      L.primeMass ≤ L.coprimePart.mass *
        (HighO3.densityFactor δ ρ * wuSingularSeries N / log N) +
          ε * truncatedSixthMassScale N := by
  have he : 0 < ε / 4 := by positivity
  obtain ⟨T0, hT04, hR1⟩ := original_nonunit_R1_paid hd hh he
  obtain ⟨T1, _, hR2⟩ := original_nonunit_R2_paid hd hh he
  obtain ⟨T2, _, hsmall⟩ := original_nonunit_small_paid hd hh he
  obtain ⟨T3, _, hbad⟩ := original_nonunit_bad_paid hd hh he
  obtain ⟨T4, _, hden⟩ := omega3_source_rosser_density hd
    (show δ < 1 / 2 by linarith) hrho
  refine ⟨max T0 (max T1 (max T2 (max T3 T4))), hT04.trans (le_max_left _ _), ?_⟩
  intro N hN hEven j high L
  let Q := (N : ℝ) ^ (1 / 2 - δ)
  let D := ⌊Q⌋₊ + 1
  let Z := sqrt Q
  have hg := omega3_source_sieve_geometry (by omega : 2 ≤ N) hd
    (show δ < 1 / 2 by linarith)
  have hf := L.coprimePart.prime_upper_finite hEven D Z
    hg.2.2.2.2.1 hg.2.2.2.2.2.1
  have hr1 := hR1 N (by omega) j high true Z
  change L.coprimePart.R1 D Z ≤ (ε / 4) * truncatedSixthMassScale N at hr1
  have hG := labelled_coprimePart_eq_restrict L
  have hr2 : L.coprimePart.R2 D Z ≤ (ε / 4) * truncatedSixthMassScale N := by
    rw [hG]
    exact (L.restrictLabels_R2_le (fun x => (L.cofactor x).Coprime N) D Z).trans
      (hR2 N (by omega) j high)
  have hs : L.coprimePart.small Z ≤ (ε / 4) * truncatedSixthMassScale N := by
    rw [hG]
    exact (L.restrictLabels_small_le (fun x => (L.cofactor x).Coprime N) Z).trans
      (hsmall N (by omega) j high)
  have hb := hbad N (by omega) j high
  have hx : 0 ≤ L.coprimePart.mass :=
    sum_nonneg (fun x hx => mul_nonneg (L.coprimePart.weight_nonneg x hx) (Nat.cast_nonneg _))
  have hm := mul_le_mul_of_nonneg_left (hden N (by omega) hEven) hx
  change L.coprimePart.mass * ordinaryRosserMainSum true N 1 D Z ≤
    L.coprimePart.mass * (HighO3.densityFactor δ ρ * wuSingularSeries N / log N) at hm
  rw [L.primeMass_coprime_split]
  nlinarith only [hf, hr1, hr2, hs, hb, hm]

theorem original_high_gamma_le_unit_primeMass {N : ℕ} {δ : ℝ}
    (j : Fin 3) (hN : 4 ≤ N) (hEven : Even N) (high : Bool) :
    gamma j N δ (if high then 21 else 20) ≤
      actualUnit N δ (Wu04RemainingCore.row j) (windows j N) high +
        (originalNonunitFamily j N δ high).primeMass := by
  have hpos : ∀ d ∈ boxConvolutionSupport (windows j N), 0 < d := by
    intro d hd
    have hdm : d ∈ WuSource.SrcSingle.psiPrimes (j.castAdd 4) N := by
      simpa only [support_eq] using hd
    exact (mem_primeWindow.mp hdm).1.pos
  have hdict := (actualFamily_dictionary N δ (Wu04RemainingCore.row j)
    (windows j N) high hpos).1
  have hfinite : actualSource N δ (Wu04RemainingCore.row j) (windows j N) high ≤
      (originalNonunitFamily j N δ high).primeMass := by
    rw [show (originalNonunitFamily j N δ high).primeMass =
      actualEnvelope N δ (Wu04RemainingCore.row j) (windows j N) high from hdict]
    exact source_le_envelope hpos (by omega) hEven (word_length high) (word_last high)
  unfold gamma
  rw [← actual_partition]
  exact add_le_add le_rfl hfinite

theorem original_high_gamma_density {δ ρ ε : ℝ}
    (hd : 0 < δ) (hh : δ ≤ 1 / 100) (hrho : 0 < ρ) (heps : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N → ∀ j : Fin 3, ∀ high : Bool,
      gamma j N δ (if high then 21 else 20) ≤
        actualUnit N δ (Wu04RemainingCore.row j) (windows j N) high +
          (originalNonunitFamily j N δ high).coprimePart.mass *
            (HighO3.densityFactor δ ρ * wuSingularSeries N / log N) +
          ε * truncatedSixthMassScale N := by
  obtain ⟨T, hT, hb⟩ := original_nonunit_prime_density hd hh hrho heps
  refine ⟨T, hT, ?_⟩
  intro N hN hEven j high
  have hf := original_high_gamma_le_unit_primeMass (δ := δ) j (by omega) hEven high
  have hp := hb N hN hEven j high
  linarith only [hf, hp]

end Wu18938Campaign.M4
