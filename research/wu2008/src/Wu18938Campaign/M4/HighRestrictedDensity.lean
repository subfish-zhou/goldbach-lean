import Wu18938Campaign.M4.HighNonunitDensity

noncomputable section
namespace Wu18938Campaign.M4
open Wu2008DoubleSieve WuPaper.R2GammaHigh HighNonunit Finset Real
open scoped Classical

theorem original_restricted_prime_density {δ ρ ε : ℝ}
    (hd : 0 < δ) (hh : δ ≤ 1 / 100) (hrho : 0 < ρ) (heps : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N → ∀ j : Fin 3, ∀ high : Bool,
      ∀ P : Profile → Prop,
      let G := (originalNonunitFamily j N δ high).restrictLabels P
      G.primeMass ≤ G.mass * (HighO3.densityFactor δ ρ * wuSingularSeries N / log N) +
        ε * truncatedSixthMassScale N := by
  have he : 0 < ε / 4 := by positivity
  obtain ⟨T0, hT04, hR1⟩ := original_nonunit_subfamily_R1_paid hd hh he
  obtain ⟨T1, _, hR2⟩ := original_nonunit_R2_paid hd hh he
  obtain ⟨T2, _, hsmall⟩ := original_nonunit_small_paid hd hh he
  obtain ⟨T3, _, hbad⟩ := original_nonunit_bad_paid hd hh he
  obtain ⟨T4, _, hden⟩ := omega3_source_rosser_density hd
    (show δ < 1 / 2 by linarith) hrho
  refine ⟨max T0 (max T1 (max T2 (max T3 T4))), hT04.trans (le_max_left _ _), ?_⟩
  intro N hN hEven j high P G
  let L := originalNonunitFamily j N δ high
  let Q := (N : ℝ) ^ (1 / 2 - δ)
  let D := ⌊Q⌋₊ + 1
  let Z := sqrt Q
  have hN2 : 2 ≤ N := by omega
  have hg := omega3_source_sieve_geometry hN2 hd (show δ < 1 / 2 by linarith)
  have hf := G.coprimePart.prime_upper_finite hEven D Z
    hg.2.2.2.2.1 hg.2.2.2.2.2.1
  have hr1 := hR1 N (by omega) j high G.coprimePart
    (fun _ hx => (mem_filter.mp (mem_filter.mp hx).1).1) (fun _ => ⟨rfl, rfl⟩) Z
  have hr2 : G.coprimePart.R2 D Z ≤ (ε / 4) * truncatedSixthMassScale N := by
    rw [labelled_coprimePart_eq_restrict]
    exact (G.restrictLabels_R2_le _ D Z).trans
      ((L.restrictLabels_R2_le P D Z).trans (hR2 N (by omega) j high))
  have hs : G.coprimePart.small Z ≤ (ε / 4) * truncatedSixthMassScale N := by
    rw [labelled_coprimePart_eq_restrict]
    exact (G.restrictLabels_small_le _ Z).trans
      ((L.restrictLabels_small_le P Z).trans (hsmall N (by omega) j high))
  have hb : G.noncoprimePart.primeMass ≤ L.noncoprimePart.primeMass := by
    apply sum_le_sum_of_subset_of_nonneg
    · intro x hx
      exact mem_filter.mpr ⟨(mem_filter.mp (mem_filter.mp hx).1).1, (mem_filter.mp hx).2⟩
    · intro x hx _
      exact mul_nonneg (L.weight_nonneg x (mem_filter.mp hx).1) (Nat.cast_nonneg _)
  have hpaid := hb.trans (hbad N (by omega) j high)
  have hx : 0 ≤ G.coprimePart.mass :=
    sum_nonneg (fun x hx => mul_nonneg (G.coprimePart.weight_nonneg x hx) (Nat.cast_nonneg _))
  have hm := mul_le_mul_of_nonneg_left (hden N (by omega) hEven) hx
  change G.coprimePart.mass * ordinaryRosserMainSum true N 1 D Z ≤
    G.coprimePart.mass * (HighO3.densityFactor δ ρ * wuSingularSeries N / log N) at hm
  have hmass : G.coprimePart.mass ≤ G.mass := by
    rw [labelled_coprimePart_eq_restrict]
    exact G.restrictLabels_mass_le _
  have hfactor : 0 ≤ HighO3.densityFactor δ ρ * wuSingularSeries N / log N := by
    have hl : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
    have hseries := wuSingularSeries_pos N (by omega)
    have hgap : 0 < 1 - 2 * δ := by linarith
    unfold HighO3.densityFactor
    positivity
  have hmain := mul_le_mul_of_nonneg_right hmass hfactor
  rw [G.primeMass_coprime_split]
  nlinarith only [hf, hr1, hr2, hs, hpaid, hm, hmain]

end Wu18938Campaign.M4
