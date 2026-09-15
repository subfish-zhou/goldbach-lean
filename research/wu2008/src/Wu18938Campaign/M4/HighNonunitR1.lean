import Wu18938Campaign.M4.HighNonunitMultiplicity
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalLabelledCoprimeOutputFinite
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalLabelledR1Layers

noncomputable section
namespace Wu18938Campaign.M4
open Wu2008DoubleSieve WuPaper.R2GammaHigh HighNonunit Finset Real Filter
open scoped Classical Topology

theorem original_nonunit_R1_log_saving {δ A : ℝ}
    (hd : 0 < δ) (hh : δ ≤ 1 / 100) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ j : Fin 3, ∀ high good : Bool, ∀ Z : ℝ,
      let L := originalNonunitFamily j N δ high
      (if good then L.coprimePart else L).R1 (⌊(N : ℝ) ^ (1 / 2 - δ)⌋₊ + 1) Z ≤
        C * N / log (N : ℝ) ^ A := by
  obtain ⟨C, hC, T, hT, hb⟩ := LabelledPhysical.Family.R1_log_saving A (1 / 40) (40 ^ 6)
    hA (by norm_num) (by positivity) hd
  refine ⟨C, hC, T, hT, ?_⟩
  intro N hN j high good Z
  have hN2 : 2 ≤ N := by omega
  let L := originalNonunitFamily j N δ high
  let G := if good then L.coprimePart else L
  have hsub : G.labels ⊆ L.labels := by
    cases good
    · exact Subset.rfl
    · exact filter_subset _ _
  have hdata (x : Profile) :
      G.weight x = (convolutionCoeff (windows j N) x.1 : ℝ) ∧ G.cofactor x = cofactor x := by
    cases good <;> exact ⟨rfl, rfl⟩
  apply hb N hN Profile G _ _ _ Z
  · intro x hx
    have hg := original_nonunit_geometry j hN2 hd hh high (hsub hx)
    rw [(hdata x).2]
    exact ⟨hg.power_lower, hg.power_upper⟩
  · intro x hx
    rw [(hdata x).1]
    exact_mod_cast actual_coefficient_pos (mem_filter.mp (hsub hx)).1
  · intro e
    have hs : G.layerFibre e ⊆
        (actualProfiles N δ (Wu04RemainingCore.row j) (windows j N) high).filter
          (fun x => cofactor x = e) := by
      intro x hx
      obtain ⟨hx, he⟩ := mem_filter.mp hx
      exact mem_filter.mpr ⟨(mem_filter.mp (hsub hx)).1, (hdata x).2.symm.trans he⟩
    calc
      _ = ∑ x ∈ G.layerFibre e, (convolutionCoeff (windows j N) x.1 : ℝ) :=
        sum_congr rfl (fun x _ => (hdata x).1)
      _ ≤ ∑ x ∈ (actualProfiles N δ (Wu04RemainingCore.row j) (windows j N) high).filter
          (fun x => cofactor x = e), (convolutionCoeff (windows j N) x.1 : ℝ) :=
        sum_le_sum_of_subset_of_nonneg hs (fun _ _ _ => Nat.cast_nonneg _)
      _ ≤ (40 : ℝ) ^ (1 + arity high) :=
        original_nonunit_fixed_cofactor j hN2 hd hh high e
      _ ≤ 40 ^ 6 := pow_le_pow_right₀ (by norm_num) (by cases high <;> simp [arity])

theorem original_nonunit_R1_paid {δ ε : ℝ}
    (hd : 0 < δ) (hh : δ ≤ 1 / 100) (heps : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ j : Fin 3, ∀ high good : Bool, ∀ Z : ℝ,
      let L := originalNonunitFamily j N δ high
      (if good then L.coprimePart else L).R1 (⌊(N : ℝ) ^ (1 / 2 - δ)⌋₊ + 1) Z ≤
        ε * truncatedSixthMassScale N := by
  obtain ⟨C, _, T0, hT04, hb⟩ := original_nonunit_R1_log_saving hd hh
    (show (0 : ℝ) < 3 by norm_num)
  have hC1 := wuSingularSeries_pos 1 (by norm_num)
  obtain ⟨T1, hlogBudget⟩ := eventually_atTop.mp
    ((tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (C / (ε * wuSingularSeries 1))))
  refine ⟨max T0 T1, hT04.trans (le_max_left _ _), ?_⟩
  intro N hN j high good Z
  have hl : 0 < log (N : ℝ) :=
    log_pos (by exact_mod_cast (show 1 < N by omega))
  have hseries : wuSingularSeries 1 ≤ wuSingularSeries N :=
    wuSingularSeries_le_of_dvd (by norm_num) (by omega) (one_dvd N)
  have hc : C / log (N : ℝ) ≤ ε * wuSingularSeries N := by
    apply (div_le_iff₀ hl).mpr
    have h := (div_le_iff₀ (mul_pos heps hC1)).mp (hlogBudget N (by omega))
    have h' := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hseries heps.le) hl.le
    dsimp only [Function.comp_apply] at h
    nlinarith
  calc
    _ ≤ C * N / log (N : ℝ) ^ (3 : ℝ) := hb N (by omega) j high good Z
    _ = (C / log N) * ((N : ℝ) / log N ^ 2) := by norm_num; ring
    _ ≤ (ε * wuSingularSeries N) * ((N : ℝ) / log N ^ 2) :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    _ = _ := by unfold truncatedSixthMassScale; ring

theorem original_nonunit_prime_upper_without_R1 {δ ε : ℝ}
    (hd : 0 < δ) (hh : δ ≤ 1 / 100) (heps : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ j : Fin 3, ∀ high : Bool, ∀ Z : ℝ,
      let D := ⌊(N : ℝ) ^ (1 / 2 - δ)⌋₊ + 1
      let L := originalNonunitFamily j N δ high
      1 < D → Z ≤ (D : ℝ) →
      L.primeMass ≤
        L.coprimePart.mass * ordinaryRosserMainSum true N 1 D Z +
        ε * truncatedSixthMassScale N + L.coprimePart.R2 D Z + L.coprimePart.small Z +
        ∑ b ∈ N.primeFactors, L.weightAt b := by
  obtain ⟨T, hT, hb⟩ := original_nonunit_R1_paid hd hh heps
  refine ⟨T, hT, ?_⟩
  intro N hN hEven j high Z D L hD hZ
  have hp := L.prime_upper_coprime_finite_sum (by omega) hEven D Z hD hZ
  have hr := hb N hN j high true Z
  change L.coprimePart.R1 D Z ≤ ε * truncatedSixthMassScale N at hr
  linarith only [hp, hr]

end Wu18938Campaign.M4
