import MathlibNt.Wu2008DoubleSieve.SecondFunctionalUnitFinite

/-! # The literal unit slice of the accepted Gamma16 sieve mass -/
namespace Wu2008DoubleSieve
open Finset Real
open scoped Classical

noncomputable def secondFunctionalUnitGamma16 {i : ℕ} (N : ℕ) (δ : ℝ)
    (W : Fin i → Finset ℕ) : ℝ :=
  ∑ c ∈ (gamma16Profiles N δ W).filter (fun c => c.2.2.2.2 = 1),
    (convolutionCoeff W c.1 : ℝ) * (gamma16PrimeFibre N δ c).card

/-- Exact decomposition of the actual X, not a source-count substitution. -/
theorem secondFunctionalUnitGamma16_add_nonunit {i : ℕ} (N : ℕ) (δ : ℝ)
    (W : Fin i → Finset ℕ) :
    secondFunctionalUnitGamma16 N δ W +
      (∑ c ∈ (gamma16Profiles N δ W).filter (fun c => c.2.2.2.2 ≠ 1),
        (convolutionCoeff W c.1 : ℝ) * (gamma16PrimeFibre N δ c).card) =
      gamma16X N δ W :=
  sum_filter_add_sum_filter_not _ _ _

theorem secondFunctionalUnitGamma16_geometry {i N : ℕ} {δ : ℝ}
    {W : Fin i → Finset ℕ} {c : Gamma16Profile} (hc : c ∈ gamma16Profiles N δ W) :
    c.1 ∈ boxConvolutionSupport W ∧
      (0 < c.2.1 ∧ (c.2.1 : ℝ) ≤ wuLocalCutoff N δ c.1 (5 / 2)) ∧
      (0 < c.2.2.1 ∧ (c.2.2.1 : ℝ) ≤ wuLocalCutoff N δ c.1 (5 / 2)) ∧
      (0 < c.2.2.2.1 ∧ (c.2.2.2.1 : ℝ) ≤ wuLocalCutoff N δ c.1 (5 / 2)) := by
  rcases c with ⟨d, p3, p2, p1, n⟩
  obtain ⟨hd, h3, h2, h1, _⟩ := mem_gamma16Profiles.mp hc
  have hp3 := mem_primeWindow.mp h3
  have hp2 := mem_primeWindow.mp h2
  have hp1 := mem_primeWindow.mp h1
  exact ⟨hd, ⟨hp3.1.pos, hp3.2.2.2.le⟩,
    ⟨hp2.1.pos, hp2.2.2.2.le.trans hp3.2.2.2.le⟩,
    ⟨hp1.1.pos, hp1.2.2.2.le.trans (hp2.2.2.2.le.trans hp3.2.2.2.le)⟩⟩

theorem secondFunctionalUnitGamma16_fibre_geometry {N : ℕ} {δ : ℝ}
    {c : Gamma16Profile} {p : ℕ} (hp : p ∈ gamma16PrimeFibre N δ c) :
    0 < p ∧ (p : ℝ) ≤ wuLocalCutoff N δ c.1 (5 / 2) := by
  obtain ⟨_, hprime, _, hbound, _⟩ := mem_filter.mp hp
  exact ⟨hprime.pos, hbound⟩

/-- Every local premise is produced from the original windows and source box. -/
theorem secondFunctionalUnitGamma16_le {i k N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1 / 2)
    (hb : wuSourceBox k δ N i Δ V) :
    secondFunctionalUnitGamma16 N δ (convolutionWuWindows N Δ V) ≤
      ((N : ℝ) ^ (1 / 2 - δ)) ^ (4 / (5 / 2 : ℝ)) *
        boxConvolutionReciprocalMass (convolutionWuWindows N Δ V) := by
  apply secondFunctionalUnit_mass_le _ _ _ (rpow_nonneg (Nat.cast_nonneg N) _)
    (by norm_num) (by norm_num)
  · intro d hd
    exact (omega3_source_support_le_Q hN hδ hδhi hb hd).1
  · intro c hc _
    exact secondFunctionalUnitGamma16_geometry hc
  · intro c _ _ p hp
    exact secondFunctionalUnitGamma16_fibre_geometry hp

theorem secondFunctionalUnitGamma16_nonneg {i : ℕ} (N : ℕ) (δ : ℝ)
    (W : Fin i → Finset ℕ) : 0 ≤ secondFunctionalUnitGamma16 N δ W :=
  sum_nonneg fun _ _ => mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- The zero-mass case is included without cancellation by the mass. -/
theorem secondFunctionalUnitGamma16_eq_zero_of_mass_zero {i k N : ℕ}
    {δ Δ : ℝ} {V : Fin i → ℝ} (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1 / 2)
    (hb : wuSourceBox k δ N i Δ V)
    (hmass : boxConvolutionReciprocalMass (convolutionWuWindows N Δ V) = 0) :
    secondFunctionalUnitGamma16 N δ (convolutionWuWindows N Δ V) = 0 := by
  apply le_antisymm _ (secondFunctionalUnitGamma16_nonneg N δ _)
  simpa only [hmass, mul_zero] using secondFunctionalUnitGamma16_le hN hδ hδhi hb

end Wu2008DoubleSieve
