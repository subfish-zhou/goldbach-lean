import F1TailDenominatorSquare

noncomputable section
open Real Set MeasureTheory
namespace F1TailPolynomialSigns

theorem low_nonneg {x : ℝ} (hx : 1 ≤ x) : 0 ≤ F1JointFTC.low x := by
  have hx0 : 0 < x := by linarith
  have hm : 0 ≤ x-1 := sub_nonneg.mpr hx
  rw [TailRationalBasis.low_rational hx0]
  have hid : TailRationalBasis.lowNumerator x = 160*(x-1)^1+720*(x-1)^2+(4048/3)*(x-1)^3+(4088/3)*(x-1)^4+(2398/3)*(x-1)^5+(815/3)*(x-1)^6+(5186/105)*(x-1)^7+(155/42)*(x-1)^8 := by
    unfold TailRationalBasis.lowNumerator
    ring
  rw [hid]
  positivity

theorem original_arguments {u : ℝ} (hu : u ∈ Icc 2 (927/200)) :
    1 ≤ u/2 ∧ 1 ≤ 2*(u-1)/u ∧
    1 ≤ ((1127/200)+u+1)/(2*(u+1)) ∧
    1 ≤ (2*(1127/200))/((1127/200)+u+1) := by
  have hu0 : 0 < u := by linarith [hu.1]
  have hu1 : 0 < u+1 := by linarith [hu.1]
  refine ⟨by linarith [hu.1], ?_, ?_, ?_⟩
  · apply (le_div_iff₀ hu0).2
    linarith [hu.1]
  · apply (le_div_iff₀ (by positivity : 0 < 2*(u+1))).2
    linarith [hu.2]
  · apply (le_div_iff₀ (by positivity : 0 < (1127/200)+u+1)).2
    linarith [hu.2]

theorem AB11_nonneg {u : ℝ} (hu : u ∈ Icc 2 (927/200)) :
    0 ≤ TailFiniteFTC.AB11.kernel u := by
  obtain ⟨h1,h2,h3,h4⟩ := original_arguments hu
  rw [← TailFiniteFTC.AB11.source_exact hu.1]
  exact div_nonneg (mul_nonneg (ActualTailVariation.floor_nonneg h1) (low_nonneg h3))
    (by linarith [hu.1])

theorem AB12_nonneg {u : ℝ} (hu : u ∈ Icc 2 (927/200)) :
    0 ≤ TailFiniteFTC.AB12.kernel u := by
  obtain ⟨h1,h2,h3,h4⟩ := original_arguments hu
  rw [← TailFiniteFTC.AB12.source_exact hu.1]
  exact div_nonneg (mul_nonneg (ActualTailVariation.floor_nonneg h1) (low_nonneg h4))
    (by linarith [hu.1])

theorem AB21_nonneg {u : ℝ} (hu : u ∈ Icc 2 (927/200)) :
    0 ≤ TailFiniteFTC.AB21.kernel u := by
  obtain ⟨h1,h2,h3,h4⟩ := original_arguments hu
  rw [← TailFiniteFTC.AB21.source_exact hu.1]
  exact div_nonneg (mul_nonneg (ActualTailVariation.floor_nonneg h2) (low_nonneg h3))
    (by linarith [hu.1])

theorem AB22_nonneg {u : ℝ} (hu : u ∈ Icc 2 (927/200)) :
    0 ≤ TailFiniteFTC.AB22.kernel u := by
  obtain ⟨h1,h2,h3,h4⟩ := original_arguments hu
  rw [← TailFiniteFTC.AB22.source_exact hu.1]
  exact div_nonneg (mul_nonneg (ActualTailVariation.floor_nonneg h2) (low_nonneg h4))
    (by linarith [hu.1])

theorem BA11_nonneg {u : ℝ} (hu : u ∈ Icc 2 (927/200)) :
    0 ≤ TailFiniteFTC.BA11.kernel u := by
  obtain ⟨h1,h2,h3,h4⟩ := original_arguments hu
  rw [← TailFiniteFTC.BA11.source_exact hu.1]
  exact div_nonneg (mul_nonneg (ActualTailVariation.floor_nonneg h3) (low_nonneg h1))
    (by linarith [hu.1])

theorem BA12_nonneg {u : ℝ} (hu : u ∈ Icc 2 (927/200)) :
    0 ≤ TailFiniteFTC.BA12.kernel u := by
  obtain ⟨h1,h2,h3,h4⟩ := original_arguments hu
  rw [← TailFiniteFTC.BA12.source_exact hu.1]
  exact div_nonneg (mul_nonneg (ActualTailVariation.floor_nonneg h4) (low_nonneg h1))
    (by linarith [hu.1])

theorem BA21_nonneg {u : ℝ} (hu : u ∈ Icc 2 (927/200)) :
    0 ≤ TailFiniteFTC.BA21.kernel u := by
  obtain ⟨h1,h2,h3,h4⟩ := original_arguments hu
  rw [← TailFiniteFTC.BA21.source_exact hu.1]
  exact div_nonneg (mul_nonneg (ActualTailVariation.floor_nonneg h3) (low_nonneg h2))
    (by linarith [hu.1])

theorem BA22_nonneg {u : ℝ} (hu : u ∈ Icc 2 (927/200)) :
    0 ≤ TailFiniteFTC.BA22.kernel u := by
  obtain ⟨h1,h2,h3,h4⟩ := original_arguments hu
  rw [← TailFiniteFTC.BA22.source_exact hu.1]
  exact div_nonneg (mul_nonneg (ActualTailVariation.floor_nonneg h4) (low_nonneg h2))
    (by linarith [hu.1])

end F1TailPolynomialSigns
