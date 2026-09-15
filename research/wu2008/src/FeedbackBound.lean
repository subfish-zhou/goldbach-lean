import FiniteSameMother

namespace FeedbackLimit
open Wu2008DoubleSieve NodeExtension ActualNineFeedback Set Filter
open scoped Topology
noncomputable section

/-- The genuine upper-improvement cap, without evaluating its coordinates. -/
def B (i : Fin 9) : ℝ := wuUpperCoefficient (upperNode i)

theorem actualNine_le_B {δ : ℝ} (hd : 0 < δ) (hh : δ ≤ 1 / 10) (i : Fin 9) :
    actualNine δ i ≤ B i := by
  have hs := upperNode_bounds i
  have hd' : δ < 1 / 2 := by linarith
  exact (wuImprovementLimit_le_fixed_depth true 0 hd hd' hs.1 (by linarith)).trans
    (wuImprovementAtInfinity_upper_bound (by omega) hd hd' hs.1 (by linarith))

/-- A coordinatewise contradiction uses only arbitrarily small positive delta,
not continuity of the actual improvement in delta. -/
theorem lowerIterate_le_B (n : ℕ) (i : Fin 9) : lowerIterate n i ≤ B i := by
  by_contra h
  have hμ : 0 < lowerIterate n i - B i := sub_pos.mpr (lt_of_not_ge h)
  have hr := marginRadius_pos (debitIterate_nonneg n i) hμ
  obtain ⟨δ, hd, hs⟩ := exists_between hr
  have hh : δ ≤ 1 / 10 := hs.le.trans (min_le_left _ _)
  have hp := deltaLoss_mul_lt_margin (debitIterate_nonneg n i) hμ hd hs
  have ha := (finite_actual_nine hd hh n i).trans (actualNine_le_B hd hh i)
  linarith only [hp, ha]

theorem lowerIterate_bdd (i : Fin 9) : BddAbove (range (fun n => lowerIterate n i)) :=
  ⟨B i, by rintro _ ⟨n, rfl⟩; exact lowerIterate_le_B n i⟩

/-- Coordinatewise supremum of the actual feedback iterates. -/
def Ainf (i : Fin 9) : ℝ := ⨆ n : ℕ, lowerIterate n i

theorem lowerIterate_le_Ainf (n : ℕ) (i : Fin 9) : lowerIterate n i ≤ Ainf i :=
  le_ciSup (lowerIterate_bdd i) n

theorem Ainf_nonneg (i : Fin 9) : 0 ≤ Ainf i :=
  (lowerIterate_nonneg 0 i).trans (lowerIterate_le_Ainf 0 i)

theorem Ainf_le_B (i : Fin 9) : Ainf i ≤ B i :=
  ciSup_le (fun n => lowerIterate_le_B n i)

theorem lowerIterate_tendsto (i : Fin 9) :
    Tendsto (fun n => lowerIterate n i) atTop (𝓝 (Ainf i)) :=
  tendsto_atTop_ciSup (lowerIterate_monotone i) (lowerIterate_bdd i)

end
end FeedbackLimit
