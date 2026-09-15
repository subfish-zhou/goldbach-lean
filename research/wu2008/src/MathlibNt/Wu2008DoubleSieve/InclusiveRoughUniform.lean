import MathlibNt.Wu2008DoubleSieve.NonunitRoughUniform

open Finset Real LiLiuPrereqBuchstab

namespace Wu2008DoubleSieve.InclusiveRoughUniform

/-- The unit has no prime divisor, independently of the roughness cutoff. -/
theorem rough_one (y : ℝ) : Rough y 1 := by
  intro p hp hdiv
  exact False.elim (hp.ne_one (Nat.dvd_one.mp hdiv))

/-- Membership of the unit depends only on the inclusive size cutoff. -/
theorem one_mem_roughNumbers_iff (x y : ℝ) :
    1 ∈ roughNumbers x y ↔ 1 ≤ x := by
  rw [mem_roughNumbers]
  simp only [Nat.cast_one]
  exact ⟨fun h => h.2.1, fun h => ⟨by norm_num, h, rough_one y⟩⟩

/-- Exact disjoint accounting: the unit is not an error term. -/
theorem card_eq_unit_add_erase (x y : ℝ) :
    (roughNumbers x y).card =
      (if 1 ≤ x then 1 else 0) + ((roughNumbers x y).erase 1).card := by
  classical
  by_cases hx : 1 ≤ x
  · rw [if_pos hx]
    exact (card_erase_add_one ((one_mem_roughNumbers_iff x y).mpr hx)).symm.trans
      (Nat.add_comm _ _)
  · have hn : 1 ∉ roughNumbers x y := fun h => hx ((one_mem_roughNumbers_iff x y).mp h)
    simp only [if_neg hx, zero_add, erase_eq_of_notMem hn]

theorem card_eq_unit_add_erase_real (x y : ℝ) :
    ((roughNumbers x y).card : ℝ) =
      (if 1 ≤ x then 1 else 0) + (((roughNumbers x y).erase 1).card : ℝ) := by
  exact_mod_cast card_eq_unit_add_erase x y

/-- Below one there are no positive integers in the carrier. -/
theorem roughNumbers_empty_of_lt_one {x y : ℝ} (hx : x < 1) :
    roughNumbers x y = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro n hn
  obtain ⟨hnpos, hnx, _⟩ := mem_roughNumbers.mp hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hnpos
  linarith

/-- In the small-cofactor region the inclusive count is exactly the unit atom. -/
theorem count_eq_unit_of_lt {x y : ℝ} (hy : 1 ≤ y) (hxy : x < y) :
    (roughNumbers x y).card = if 1 ≤ x then 1 else 0 := by
  rw [card_eq_unit_add_erase, NonunitRoughUniform.nonunit_empty hy hxy]
  simp only [card_empty, Nat.add_zero]

/-- One threshold before all scales, retaining both the unit and the closed legal gate.
The only analytic estimate used is the established nonunit producer. -/
theorem uniform_upper {η τ : ℝ} (hη : 0 < η) (hτ : 0 < τ) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ x y : ℝ,
      x ≤ (N : ℝ) → (N : ℝ) ^ η ≤ y →
      ((roughNumbers x y).card : ℝ) ≤
        (if 1 ≤ x then 1 else 0) +
        (if y ≤ x then (buchstab (log x / log y) + τ) * x / log y else 0) := by
  obtain ⟨T, hT, hscalar⟩ := NonunitRoughUniform.uniform_upper hη hτ
  refine ⟨T, hT, ?_⟩
  intro N hN x y hxN hyN
  obtain ⟨hempty, hupper⟩ := hscalar N hN x y hxN hyN
  rw [card_eq_unit_add_erase_real]
  apply add_le_add le_rfl
  by_cases hxy : y ≤ x
  · rw [if_pos hxy]
    exact hupper hxy
  · rw [if_neg hxy, hempty (lt_of_not_ge hxy)]
    norm_num

end Wu2008DoubleSieve.InclusiveRoughUniform
