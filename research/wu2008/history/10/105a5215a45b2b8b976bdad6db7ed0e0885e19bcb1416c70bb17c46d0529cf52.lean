import WSrcGridRoot

namespace WuSource.SrcGridAccepted
open Wu2008DoubleSieve NodeExtension

/-- Accept a certificate valid only below its own positive radius. -/
theorem small_radius_tables {z : Fin 9 → ℝ} {d : ℝ} (hd : 0 < d)
    (hz : ∀ δ : ℝ, 0 < δ → δ < d → ∀ k, z k ≤ actualNine δ k) :
    ∃ r : ℝ, 0 < r ∧ r < d ∧ r ≤ 1/10 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ r →
        (∀ i : ℕ, 2 ≤ i → i ≤ 29 →
          extendedNode z i ≤ wuImprovementLimit true δ (rNode i)) ∧
        (∀ j : ℕ, j ≤ 29 →
          originalTransfer z j ≤ wuImprovementLimit false δ (rNode j)) := by
  let r : ℝ := min (d/2) (1/10)
  have hr : 0 < r := lt_min (half_pos hd) (by norm_num)
  have hrd : r < d := (min_le_left _ _).trans_lt (half_lt_self hd)
  have hrhi : r ≤ 1/10 := min_le_right _ _
  refine ⟨r,hr,hrd,hrhi,?_⟩
  intro δ hδ hδr
  exact SrcGrid.full_tables_lower hδ (hδr.trans hrhi)
    (hz δ hδ (hδr.trans_lt hrd))

end WuSource.SrcGridAccepted
