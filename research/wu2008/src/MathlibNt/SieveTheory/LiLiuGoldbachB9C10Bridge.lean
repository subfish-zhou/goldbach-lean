import MathlibNt.SieveTheory.LiLiuGoldbachS5SwitchedCarrier
import MathlibNt.SieveTheory.LiLiuGoldbachB10ProductCount

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

theorem goldbachC9Pairs_eq_C10Pairs (N : ℕ) :
    goldbachC9Pairs N = goldbachC10Pairs N ((N : ℝ)^(4 / 53 : ℝ))
      ((N : ℝ)^(1 / 3 : ℝ)) := by
  ext rs
  rw [mem_goldbachC9Pairs_iff, mem_goldbachC10Pairs_iff]
  constructor
  · rintro ⟨hr, hs, hc, hlo, _hle, hp, hrhi, hslo⟩
    exact ⟨hr, hs, hc, hlo, hrhi, hslo, hp⟩
  · rintro ⟨hr, hs, hc, hlo, hrhi, hslo, hp⟩
    exact ⟨hr, hs, hc, hlo, by exact_mod_cast hrhi.trans hslo, hp, hrhi, hslo⟩

theorem goldbachC9ProductSupport_eq_C10ProductSupport (N : ℕ) :
    goldbachC9ProductSupport N =
      goldbachC10ProductSupport N ((N : ℝ)^(4 / 53 : ℝ)) ((N : ℝ)^(1 / 3 : ℝ)) := by
  unfold goldbachC9ProductSupport goldbachC10ProductSupport
  rw [goldbachC9Pairs_eq_C10Pairs]
  rfl

/-- Equality of the entire labelled mother families, not just of their output sets. -/
theorem goldbachB9PlusAtoms_eq_B10ZeroPrefix (N : ℕ) :
    goldbachB9PlusAtoms N = goldbachB10Atoms N 0
      ((N : ℝ)^(4 / 53 : ℝ)) ((N : ℝ)^(1 / 3 : ℝ)) := by
  ext x
  rw [mem_goldbachB9PlusAtoms_iff, mem_goldbachB10Atoms_iff]
  constructor
  · rintro ⟨hrs, hq, hprod⟩
    have hm := goldbachC9Prod_pos hrs
    have hmR : (0 : ℝ) < (goldbachC10Prod x.1 : ℝ) := by exact_mod_cast hm
    refine ⟨(goldbachC9Pairs_eq_C10Pairs N) ▸ hrs, ?_, hq, ?_, ?_⟩
    · apply Finset.mem_range.mpr
      have hle := Nat.le_mul_of_pos_left x.2 hm
      omega
    · simp only [zero_mul, zero_div]
      exact_mod_cast hq.pos
    · apply (lt_div_iff₀ hmR).mpr
      exact_mod_cast (by simpa [goldbachC9Prod, goldbachC8Prod, goldbachC10Prod,
        mul_comm] using hprod : x.2 * goldbachC10Prod x.1 < N)
  · rintro ⟨hrs, _hrange, hq, _hlo, hhi⟩
    have hrs9 : x.1 ∈ goldbachC9Pairs N := (goldbachC9Pairs_eq_C10Pairs N).symm ▸ hrs
    have hmR : (0 : ℝ) < (goldbachC10Prod x.1 : ℝ) := by
      exact_mod_cast goldbachC9Prod_pos hrs9
    refine ⟨hrs9, hq, ?_⟩
    have hp : x.2 * goldbachC10Prod x.1 < N := by
      exact_mod_cast (lt_div_iff₀ hmR).mp hhi
    simpa [goldbachC9Prod, goldbachC8Prod, goldbachC10Prod, mul_comm] using hp

theorem goldbachB9PlusSiftedAtoms_eq_B10ZeroPrefix (N : ℕ) (Z : ℝ) :
    goldbachB9PlusSiftedAtoms N Z = goldbachB10SiftedAtoms N 0
      ((N : ℝ)^(4 / 53 : ℝ)) ((N : ℝ)^(1 / 3 : ℝ)) Z := by
  classical
  rw [goldbachB9PlusSiftedAtoms, goldbachB9PlusAtoms_eq_B10ZeroPrefix]
  ext x
  simp only [Finset.mem_filter, mem_goldbachB10Atoms_iff,
    mem_goldbachB10SiftedAtoms_iff]
  change ((_ ∧ _ ∧ _) ∧ literalHPoint N 1 Z (goldbachPi10Output N x)) ↔ _
  tauto

theorem goldbachB9PlusSifted_card_eq_B10ZeroPrefix (N : ℕ) (Z : ℝ) :
    ((goldbachB9PlusSiftedAtoms N Z).card : ℤ) = goldbachB10SiftedCount N 0
      ((N : ℝ)^(4 / 53 : ℝ)) ((N : ℝ)^(1 / 3 : ℝ)) Z := by
  rw [goldbachB9PlusSiftedAtoms_eq_B10ZeroPrefix, goldbachB10SiftedCount_eq_card_atoms]

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig