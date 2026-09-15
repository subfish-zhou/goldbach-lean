import MathlibNt.Wu2004MeanValue.ActualAP
import Mathlib.Data.Finset.Max

/-! The actual reduced-residue supremum is attained separately at each
positive modulus. This is a finite selection, not an exchange of suprema
with a modulus sum. The source coordinates share the selected residue. -/

namespace Wu2004MeanValue

open Classical Finset
open scoped BigOperators
noncomputable section

def actualAPResidueSup (S : Finset ℕ) (f r : ℕ → ℝ) (d : ℕ) : ℝ :=
  sSup (insert 0 {v : ℝ | ∃ b : ℕ, b.Coprime d ∧ v = |actualAPSum S f r d b|})

theorem actualAPSum_residue_mod (S : Finset ℕ) (f r : ℕ → ℝ) (d b : ℕ) :
    actualAPSum S f r d (b % d) = actualAPSum S f r d b := by
  simp only [actualAPSum, ebar_residue_mod]

theorem actualAPResidueSup_attained (S : Finset ℕ) (f r : ℕ → ℝ)
    (d : ℕ) (hd : 0 < d) :
    ∃ b : ℕ, b < d ∧ b.Coprime d ∧
      actualAPResidueSup S f r d = |actualAPSum S f r d b| ∧
      ∀ a : ℕ, a.Coprime d → |actualAPSum S f r d a| ≤ |actualAPSum S f r d b| := by
  let R := (range d).filter (fun b => b.Coprime d)
  have hR : R.Nonempty := by
    refine ⟨1 % d, mem_filter.mpr ⟨mem_range.mpr (Nat.mod_lt _ hd), ?_⟩⟩
    exact (ZMod.coprime_mod_iff_coprime 1 d).mpr (Nat.coprime_one_left d)
  obtain ⟨b, hb, hmax⟩ := exists_max_image R (fun b => |actualAPSum S f r d b|) hR
  have hbound (a : ℕ) (ha : a.Coprime d) :
      |actualAPSum S f r d a| ≤ |actualAPSum S f r d b| := by
    rw [← actualAPSum_residue_mod S f r d a]
    exact hmax (a % d) (mem_filter.mpr ⟨mem_range.mpr (Nat.mod_lt _ hd),
      (ZMod.coprime_mod_iff_coprime a d).mpr ha⟩)
  have hupper : ∀ v ∈ insert 0
      {v : ℝ | ∃ a : ℕ, a.Coprime d ∧ v = |actualAPSum S f r d a|},
      v ≤ |actualAPSum S f r d b| := by
    intro v hv
    rcases Set.mem_insert_iff.mp hv with rfl | ⟨a, ha, rfl⟩
    · exact abs_nonneg _
    · exact hbound a ha
  refine ⟨b, mem_range.mp (mem_filter.mp hb).1, (mem_filter.mp hb).2, ?_, hbound⟩
  unfold actualAPResidueSup
  apply le_antisymm
  · exact csSup_le ⟨0, Set.mem_insert _ _⟩ hupper
  · exact le_csSup ⟨_, hupper⟩
      (Set.mem_insert_of_mem _ ⟨b, (mem_filter.mp hb).2, rfl⟩)

theorem actualAPSum_le_residueSup (S : Finset ℕ) (f r : ℕ → ℝ)
    (d b : ℕ) (hd : 0 < d) (hb : b.Coprime d) :
    |actualAPSum S f r d b| ≤ actualAPResidueSup S f r d := by
  obtain ⟨a, _, _, heq, hmax⟩ := actualAPResidueSup_attained S f r d hd
  rw [heq]
  exact hmax b hb

theorem actualAPResidueSup_sum_attained (S : Finset ℕ) (f r : ℕ → ℝ)
    (Q : ℕ) (w : ℕ → ℝ) :
    ∃ b : ℕ → ℕ, (∀ d ∈ Icc 1 Q, (b d).Coprime d) ∧
      (∑ d ∈ Icc 1 Q, w d * actualAPResidueSup S f r d) =
        ∑ d ∈ Icc 1 Q, w d * |actualAPSum S f r d (b d)| := by
  have hex : ∀ d : ℕ, ∃ b : ℕ, 0 < d →
      b.Coprime d ∧ actualAPResidueSup S f r d = |actualAPSum S f r d b| := by
    intro d
    by_cases hd : 0 < d
    · obtain ⟨b, _, hb, heq, _⟩ := actualAPResidueSup_attained S f r d hd
      exact ⟨b, fun _ => ⟨hb, heq⟩⟩
    · exact ⟨0, fun h => (hd h).elim⟩
  choose b hb using hex
  refine ⟨b, fun d hd => (hb d (mem_Icc.mp hd).1).1, ?_⟩
  apply sum_congr rfl
  intro d hd
  rw [(hb d (mem_Icc.mp hd).1).2]

end
end Wu2004MeanValue
