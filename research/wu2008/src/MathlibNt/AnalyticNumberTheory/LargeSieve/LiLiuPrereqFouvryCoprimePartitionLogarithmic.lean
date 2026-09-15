import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryCoprimePartition
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Logarithmic cardinality bound for the Fouvry partition

The explicit absolute constant `4 / log 2` converts the exact binary count
to the bound in F87, Lemma 7. Real cutoffs are handled by the natural floor,
with the original integer-pair domain proved exactly.
-/

namespace LiLiuPrereqFouvry.CoprimePartition

noncomputable def partitionConstant : ℝ := 4 / Real.log 2

theorem partitionConstant_pos : 0 < partitionConstant := by
  exact div_pos (by norm_num) (Real.log_pos (by norm_num))

theorem bitColor_card_le_log {T : ℕ} (hT : 2 ≤ T) :
    (2 * (Nat.log2 T + 1) : ℕ) ≤ partitionConstant * Real.log T := by
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : Real.log 2 ≤ Real.log T :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hT)
  have hnat : (Nat.log2 T : ℝ) ≤ Real.log T / Real.log 2 := Real.log2_le_logb T
  have hnat' := (le_div_iff₀ htwo).mp hnat
  have hbound : (2 * (Nat.log2 T + 1) : ℕ) * Real.log 2 ≤ 4 * Real.log T := by
    push_cast
    nlinarith
  rw [partitionConstant, div_mul_eq_mul_div]
  exact (le_div_iff₀ htwo).mpr hbound

theorem card_partition_le_log {T : ℕ} (hT : 2 ≤ T) (ω : ℕ) :
    ((partition T ω).card : ℝ) ≤ (partitionConstant * Real.log T) ^ (ω ^ 2) := by
  calc
    ((partition T ω).card : ℝ) ≤ ((2 * (Nat.log2 T + 1)) ^ (ω ^ 2) : ℕ) := by
      exact_mod_cast card_partition_le T ω
    _ ≤ (partitionConstant * Real.log T) ^ (ω ^ 2) := by
      push_cast
      exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast bitColor_card_le_log hT) _

/-- The integer pairs with real upper cutoff `T`. -/
noncomputable def realAdmissiblePairs (T : ℝ) (ω : ℕ) : Finset (ℕ × ℕ) :=
  admissiblePairs ⌊T⌋₊ ω

theorem mem_realAdmissiblePairs {T : ℝ} (hT : 0 ≤ T) {ω : ℕ} {a : ℕ × ℕ} :
    a ∈ realAdmissiblePairs T ω ↔
      (1 ≤ a.1 ∧ (a.1 : ℝ) ≤ T) ∧ (1 ≤ a.2 ∧ (a.2 : ℝ) ≤ T) ∧
        a.1.Coprime a.2 ∧ a.1.primeFactors.card ≤ ω ∧ a.2.primeFactors.card ≤ ω := by
  simp only [realAdmissiblePairs, mem_admissiblePairs, Nat.le_floor_iff hT]

noncomputable def realPartition (T : ℝ) (ω : ℕ) : Finset (Finset (ℕ × ℕ)) :=
  partition ⌊T⌋₊ ω

theorem realPartition_nonempty {T : ℝ} {ω : ℕ} {s : Finset (ℕ × ℕ)}
    (hs : s ∈ realPartition T ω) : s.Nonempty :=
  partition_nonempty hs

theorem realPartition_pairwise_disjoint (T : ℝ) (ω : ℕ) :
    (realPartition T ω : Set (Finset (ℕ × ℕ))).PairwiseDisjoint id :=
  partition_pairwise_disjoint _ _

theorem realPartition_cover (T : ℝ) (ω : ℕ) :
    (realPartition T ω).biUnion id = realAdmissiblePairs T ω :=
  partition_cover _ _

theorem realPartition_cross_coprime {T : ℝ} {ω : ℕ} {s : Finset (ℕ × ℕ)}
    (hs : s ∈ realPartition T ω) {a b : ℕ × ℕ} (ha : a ∈ s) (hb : b ∈ s) :
    a.1.Coprime b.2 :=
  partition_cross_coprime hs ha hb

theorem card_realPartition_le_log {T : ℝ} (hT : 2 ≤ T) (ω : ℕ) :
    ((realPartition T ω).card : ℝ) ≤ (partitionConstant * Real.log T) ^ (ω ^ 2) := by
  have hT₀ : 0 ≤ T := by linarith
  have hfloor : 2 ≤ ⌊T⌋₊ := (Nat.le_floor_iff hT₀).mpr (by exact_mod_cast hT)
  have hfloor₀ : (0 : ℝ) < ⌊T⌋₊ := by exact_mod_cast (by omega : 0 < ⌊T⌋₊)
  calc
    ((realPartition T ω).card : ℝ) ≤
        (partitionConstant * Real.log (⌊T⌋₊ : ℝ)) ^ (ω ^ 2) :=
      card_partition_le_log hfloor ω
    _ ≤ _ := pow_le_pow_left₀
      (mul_nonneg partitionConstant_pos.le (Real.log_natCast_nonneg _))
      (mul_le_mul_of_nonneg_left (Real.log_le_log hfloor₀ (Nat.floor_le hT₀))
        partitionConstant_pos.le) _

theorem sum_realPartition {M : Type*} [AddCommMonoid M] (T : ℝ) (ω : ℕ)
    (f : ℕ × ℕ → M) :
    ∑ s ∈ realPartition T ω, ∑ a ∈ s, f a = ∑ a ∈ realAdmissiblePairs T ω, f a :=
  sum_partition _ _ _

/-- F87, Lemma 7, with a constructed finite partition and an explicit absolute constant.
The statement also allows `ω = 0`; the printed lemma only requires `ω ≥ 1`. -/
theorem fouvry_coprime_partition :
    ∃ C : ℝ, 0 < C ∧ ∀ (T : ℝ), 2 ≤ T → ∀ (ω : ℕ),
      ∃ P : Finset (Finset (ℕ × ℕ)),
        (∀ s ∈ P, s.Nonempty) ∧
        (P : Set (Finset (ℕ × ℕ))).PairwiseDisjoint id ∧
        P.biUnion id = realAdmissiblePairs T ω ∧
        (∀ s ∈ P, ∀ a ∈ s, ∀ b ∈ s, a.1.Coprime b.2) ∧
        (P.card : ℝ) ≤ (C * Real.log T) ^ (ω ^ 2) := by
  refine ⟨partitionConstant, partitionConstant_pos, ?_⟩
  intro T hT ω
  exact ⟨realPartition T ω, fun _ hs => realPartition_nonempty hs,
    realPartition_pairwise_disjoint T ω, realPartition_cover T ω,
    fun _ hs _ ha _ hb => realPartition_cross_coprime hs ha hb,
    card_realPartition_le_log hT ω⟩

end LiLiuPrereqFouvry.CoprimePartition
