import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
# The coprimality partition of Fouvry

The binary separation argument underlying F84, Lemma 6 (pp. 226–227),
and F87, Lemma 7 (p. 624). The exponent is the square of the bound on
the number of distinct prime factors, as in F84's proof and F87's statement.
-/

namespace LiLiuPrereqFouvry.CoprimePartition

/-- A separating bit and its value on the first coordinate. -/
abbrev BitColor (T : ℕ) := Fin (Nat.log2 T + 1) × Bool

theorem exists_separating_bit {T a b : ℕ} (ha : a ≤ T) (hb : b ≤ T)
    (hab : a ≠ b) :
    ∃ i : Fin (Nat.log2 T + 1), a.testBit i ≠ b.testBit i := by
  obtain ⟨i, hi⟩ := Nat.exists_testBit_ne_of_ne hab
  have hT : T < 2 ^ (Nat.log2 T + 1) := by
    simpa [Nat.log2_eq_log_two] using Nat.lt_pow_succ_log_self (by decide : 1 < 2) T
  have hil : i < Nat.log2 T + 1 := by
    by_contra h
    have hp : 2 ^ (Nat.log2 T + 1) ≤ 2 ^ i :=
      Nat.pow_le_pow_right (by decide) (by omega)
    exact hi ((Nat.testBit_lt_two_pow (by omega)).trans
      (Nat.testBit_lt_two_pow (by omega)).symm)
  exact ⟨⟨i, hil⟩, hi⟩

/-- Choose a differing bit when there is one; the fallback is only used off domain. -/
noncomputable def bitColor (T a b : ℕ) : BitColor T :=
  if h : ∃ i : Fin (Nat.log2 T + 1), a.testBit i ≠ b.testBit i then
    ⟨Classical.choose h, a.testBit (Classical.choose h).val⟩
  else ⟨⟨0, by omega⟩, false⟩

theorem bitColor_spec {T a b : ℕ} (ha : a ≤ T) (hb : b ≤ T) (hab : a ≠ b) :
    a.testBit (bitColor T a b).1 = (bitColor T a b).2 ∧
      b.testBit (bitColor T a b).1 ≠ (bitColor T a b).2 := by
  classical
  have h := exists_separating_bit ha hb hab
  simpa only [bitColor, dif_pos h, ne_eq, true_and] using
    And.intro (rfl : a.testBit (Classical.choose h).val =
      a.testBit (Classical.choose h).val) (Classical.choose_spec h).symm

/-- Equal binary colors prohibit cross equality, not merely equality within a pair. -/
theorem bitColor_cross_ne {T a b c d : ℕ}
    (ha : a ≤ T) (hb : b ≤ T) (hc : c ≤ T) (hd : d ≤ T)
    (hab : a ≠ b) (hcd : c ≠ d) (hcolor : bitColor T a b = bitColor T c d) :
    a ≠ d := by
  have h₁ := (bitColor_spec ha hb hab).1
  have h₂ := (bitColor_spec hc hd hcd).2
  rw [hcolor] at h₁
  intro h
  exact h₂ (h ▸ h₁)

theorem card_bitColor (T : ℕ) :
    Fintype.card (BitColor T) = 2 * (Nat.log2 T + 1) := by
  simp [BitColor, Nat.mul_comm]

/-- Enumerate the distinct prime factors increasingly and pad to the requested length. -/
noncomputable def paddedFactor (ω n pad : ℕ) (i : Fin ω) : ℕ :=
  if h : i.val < n.primeFactors.card then
    n.primeFactors.orderEmbOfFin rfl ⟨i.val, h⟩
  else pad

theorem paddedFactor_mem_or_eq (ω n pad : ℕ) (i : Fin ω) :
    paddedFactor ω n pad i ∈ n.primeFactors ∨ paddedFactor ω n pad i = pad := by
  classical
  unfold paddedFactor
  split
  · exact Or.inl (Finset.orderEmbOfFin_mem _ _ _)
  · exact Or.inr rfl

theorem exists_paddedFactor {ω n p : ℕ} (hω : n.primeFactors.card ≤ ω)
    (hp : p ∈ n.primeFactors) (pad : ℕ) :
    ∃ i : Fin ω, paddedFactor ω n pad i = p := by
  classical
  have hp' : p ∈ Set.range (n.primeFactors.orderEmbOfFin rfl) := by
    rw [Finset.range_orderEmbOfFin]
    exact hp
  obtain ⟨i, hi⟩ := hp'
  refine ⟨⟨i.val, lt_of_lt_of_le i.isLt hω⟩, ?_⟩
  simpa only [paddedFactor, dif_pos i.isLt] using hi

theorem paddedFactor_le {T ω n pad : ℕ} (hn : n ≤ T) (hpad : pad ≤ T)
    (i : Fin ω) : paddedFactor ω n pad i ≤ T := by
  rcases paddedFactor_mem_or_eq ω n pad i with h | h
  · exact (Nat.le_of_mem_primeFactors h).trans hn
  · rw [h]
    exact hpad

/-- Asymmetric padding by 0 and 1 never creates a common prime factor. -/
theorem paddedFactor_ne {ω a b : ℕ} (hab : a.Coprime b) (i j : Fin ω) :
    paddedFactor ω a 0 i ≠ paddedFactor ω b 1 j := by
  intro heq
  rcases paddedFactor_mem_or_eq ω a 0 i with ha | ha <;>
    rcases paddedFactor_mem_or_eq ω b 1 j with hb | hb
  · exact (Finset.disjoint_left.mp hab.disjoint_primeFactors) ha (heq ▸ hb)
  · exact (Nat.prime_of_mem_primeFactors ha).ne_one (heq.trans hb)
  · exact (Nat.prime_of_mem_primeFactors hb).ne_zero (heq.symm.trans ha)
  · omega

/-- One binary color for every pair of prime-factor slots. -/
abbrev MatrixColor (T ω : ℕ) := Fin ω → Fin ω → BitColor T

noncomputable def matrixColor (T ω : ℕ) (a : ℕ × ℕ) : MatrixColor T ω :=
  fun i j => bitColor T (paddedFactor ω a.1 0 i) (paddedFactor ω a.2 1 j)

theorem card_matrixColor (T ω : ℕ) :
    Fintype.card (MatrixColor T ω) = (2 * (Nat.log2 T + 1)) ^ (ω ^ 2) := by
  simp [MatrixColor, ← pow_mul, pow_two, Nat.mul_comm]

/-- Equality of the full matrix forces coprimality across two different pairs. -/
theorem matrixColor_cross_coprime {T ω a b c d : ℕ} (hT : 1 ≤ T)
    (ha₀ : a ≠ 0) (hd₀ : d ≠ 0)
    (ha : a ≤ T) (hb : b ≤ T) (hc : c ≤ T) (hd : d ≤ T)
    (haω : a.primeFactors.card ≤ ω) (hdω : d.primeFactors.card ≤ ω)
    (hab : a.Coprime b) (hcd : c.Coprime d)
    (hcolor : matrixColor T ω (a, b) = matrixColor T ω (c, d)) :
    a.Coprime d := by
  apply (Nat.disjoint_primeFactors ha₀ hd₀).mp
  rw [Finset.disjoint_left]
  intro p hpa hpd
  obtain ⟨i, hi⟩ := exists_paddedFactor haω hpa 0
  obtain ⟨j, hj⟩ := exists_paddedFactor hdω hpd 1
  have hcol := congrFun (congrFun hcolor i) j
  have hne := bitColor_cross_ne
    (paddedFactor_le ha (Nat.zero_le T) i) (paddedFactor_le hb hT j)
    (paddedFactor_le hc (Nat.zero_le T) i) (paddedFactor_le hd hT j)
    (paddedFactor_ne hab i j) (paddedFactor_ne hcd i j) hcol
  exact hne (hi.trans hj.symm)

/-- The finite set in F87, Lemma 7; the prime factors are counted without multiplicity. -/
def admissiblePairs (T ω : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 1 T) ×ˢ (Finset.Icc 1 T)).filter
    (fun a => a.1.Coprime a.2 ∧ a.1.primeFactors.card ≤ ω ∧
      a.2.primeFactors.card ≤ ω)

theorem mem_admissiblePairs {T ω : ℕ} {a : ℕ × ℕ} :
    a ∈ admissiblePairs T ω ↔
      (1 ≤ a.1 ∧ a.1 ≤ T) ∧ (1 ≤ a.2 ∧ a.2 ≤ T) ∧
        a.1.Coprime a.2 ∧ a.1.primeFactors.card ≤ ω ∧ a.2.primeFactors.card ≤ ω := by
  simp only [admissiblePairs, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
  tauto

/-- The fiber of a prime-pair color matrix. -/
noncomputable def cell (T ω : ℕ) (κ : MatrixColor T ω) : Finset (ℕ × ℕ) :=
  (admissiblePairs T ω).filter (fun a => matrixColor T ω a = κ)

theorem mem_cell {T ω : ℕ} {κ : MatrixColor T ω} {a : ℕ × ℕ} :
    a ∈ cell T ω κ ↔ a ∈ admissiblePairs T ω ∧ matrixColor T ω a = κ := by
  classical
  exact Finset.mem_filter

theorem cell_cross_coprime {T ω : ℕ} {κ : MatrixColor T ω} {a b : ℕ × ℕ}
    (ha : a ∈ cell T ω κ) (hb : b ∈ cell T ω κ) : a.1.Coprime b.2 := by
  obtain ⟨ha, hca⟩ := mem_cell.mp ha
  obtain ⟨hb, hcb⟩ := mem_cell.mp hb
  obtain ⟨ha₁, ha₂, hac, haw, _⟩ := mem_admissiblePairs.mp ha
  obtain ⟨hb₁, hb₂, hbc, _, hbw⟩ := mem_admissiblePairs.mp hb
  exact matrixColor_cross_coprime (ha₁.1.trans ha₁.2) (by omega) (by omega)
    ha₁.2 ha₂.2 hb₁.2 hb₂.2 haw hbw hac hbc (hca.trans hcb.symm)

theorem disjoint_cells {T ω : ℕ} {κ η : MatrixColor T ω} (h : κ ≠ η) :
    Disjoint (cell T ω κ) (cell T ω η) := by
  classical
  rw [Finset.disjoint_left]
  intro a ha hb
  exact h ((mem_cell.mp ha).2.symm.trans (mem_cell.mp hb).2)

/-- Only nonempty fibers are retained, so this is a genuine partition into finite sets. -/
noncomputable def partition (T ω : ℕ) : Finset (Finset (ℕ × ℕ)) :=
  (((admissiblePairs T ω).image (matrixColor T ω)).image (cell T ω))

theorem mem_partition {T ω : ℕ} {s : Finset (ℕ × ℕ)} :
    s ∈ partition T ω ↔ ∃ a ∈ admissiblePairs T ω, cell T ω (matrixColor T ω a) = s := by
  classical
  simp [partition]

theorem partition_nonempty {T ω : ℕ} {s : Finset (ℕ × ℕ)}
    (hs : s ∈ partition T ω) : s.Nonempty := by
  obtain ⟨a, ha, rfl⟩ := mem_partition.mp hs
  exact ⟨a, mem_cell.mpr ⟨ha, rfl⟩⟩

theorem partition_pairwise_disjoint (T ω : ℕ) :
    (partition T ω : Set (Finset (ℕ × ℕ))).PairwiseDisjoint id := by
  classical
  intro s hs t ht hst
  obtain ⟨a, _, rfl⟩ := mem_partition.mp hs
  obtain ⟨b, _, rfl⟩ := mem_partition.mp ht
  exact disjoint_cells (fun h => hst (congrArg (cell T ω) h))

theorem partition_cover (T ω : ℕ) :
    (partition T ω).biUnion id = admissiblePairs T ω := by
  classical
  ext a
  simp only [Finset.mem_biUnion, id_eq]
  constructor
  · rintro ⟨s, hs, ha⟩
    obtain ⟨b, _, rfl⟩ := mem_partition.mp hs
    exact (mem_cell.mp ha).1
  · intro ha
    exact ⟨cell T ω (matrixColor T ω a),
      mem_partition.mpr ⟨a, ha, rfl⟩, mem_cell.mpr ⟨ha, rfl⟩⟩

theorem partition_cross_coprime {T ω : ℕ} {s : Finset (ℕ × ℕ)}
    (hs : s ∈ partition T ω) {a b : ℕ × ℕ} (ha : a ∈ s) (hb : b ∈ s) :
    a.1.Coprime b.2 := by
  obtain ⟨c, _, rfl⟩ := mem_partition.mp hs
  exact cell_cross_coprime ha hb

/-- The exact finite bound, including `ω = 0` and `T = 0,1`. -/
theorem card_partition_le (T ω : ℕ) :
    (partition T ω).card ≤ (2 * (Nat.log2 T + 1)) ^ (ω ^ 2) := by
  classical
  calc
    (partition T ω).card ≤ ((admissiblePairs T ω).image (matrixColor T ω)).card :=
      Finset.card_image_le
    _ ≤ Fintype.card (MatrixColor T ω) := Finset.card_le_univ _
    _ = _ := card_matrixColor T ω

/-- Arbitrary signed or complex weights decompose without a triangle inequality. -/
theorem sum_partition {M : Type*} [AddCommMonoid M] (T ω : ℕ) (f : ℕ × ℕ → M) :
    ∑ s ∈ partition T ω, ∑ a ∈ s, f a = ∑ a ∈ admissiblePairs T ω, f a := by
  classical
  rw [← partition_cover T ω]
  exact (Finset.sum_biUnion (partition_pairwise_disjoint T ω)).symm

end LiLiuPrereqFouvry.CoprimePartition
