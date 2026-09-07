import MathlibNt.SieveTheory.LiLiuGoldbachG12FlexibleRectangleC2
import MathlibNt.SieveTheory.LiLiuFouvryG9RectanglePrefixFinite

noncomputable section
open Classical Finset
open scoped BigOperators
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

namespace G12FineGrid

/-- Rounded geometric endpoints; repeated endpoints are deliberately retained. -/
def endpoint (ρ : ℝ) (i : ℕ) : ℕ := Nat.ceil (ρ ^ i) - 1

def cell (ρ : ℝ) (i : ℕ) : Finset ℕ := Ioc (endpoint ρ i) (endpoint ρ (i+1))

/-- Literal clipping, with no positive-width assumption. -/
def clipped (ρ : ℝ) (L H i : ℕ) : Finset ℕ :=
  Ioc (max L (endpoint ρ i)) (min H (endpoint ρ (i+1)))

theorem mem_clipped (ρ : ℝ) (L H i n : ℕ) :
    n ∈ clipped ρ L H i ↔ n ∈ Ioc L H ∧ n ∈ cell ρ i := by
  simp only [clipped, cell, mem_Ioc, max_lt_iff, le_min_iff]
  tauto

theorem endpoint_zero (ρ : ℝ) : endpoint ρ 0 = 0 := by simp [endpoint]

theorem endpoint_mono {ρ : ℝ} (hρ : 1 < ρ) : Monotone (endpoint ρ) := by
  intro i j hij
  exact Nat.sub_le_sub_right (Nat.ceil_mono (pow_le_pow_right₀ hρ.le hij)) 1

theorem mem_cell_iff {ρ : ℝ} (hρ : 1 < ρ) {i n : ℕ} (hn : 1 ≤ n) :
    n ∈ cell ρ i ↔ ρ^i ≤ (n : ℝ) ∧ (n : ℝ) < ρ^(i+1) := by
  have hp : 0 < Nat.ceil (ρ^(i+1)) := Nat.ceil_pos.mpr (pow_pos (by linarith) _)
  simp only [cell, mem_Ioc, endpoint]
  rw [← Nat.ceil_le, ← Nat.lt_ceil]
  omega

theorem unique {ρ : ℝ} (hρ : 1 < ρ) {i j n : ℕ}
    (hi : n ∈ cell ρ i) (hj : n ∈ cell ρ j) : i = j := by
  have hn : 1 ≤ n := by have := (mem_Ioc.mp hi).1; omega
  exact fouvryG9RectanglePrefix_index_unique hρ
    ((mem_cell_iff hρ hn).mp hi) ((mem_cell_iff hρ hn).mp hj)

theorem disjoint {ρ : ℝ} (hρ : 1 < ρ) {i j : ℕ} (hij : i ≠ j) :
    Disjoint (cell ρ i) (cell ρ j) := by
  exact disjoint_left.mpr (fun _ hi hj => hij (unique hρ hi hj))

/-- A finite cover works even when several adjacent endpoints coincide. -/
theorem cover_to_endpoint (ρ : ℝ) (K : ℕ) {n : ℕ}
    (hn : 1 ≤ n) (hN : n ≤ endpoint ρ K) : ∃ i < K, n ∈ cell ρ i := by
  induction K with
  | zero => simp [endpoint_zero] at hN; omega
  | succ K ih =>
    by_cases h : n ≤ endpoint ρ K
    · obtain ⟨i, hi, hm⟩ := ih h
      exact ⟨i, by omega, hm⟩
    · exact ⟨K, by omega, mem_Ioc.mpr ⟨by omega, hN⟩⟩

/-- A concrete logarithmic number of cells, not an existential truncation. -/
def count (ρ : ℝ) (N : ℕ) : ℕ := Nat.ceil (Real.log N / Real.log ρ) + 1

theorem count_covers {ρ : ℝ} (hρ : 1 < ρ) {N : ℕ} (hN : 1 ≤ N) :
    N ≤ endpoint ρ (count ρ N) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hl := Real.log_pos hρ
  have hc := Nat.le_ceil (Real.log N / Real.log ρ)
  have he : Real.log (N : ℝ) < (count ρ N : ℝ) * Real.log ρ := by
    dsimp [count]
    push_cast
    have := (div_le_iff₀ hl).mp hc
    nlinarith
  have hpow : (N : ℝ) < ρ ^ count ρ N := by
    apply (Real.log_lt_log_iff hNp (pow_pos (by linarith) _)).mp
    rwa [Real.log_pow]
  have := Nat.lt_ceil.mpr hpow
  unfold endpoint
  omega

theorem cover {ρ : ℝ} (hρ : 1 < ρ) {N n : ℕ} (hn : 1 ≤ n) (hN : n ≤ N) :
    ∃! i, i < count ρ N ∧ n ∈ cell ρ i := by
  obtain ⟨i, hi, hm⟩ := cover_to_endpoint ρ (count ρ N) hn
    (hN.trans (count_covers hρ (by omega)))
  exact ⟨i, ⟨hi, hm⟩, fun j hj => unique hρ hj.2 hm⟩

theorem endpoint_width {ρ : ℝ} (hρ : 1 < ρ) (i : ℕ) :
    (endpoint ρ (i+1) : ℝ) ≤ ρ * ((endpoint ρ i : ℝ) + 1) := by
  have hp : 0 < Nat.ceil (ρ^i) := Nat.ceil_pos.mpr (pow_pos (by linarith) _)
  have hp' : 0 < Nat.ceil (ρ^(i+1)) := Nat.ceil_pos.mpr (pow_pos (by linarith) _)
  have hlo := Nat.le_ceil (ρ^i)
  have hhi := Nat.ceil_lt_add_one (le_of_lt (pow_pos (by linarith : 0 < ρ) (i+1)))
  have hm := mul_le_mul_of_nonneg_left hlo (by linarith : 0 ≤ ρ)
  unfold endpoint
  rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
  push_cast
  rw [pow_succ] at hhi ⊢
  nlinarith

theorem clipped_width {ρ : ℝ} (hρ : 1 < ρ) (L H i : ℕ) :
    (min H (endpoint ρ (i+1)) : ℝ) ≤
      ρ * ((max L (endpoint ρ i) : ℝ) + 1) := by
  have hlo : (endpoint ρ i : ℝ) ≤ max L (endpoint ρ i) := by exact_mod_cast le_max_right L (endpoint ρ i)
  have hhi : (min H (endpoint ρ (i+1)) : ℝ) ≤ endpoint ρ (i+1) := by exact_mod_cast min_le_right H (endpoint ρ (i+1))
  have hw := endpoint_width hρ i
  push_cast at hlo hhi ⊢
  nlinarith

theorem clipped_dyadic {ρ : ℝ} (hρ : 1 < ρ) (hu : ρ ≤ 3/2) (L H i : ℕ)
    (hlo : 3 ≤ max L (endpoint ρ i)) :
    min H (endpoint ρ (i+1)) ≤ 2 * max L (endpoint ρ i) := by
  have hw := clipped_width hρ L H i
  have hlow : (3 : ℝ) ≤ max L (endpoint ρ i) := by exact_mod_cast hlo
  push_cast at hlow
  have he : (min H (endpoint ρ (i+1)) : ℝ) ≤ 2 * (max L (endpoint ρ i) : ℝ) := by nlinarith
  exact_mod_cast he


/-- Occupancy singles out a unique nonempty cell, not merely a chosen index. -/
theorem cover_nonempty {ρ : ℝ} (hρ : 1 < ρ) {N n : ℕ} (hn : 1 ≤ n) (hN : n ≤ N) :
    ∃! i, i < count ρ N ∧ n ∈ cell ρ i ∧ (cell ρ i).Nonempty := by
  obtain ⟨i, hi, hu⟩ := cover hρ hn hN
  exact ⟨i, ⟨hi.1, hi.2, ⟨n, hi.2⟩⟩, fun j hj => hu j ⟨hj.1,hj.2.1⟩⟩

theorem clipped_disjoint {ρ : ℝ} (hρ : 1 < ρ) (L H : ℕ) {i j : ℕ} (hij : i ≠ j) :
    Disjoint (clipped ρ L H i) (clipped ρ L H j) := by
  exact disjoint_left.mpr (fun n hi hj => hij
    (unique hρ ((mem_clipped ρ L H i n).mp hi).2 ((mem_clipped ρ L H j n).mp hj).2))

theorem clipped_cover {ρ : ℝ} (hρ : 1 < ρ) {L H n : ℕ} (hn : n ∈ Ioc L H) :
    ∃! i, i < count ρ H ∧ n ∈ clipped ρ L H i := by
  obtain ⟨hl,hh⟩ := mem_Ioc.mp hn
  obtain ⟨i,hi,hu⟩ := cover hρ (by omega : 1 ≤ n) hh
  exact ⟨i, ⟨hi.1, (mem_clipped _ _ _ _ _).mpr ⟨hn,hi.2⟩⟩,
    fun j hj => hu j ⟨hj.1,((mem_clipped _ _ _ _ _).mp hj.2).2⟩⟩

/-- Empty and reversed clipping intervals are included in this exact equality. -/
theorem clipped_union {ρ : ℝ} (hρ : 1 < ρ) (L H : ℕ) :
    (range (count ρ H)).biUnion (clipped ρ L H) = Ioc L H := by
  ext n
  constructor
  · intro hn
    obtain ⟨i,_,hi⟩ := mem_biUnion.mp hn
    exact ((mem_clipped _ _ _ _ _).mp hi).1
  · intro hn
    obtain ⟨i,⟨hi,hm⟩,_⟩ := clipped_cover hρ hn
    exact mem_biUnion.mpr ⟨i,mem_range.mpr hi,hm⟩

theorem endpoint_dyadic {ρ : ℝ} (hρ : 1 < ρ) (hu : ρ ≤ 3/2) (i : ℕ)
    (hi : 3 ≤ endpoint ρ i) : endpoint ρ (i+1) ≤ 2 * endpoint ρ i := by
  simpa using clipped_dyadic hρ hu 0 (endpoint ρ (i+1)) i (by simpa using hi)

end G12FineGrid
