import MathlibNt.SieveTheory.LiLiuGoldbachG12FineGridMother

noncomputable section
open Classical Finset
open scoped BigOperators
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

namespace G12FineGrid

def longLower (ρ : ℝ) (k : ℕ × ℕ) : ℕ := max 0 (endpoint ρ k.1)
def longUpper (ρ : ℝ) (N : ℕ) (k : ℕ × ℕ) : ℕ := min (N-1) (endpoint ρ (k.1+1))
def shortLower (ρ : ℝ) (N : ℕ) (k : ℕ × ℕ) : ℕ := max (lowCut N) (endpoint ρ k.2)
def shortUpper (ρ : ℝ) (N : ℕ) (k : ℕ × ℕ) : ℕ := min (highCut N) (endpoint ρ (k.2+1))

/-- The exact production rectangle, at the actual clipped endpoints. -/
def safe (ρ : ℝ) (N : ℕ) (ε : ℝ) (k : ℕ × ℕ) : Finset (ℕ × ℕ) :=
  G12FlexibleRectangle.rectangle N ε (longLower ρ k) (longUpper ρ N k)
    (shortLower ρ N k) (shortUpper ρ N k)

/-- This set has no analytic smallness assertion. -/
def boundaryCell (ρ : ℝ) (N : ℕ) (ε : ℝ) (k : ℕ × ℕ) : Finset (ℕ × ℕ) :=
  motherCell ρ N ε k \ safe ρ N ε k

theorem short_lower_valid (ρ : ℝ) (N : ℕ) (k : ℕ × ℕ) :
    (N : ℝ)^(4/53 : ℝ) ≤ shortLower ρ N k := by
  exact (Nat.le_ceil _).trans (by exact_mod_cast le_max_left (lowCut N) (endpoint ρ k.2))

theorem highCut_strict {N : ℕ} (hN : 1 ≤ N) :
    (highCut N : ℝ) < (N : ℝ)^(1/10 : ℝ) := by
  have hp : (0 : ℝ) < (N : ℝ)^(1/10 : ℝ) :=
    Real.rpow_pos_of_pos (by exact_mod_cast (by omega : 0 < N)) _
  have hc := Nat.ceil_pos.mpr hp
  have hh := Nat.ceil_lt_add_one hp.le
  unfold highCut
  rw [Nat.cast_sub (by omega), Nat.cast_one]
  linarith

theorem short_upper_valid (ρ : ℝ) {N : ℕ} (hN : 1 ≤ N) (k : ℕ × ℕ) :
    (shortUpper ρ N k : ℝ) < (N : ℝ)^(1/10 : ℝ) := by
  exact lt_of_le_of_lt (by exact_mod_cast min_le_left (highCut N) (endpoint ρ (k.2+1)))
    (highCut_strict hN)

theorem safe_subset (ρ : ℝ) {N : ℕ} (hN : 1 ≤ N) (ε : ℝ) (k : ℕ × ℕ) :
    safe ρ N ε k ⊆ motherCell ρ N ε k := by
  intro p hp
  have hm := G12FlexibleRectangle.rectangle_subset_mother N ε
    (longLower ρ k) (longUpper ρ N k) (shortLower ρ N k) (shortUpper ρ N k)
    (short_lower_valid ρ N k) (short_upper_valid ρ hN k) hp
  have hb : p ∈ box ρ N k := by
    obtain ⟨hl,hr⟩ := mem_product.mp hp
    exact mem_product.mpr ⟨(mem_filter.mp hl).1,(mem_filter.mp hr).1⟩
  exact mem_filter.mpr ⟨hm,hb⟩

/-- All three failed tests are still in the boundary, without paying for them. -/
theorem boundaryCell_iff (ρ : ℝ) (N : ℕ) (ε : ℝ) (k : ℕ × ℕ) (m r : ℕ)
    (hp : (m,r) ∈ motherCell ρ N ε k) :
    (m,r) ∈ boundaryCell ρ N ε k ↔
      m.minFac < shortUpper ρ N k ∨ (shortLower ρ N k : ℝ)*m < ε*N ∨
        N ≤ shortUpper ρ N k*m := by
  obtain ⟨hm,hb⟩ := mem_filter.mp hp
  obtain ⟨hl,hr⟩ := mem_product.mp hb
  have he := G12FlexibleRectangle.local_boundary_iff N m r
    (longLower ρ k) (longUpper ρ N k) (shortLower ρ N k) (shortUpper ρ N k)
    ε hm hl hr
  simpa only [boundaryCell, mem_sdiff, hp, true_and, G12FlexibleRectangle.boundary,
    hm, safe] using he

theorem local_partition (ρ : ℝ) {N : ℕ} (hN : 1 ≤ N) (ε : ℝ) (k : ℕ × ℕ) :
    Disjoint (safe ρ N ε k) (boundaryCell ρ N ε k) ∧
      safe ρ N ε k ∪ boundaryCell ρ N ε k = motherCell ρ N ε k := by
  exact ⟨disjoint_sdiff_self_right, union_sdiff_of_subset (safe_subset ρ hN ε k)⟩

theorem local_weighted_partition (ρ : ℝ) {N : ℕ} (hN : 1 ≤ N) (ε : ℝ)
    (k : ℕ × ℕ) (f : ℕ × ℕ → ℝ) :
    (∑ p ∈ motherCell ρ N ε k, goldbachG12NormalizedCoefficient N p.1 * f p) =
    (∑ p ∈ safe ρ N ε k, goldbachG12NormalizedCoefficient N p.1 * f p) +
      ∑ p ∈ boundaryCell ρ N ε k, goldbachG12NormalizedCoefficient N p.1 * f p := by
  obtain ⟨hd,he⟩ := local_partition ρ hN ε k
  rw [← he, sum_union hd]

/-- An exact three-way ledger: cutoff slice, safe rectangles, and unpaid boundary. -/
theorem refined_weighted_partition {ρ : ℝ} (hρ : 1 < ρ) {N : ℕ} (hN : 1 ≤ N)
    (ε : ℝ) (f : ℕ × ℕ → ℝ) :
    (400 * ∑ p ∈ G12FlexibleRectangle.mother N ε,
      goldbachG12NormalizedCoefficient N p.1 * f p) =
    (400 * ∑ p ∈ cutoffSlice N ε, goldbachG12NormalizedCoefficient N p.1 * f p) +
    400 * ∑ k ∈ indices ρ N,
      ((∑ p ∈ safe ρ N ε k, goldbachG12NormalizedCoefficient N p.1 * f p) +
        ∑ p ∈ boundaryCell ρ N ε k, goldbachG12NormalizedCoefficient N p.1 * f p) := by
  rw [weighted_partition hρ N ε f]
  congr 2
  apply sum_congr rfl
  intro k _
  exact local_weighted_partition ρ hN ε k f

/-- Only the large-N source-scale gate remains; active long coordinates are real. -/
theorem mother_long_scale {N m r : ℕ} {ε : ℝ}
    (hp : (m,r) ∈ G12FlexibleRectangle.mother N ε) :
    (N : ℝ)^(4/53 : ℝ) ≤ (m : ℝ) := by
  exact (goldbachG12ActiveProductSupport_data (mem_product.mp (mem_filter.mp hp).1).1).2.2.2.1

/-- Equality at the high real cutoff is excluded even if the cutoff is prime. -/
theorem high_endpoint_excluded {N m r : ℕ} {ε : ℝ}
    (hr : (r : ℝ) = (N : ℝ)^(1/10 : ℝ)) :
    (m,r) ∉ G12FlexibleRectangle.mother N ε := by
  intro h
  have hh := (mem_filter.mp h).2.2.2.2.2.2.2
  change (r : ℝ) < (N : ℝ)^(1/10 : ℝ) at hh
  linarith

/-- The retained slice has precisely its literal mother predicate. -/
theorem cutoffSlice_iff (N m r : ℕ) (ε : ℝ) :
    (m,r) ∈ cutoffSlice N ε ↔
      (m,r) ∈ G12FlexibleRectangle.mother N ε ∧ r = lowCut N := by
  exact mem_filter


theorem short_dyadic {ρ : ℝ} (hρ : 1 < ρ) (hu : ρ ≤ 3/2) (N : ℕ) (k : ℕ × ℕ)
    (hT : 3 ≤ shortLower ρ N k) : shortUpper ρ N k ≤ 2 * shortLower ρ N k := by
  exact clipped_dyadic hρ hu (lowCut N) (highCut N) k.2 hT

theorem long_dyadic {ρ : ℝ} (hρ : 1 < ρ) (hu : ρ ≤ 3/2) (N : ℕ) (k : ℕ × ℕ)
    (hM : 3 ≤ longLower ρ k) : longUpper ρ N k ≤ 2 * longLower ρ k := by
  exact clipped_dyadic hρ hu 0 (N-1) k.1 hM

theorem occupied_endpoint_order {ρ : ℝ} {N : ℕ} {k p : ℕ × ℕ}
    (hp : p ∈ box ρ N k) :
    longLower ρ k < longUpper ρ N k ∧ shortLower ρ N k < shortUpper ρ N k := by
  obtain ⟨hm,hr⟩ := mem_product.mp hp
  exact ⟨(mem_Ioc.mp hm).1.trans_le (mem_Ioc.mp hm).2,
    (mem_Ioc.mp hr).1.trans_le (mem_Ioc.mp hr).2⟩

/-- A high endpoint in the original fibre stays in the high half, with no
assumption that the endpoint is composite. -/
theorem original_high_endpoint {N m r : ℕ} {ε : ℝ}
    (hf : r ∈ goldbachG11ProductFirstPrimeFiber N ε ((N : ℝ)^(4/53 : ℝ)) m)
    (hr : (r : ℝ) = (N : ℝ)^(1/10 : ℝ)) :
    r ∈ (goldbachG11ProductFirstPrimeFiber N ε ((N : ℝ)^(4/53 : ℝ)) m).filter
      (fun r : ℕ => (N : ℝ)^(1/10 : ℝ) ≤ (r : ℝ)) := by
  exact mem_filter.mpr ⟨hf,hr.ge⟩

/-- Full original count, retaining both the slice and all three safety failures. -/
theorem original_low_safe_partition {ρ : ℝ} (hρ : 1 < ρ) {N : ℕ} (hN : 1 ≤ N)
    (ε : ℝ) :
    (∑ m ∈ goldbachG12ActiveProductSupport N,
      (goldbachG12ProductCoefficient N ((N : ℝ)^(4/53 : ℝ))
        ((N : ℝ)^(4/33 : ℝ)) ((N : ℝ)^(3/11 : ℝ)) m : ℝ) *
      (((goldbachG11ProductFirstPrimeFiber N ε ((N : ℝ)^(4/53 : ℝ)) m).filter
        (fun r : ℕ => (r : ℝ) < (N : ℝ)^(1/10 : ℝ))).card : ℝ)) =
    (400 * ∑ p ∈ cutoffSlice N ε, goldbachG12NormalizedCoefficient N p.1 *
      (if (N-p.2*p.1).Prime then (1 : ℝ) else 0)) +
    400 * ∑ k ∈ indices ρ N,
      ((∑ p ∈ safe ρ N ε k, goldbachG12NormalizedCoefficient N p.1 *
        (if (N-p.2*p.1).Prime then (1 : ℝ) else 0)) +
      ∑ p ∈ boundaryCell ρ N ε k, goldbachG12NormalizedCoefficient N p.1 *
        (if (N-p.2*p.1).Prime then (1 : ℝ) else 0)) := by
  rw [← G12LowRectangle.original_low_count]
  exact refined_weighted_partition hρ hN ε _

end G12FineGrid
