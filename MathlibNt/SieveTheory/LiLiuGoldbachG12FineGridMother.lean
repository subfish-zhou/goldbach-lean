import MathlibNt.SieveTheory.LiLiuGoldbachG12FineGrid

noncomputable section
open Classical Finset
open scoped BigOperators
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

namespace G12FineGrid

/-- The lower cutoff is not deleted: its integer slice is retained separately. -/
def lowCut (N : ℕ) : ℕ := Nat.ceil ((N : ℝ)^(4/53 : ℝ))
def highCut (N : ℕ) : ℕ := Nat.ceil ((N : ℝ)^(1/10 : ℝ)) - 1

def indices (ρ : ℝ) (N : ℕ) : Finset (ℕ × ℕ) := range (count ρ N) ×ˢ range (count ρ N)

/-- These are coordinate boxes, not safe rectangles. -/
def box (ρ : ℝ) (N : ℕ) (k : ℕ × ℕ) : Finset (ℕ × ℕ) :=
  clipped ρ 0 (N-1) k.1 ×ˢ clipped ρ (lowCut N) (highCut N) k.2

def motherCell (ρ : ℝ) (N : ℕ) (ε : ℝ) (k : ℕ × ℕ) : Finset (ℕ × ℕ) :=
  (G12FlexibleRectangle.mother N ε).filter (· ∈ box ρ N k)

def cutoffSlice (N : ℕ) (ε : ℝ) : Finset (ℕ × ℕ) :=
  (G12FlexibleRectangle.mother N ε).filter (fun p => p.2 = lowCut N)

theorem box_unique {ρ : ℝ} (hρ : 1 < ρ) {N : ℕ} {k l p : ℕ × ℕ}
    (hk : p ∈ box ρ N k) (hl : p ∈ box ρ N l) : k = l := by
  obtain ⟨hkm, hkr⟩ := mem_product.mp hk
  obtain ⟨hlm, hlr⟩ := mem_product.mp hl
  exact Prod.ext (unique hρ ((mem_clipped _ _ _ _ _).mp hkm).2
    ((mem_clipped _ _ _ _ _).mp hlm).2)
    (unique hρ ((mem_clipped _ _ _ _ _).mp hkr).2
    ((mem_clipped _ _ _ _ _).mp hlr).2)

theorem box_disjoint {ρ : ℝ} (hρ : 1 < ρ) (N : ℕ) {k l : ℕ × ℕ} (hkl : k ≠ l) :
    Disjoint (box ρ N k) (box ρ N l) := by
  exact disjoint_left.mpr (fun _ hk hl => hkl (box_unique hρ hk hl))

theorem cell_disjoint {ρ : ℝ} (hρ : 1 < ρ) (N : ℕ) (ε : ℝ)
    {k l : ℕ × ℕ} (hkl : k ≠ l) : Disjoint (motherCell ρ N ε k) (motherCell ρ N ε l) := by
  exact disjoint_left.mpr (fun _ hk hl => hkl
    (box_unique hρ (mem_filter.mp hk).2 (mem_filter.mp hl).2))

/-- Actual mother coordinates: strict m<N and r<N, and the exact rounded cutoffs. -/
theorem mother_coordinates {N m r : ℕ} {ε : ℝ}
    (h : (m,r) ∈ G12FlexibleRectangle.mother N ε) :
    1 ≤ m ∧ m < N ∧ 1 ≤ r ∧ r < N ∧ lowCut N ≤ r ∧ r ≤ highCut N := by
  obtain ⟨hb,hp,_,hz,_,_,hmr,hrhi⟩ := mem_filter.mp h
  have hm0 := (goldbachG12ActiveProductSupport_data (mem_product.mp hb).1).1
  have hr0 := hp.pos
  have hmN := (Nat.le_mul_of_pos_left m hr0).trans_lt hmr
  have hrN := (Nat.le_mul_of_pos_right r hm0).trans_lt hmr
  have hlo : lowCut N ≤ r := Nat.ceil_le.mpr hz.le
  have hhi := Nat.lt_ceil.mpr hrhi
  refine ⟨by omega, hmN, by omega, hrN, hlo, ?_⟩
  unfold highCut
  omega

/-- Every nonslice mother atom is in exactly one finite coordinate box. -/
theorem mother_cover {ρ : ℝ} (hρ : 1 < ρ) {N : ℕ} {ε : ℝ} {p : ℕ × ℕ}
    (hp : p ∈ G12FlexibleRectangle.mother N ε) (hs : p.2 ≠ lowCut N) :
    ∃! k, k ∈ indices ρ N ∧ p ∈ motherCell ρ N ε k := by
  obtain ⟨hm0,hmN,hr0,hrN,hrL,hrH⟩ := mother_coordinates hp
  obtain ⟨i, ⟨hi, hmi⟩, _⟩ := cover hρ hm0 hmN.le
  obtain ⟨j, ⟨hj, hrj⟩, _⟩ := cover hρ hr0 hrN.le
  have hb : p ∈ box ρ N (i,j) := by
    apply mem_product.mpr
    constructor
    · exact (mem_clipped _ _ _ _ _).mpr ⟨mem_Ioc.mpr ⟨by omega, by omega⟩, hmi⟩
    · exact (mem_clipped _ _ _ _ _).mpr ⟨mem_Ioc.mpr ⟨by omega, hrH⟩, hrj⟩
  refine ⟨(i,j), ⟨mem_product.mpr ⟨mem_range.mpr hi, mem_range.mpr hj⟩,
    mem_filter.mpr ⟨hp,hb⟩⟩, ?_⟩
  intro k hk
  exact box_unique hρ (mem_filter.mp hk.2).2 hb

theorem slice_disjoint (ρ : ℝ) (N : ℕ) (ε : ℝ) (k : ℕ × ℕ) :
    Disjoint (cutoffSlice N ε) (motherCell ρ N ε k) := by
  apply disjoint_left.mpr
  intro p hs hk
  have he := (mem_filter.mp hs).2
  have hr := (mem_product.mp (mem_filter.mp hk).2).2
  have hh := (mem_Ioc.mp ((mem_clipped _ _ _ _ _).mp hr).1).1
  change p.2 = lowCut N at he
  omega

/-- Exact finite decomposition, with the cutoff slice explicitly present. -/
theorem mother_partition {ρ : ℝ} (hρ : 1 < ρ) (N : ℕ) (ε : ℝ) :
    cutoffSlice N ε ∪ (indices ρ N).biUnion (motherCell ρ N ε) =
      G12FlexibleRectangle.mother N ε := by
  ext p
  constructor
  · intro h
    rcases mem_union.mp h with hs | hg
    · exact (mem_filter.mp hs).1
    · obtain ⟨k, _, hk⟩ := mem_biUnion.mp hg
      exact (mem_filter.mp hk).1
  · intro hp
    by_cases hs : p.2 = lowCut N
    · exact mem_union_left _ (mem_filter.mpr ⟨hp,hs⟩)
    · obtain ⟨k, ⟨hk,hpk⟩, _⟩ := mother_cover hρ hp hs
      exact mem_union_right _ (mem_biUnion.mpr ⟨k,hk,hpk⟩)

/-- The same physical coefficient and body multiplicity 400 survive the mesh. -/
theorem weighted_partition {ρ : ℝ} (hρ : 1 < ρ) (N : ℕ) (ε : ℝ) (f : ℕ × ℕ → ℝ) :
    (400 * ∑ p ∈ G12FlexibleRectangle.mother N ε,
      goldbachG12NormalizedCoefficient N p.1 * f p) =
    (400 * ∑ p ∈ cutoffSlice N ε, goldbachG12NormalizedCoefficient N p.1 * f p) +
      400 * ∑ k ∈ indices ρ N, ∑ p ∈ motherCell ρ N ε k,
        goldbachG12NormalizedCoefficient N p.1 * f p := by
  have hd : Disjoint (cutoffSlice N ε) ((indices ρ N).biUnion (motherCell ρ N ε)) := by
    apply disjoint_left.mpr
    intro p hs hg
    obtain ⟨k,_,hk⟩ := mem_biUnion.mp hg
    exact disjoint_left.mp (slice_disjoint ρ N ε k) hs hk
  have hpair : (↑(indices ρ N) : Set (ℕ × ℕ)).PairwiseDisjoint (motherCell ρ N ε) := by
    intro k _ l _ hkl
    exact cell_disjoint hρ N ε hkl
  rw [← mother_partition hρ N ε, sum_union hd, sum_biUnion hpair, mul_add]

/-- Literal original low fibre count, not a replacement coefficient. -/
theorem original_low_partition {ρ : ℝ} (hρ : 1 < ρ) (N : ℕ) (ε : ℝ) :
    (∑ m ∈ goldbachG12ActiveProductSupport N,
      (goldbachG12ProductCoefficient N ((N : ℝ)^(4/53 : ℝ))
        ((N : ℝ)^(4/33 : ℝ)) ((N : ℝ)^(3/11 : ℝ)) m : ℝ) *
      (((goldbachG11ProductFirstPrimeFiber N ε ((N : ℝ)^(4/53 : ℝ)) m).filter
        (fun r : ℕ => (r : ℝ) < (N : ℝ)^(1/10 : ℝ))).card : ℝ)) =
    (400 * ∑ p ∈ cutoffSlice N ε, goldbachG12NormalizedCoefficient N p.1 *
      (if (N-p.2*p.1).Prime then (1 : ℝ) else 0)) +
    400 * ∑ k ∈ indices ρ N, ∑ p ∈ motherCell ρ N ε k,
      goldbachG12NormalizedCoefficient N p.1 *
        (if (N-p.2*p.1).Prime then (1 : ℝ) else 0) := by
  rw [← G12LowRectangle.original_low_count]
  exact weighted_partition hρ N ε _

end G12FineGrid
