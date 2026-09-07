import MathlibNt.SieveTheory.LiLiuGoldbachG12BandOutput

noncomputable section
open Classical Finset
open scoped BigOperators
open MathlibNt.SieveTheory MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
open G12ClippedWindow G12FineGrid G12RoughBoundary
namespace G12BandOutput

/-- One global clipped window, independent of the number of grid cells. -/
def clip (N : ℕ) (ε : ℝ) (T V : ℕ → ℝ) (m : ℕ) : Finset ℕ :=
  window N (clampLower N ε T V) (clampUpper N ε V) m

def productLo (N : ℕ) (l : ℝ) (m : ℕ) : ℝ := l*N/m

def roughLo (a : ℝ) (m : ℕ) : ℝ := m.minFac/a

def top (N : ℕ) : ℕ → ℝ := goldbachG11PiLiHi N

theorem mem_clip (N m r : ℕ) (ε : ℝ) (T V : ℕ → ℝ) :
    r ∈ clip N ε T V m ↔ r ∈ goldbachG11LinkedPrimeWindow N ε m ∧
      T m < r ∧ (r : ℝ) ≤ V m := by
  rw [clip, clamp_window_eq_filter, mem_filter]

theorem product_clip_good_le (N : ℕ) (ε l u : ℝ) :
    goodMass N (goldbachG12NormalizedCoefficient N)
      (clampLower N ε (productLo N l) (productLo N u))
      (clampUpper N ε (productLo N u)) ≤ bandMass N ε l u := by
  unfold goodMass bandMass
  apply sum_le_sum
  intro m hm
  apply mul_le_mul_of_nonneg_left _ (goldbachG12NormalizedCoefficient_bounds N m).1
  apply Nat.cast_le.mpr
  apply card_le_card
  intro r hr
  obtain ⟨hr,hcop⟩ := mem_filter.mp hr
  obtain ⟨hw,hl,hu⟩ := (mem_clip N m r ε _ _).mp hr
  have hp := (mem_filter.mp hw).2.1
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (goldbachG12ActiveProductSupport_data hm).1
  exact mem_filter.mpr ⟨hw,hp.coprime_iff_not_dvd.mp hcop,
    (div_lt_iff₀ hm0).mp hl,(le_div_iff₀ hm0).mp hu⟩

theorem rough_clip_good_le (N : ℕ) (ε : ℝ) {a : ℝ} (ha : 0 < a) :
    goodMass N (goldbachG12NormalizedCoefficient N)
      (clampLower N ε (roughLo a) (top N)) (clampUpper N ε (top N)) ≤
        nearWindowMass N ε a := by
  unfold goodMass nearWindowMass
  apply sum_le_sum
  intro m _
  apply mul_le_mul_of_nonneg_left _ (goldbachG12NormalizedCoefficient_bounds N m).1
  apply Nat.cast_le.mpr
  apply card_le_card
  intro r hr
  obtain ⟨hr,hcop⟩ := mem_filter.mp hr
  obtain ⟨hw,hl,_⟩ := (mem_clip N m r ε _ _).mp hr
  have hp := (mem_filter.mp hw).2.1
  exact mem_filter.mpr ⟨hw,hp.coprime_iff_not_dvd.mp hcop,
    by simpa only [mul_comm] using ((div_lt_iff₀ ha).mp hl).le⟩

/-- Literal pair carrier; it does not identify distinct body representations. -/
def pairs (N : ℕ) (ε : ℝ) (T V : ℕ → ℝ) : Finset (ℕ × ℕ) :=
  ((goldbachG12ActiveProductSupport N) ×ˢ range (N+1)).filter
    (fun p => p.2 ∈ clip N ε T V p.1)

theorem mem_pairs (N : ℕ) (ε : ℝ) (T V : ℕ → ℝ) (p : ℕ × ℕ) :
    p ∈ pairs N ε T V ↔ p.1 ∈ goldbachG12ActiveProductSupport N ∧
      p.2 ∈ clip N ε T V p.1 := by
  constructor
  · intro hp
    exact ⟨(mem_product.mp (mem_filter.mp hp).1).1,(mem_filter.mp hp).2⟩
  · rintro ⟨hm,hr⟩
    exact mem_filter.mpr ⟨mem_product.mpr ⟨hm,(mem_filter.mp hr).1⟩,hr⟩

def atom (N : ℕ) (p : ℕ × ℕ) : ℝ :=
  goldbachG12NormalizedCoefficient N p.1 * (if (N-p.2*p.1).Prime then 1 else 0)

theorem atom_nonneg (N : ℕ) (p : ℕ × ℕ) : 0 ≤ atom N p :=
  mul_nonneg (goldbachG12NormalizedCoefficient_bounds N p.1).1 (prime_indicator_nonneg N p.1 p.2)

theorem pairs_output_eq (N : ℕ) (ε : ℝ) (T V : ℕ → ℝ) :
    400 * ∑ p ∈ pairs N ε T V, atom N p =
      primeOutput N (goldbachG12NormalizedCoefficient N)
        (clampLower N ε T V) (clampUpper N ε V) := by
  rw [primeOutput_eq_indicator]
  congr 1
  rw [pairs, sum_filter, sum_product]
  apply sum_congr rfl
  intro m _
  have he : (range (N+1)).filter (fun r => r ∈ clip N ε T V m) = clip N ε T V m := by
    ext r
    simp only [mem_filter]
    exact ⟨fun h => h.2,fun h => ⟨(mem_filter.mp h).1,h⟩⟩
  rw [← sum_filter,he,mul_sum]
  rfl

/-- The three global source pair sets, with a genuinely strict rough lower endpoint. -/
def cover (N : ℕ) (ε a : ℝ) : Finset (ℕ × ℕ) :=
  (pairs N ε (productLo N (ε/a)) (productLo N (a*ε)) ∪
    pairs N ε (productLo N (1/a)) (productLo N 1)) ∪
      pairs N ε (roughLo a) (top N)

theorem band_mem_pairs {N : ℕ} {ε l u : ℝ} {p : ℕ × ℕ}
    (hm : p.1 ∈ goldbachG12ActiveProductSupport N) (hr : p.2 ∈ bandWindow N ε l u p.1) :
    p ∈ pairs N ε (productLo N l) (productLo N u) := by
  obtain ⟨hw,_,hl,hu⟩ := mem_filter.mp hr
  have hm0 : (0 : ℝ) < p.1 := by exact_mod_cast (goldbachG12ActiveProductSupport_data hm).1
  exact (mem_pairs N ε _ _ p).mpr ⟨hm,(mem_clip N p.1 p.2 ε _ _).mpr
    ⟨hw,(div_lt_iff₀ hm0).mpr hl,(le_div_iff₀ hm0).mpr hu⟩⟩

/-- Strict containment retains q=r; no endpoint atom is deleted. -/
theorem rough_mem_pairs {ρ a ε : ℝ} {N : ℕ}
    (hN : 1 ≤ N) (ha : 0 < a)
    (hmesh : ∀ k ∈ indices ρ N,
      (shortUpper ρ N k : ℝ) ≤ a*(shortLower ρ N k : ℝ))
    {p : ℕ × ℕ} (hp : p ∈ roughBoundary ρ N ε) :
    p ∈ pairs N ε (roughLo a) (top N) := by
  obtain ⟨k,hk,hp⟩ := mem_biUnion.mp hp
  obtain ⟨hp,hfail⟩ := mem_filter.mp hp
  have hm := (mem_product.mp (mem_filter.mp (mem_filter.mp hp).1).1).1
  have hw := ((motherCell_window_iff ρ hN ε k hm).mp hp).2
  obtain ⟨hrange,hrp,_,hlo,hhi⟩ := mem_filter.mp hw
  obtain ⟨hlo,hTr⟩ := max_lt_iff.mp hlo
  obtain ⟨hhi,_⟩ := le_min_iff.mp hhi
  have hrW : p.2 ∈ goldbachG11LinkedPrimeWindow N ε p.1 :=
    mem_filter.mpr ⟨hrange,hrp,hlo,hhi⟩
  have hfR : (p.1.minFac : ℝ) < shortUpper ρ N k := by exact_mod_cast hfail
  have hnear : (p.1.minFac : ℝ) < a*p.2 :=
    (hfR.trans_le (hmesh k hk)).trans (mul_lt_mul_of_pos_left hTr ha)
  exact (mem_pairs N ε _ _ p).mpr ⟨hm,(mem_clip N p.1 p.2 ε _ _).mpr
    ⟨hrW,(div_lt_iff₀ ha).mpr (by simpa only [mul_comm] using hnear),hhi⟩⟩

theorem boundary_subset_cover {ρ a ε : ℝ} {N : ℕ}
    (hN : 1 ≤ N) (ha : 1 < a) (he : 0 < ε)
    (hmesh : ∀ k ∈ indices ρ N,
      (shortUpper ρ N k : ℝ) ≤ a*(shortLower ρ N k : ℝ)) :
    (indices ρ N).biUnion (boundaryCell ρ N ε) ⊆ cover N ε a := by
  rw [boundary_union_decomposition]
  intro p hp
  rcases mem_union.mp hp with hp | hp
  · obtain ⟨hm,hr | hr⟩ := productBoundary_in_bands hN ha he hmesh hp
    · exact mem_union_left _ (mem_union_left _ (band_mem_pairs hm hr))
    · exact mem_union_left _ (mem_union_right _ (band_mem_pairs hm hr))
  · exact mem_union_right _ (rough_mem_pairs hN (by linarith) hmesh hp)

end G12BandOutput
