import MathlibNt.SieveTheory.LiLiuGoldbachG12FineGridSafety
import MathlibNt.SieveTheory.LiLiuGoldbachG12LocalScalePackage

noncomputable section
open Classical Finset Filter
open scoped BigOperators Topology
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

namespace G12FineGrid

/-- A large occupied long coordinate forces the actual rounded lower endpoint up. -/
theorem occupied_long_lower {ρ : ℝ} (hρ : 1 < ρ) (hu : ρ ≤ 3/2)
    {N : ℕ} {ε : ℝ} {k p : ℕ × ℕ}
    (hp : p ∈ motherCell ρ N ε k) (hsize : (6 : ℝ) ≤ (N : ℝ)^(4/53 : ℝ)) :
    3 ≤ longLower ρ k := by
  have hm := mother_long_scale (mem_filter.mp hp).1
  have hb := (mem_product.mp (mem_filter.mp hp).2).1
  have hupper : p.1 ≤ longUpper ρ N k := (mem_Ioc.mp hb).2
  have hw : (longUpper ρ N k : ℝ) ≤ ρ * ((longLower ρ k : ℝ) + 1) := by
    simpa only [longUpper, longLower, Nat.cast_min, Nat.cast_max] using
      clipped_width hρ 0 (N-1) k.1
  have hh : (p.1 : ℝ) ≤ longUpper ρ N k := by exact_mod_cast hupper
  by_contra hn
  have hn' : (longLower ρ k : ℝ) ≤ 2 := by exact_mod_cast (show longLower ρ k ≤ 2 by omega)
  have hz : (0 : ℝ) ≤ longLower ρ k := Nat.cast_nonneg _
  nlinarith

/-- Geometry of the actual clipped endpoints; this is not a safety assertion. -/
structure SourceGeometry (ρ : ℝ) (N : ℕ) (ε : ℝ) (k : ℕ × ℕ) : Prop where
  long_three : 3 ≤ longLower ρ k
  short_three : 3 ≤ shortLower ρ N k
  long_order : longLower ρ k ≤ longUpper ρ N k
  long_twice : longUpper ρ N k ≤ 2 * longLower ρ k
  short_order : shortLower ρ N k ≤ shortUpper ρ N k
  short_twice : shortUpper ρ N k ≤ 2 * shortLower ρ N k
  source_lower : (N : ℝ)^(4/53 : ℝ) ≤ shortLower ρ N k
  source_upper : (shortUpper ρ N k : ℝ) < (N : ℝ)^(1/10 : ℝ)
  scale_lower : ε * N ≤ 4 * (longLower ρ k : ℝ) * shortLower ρ N k
  scale_upper : 4 * (longLower ρ k : ℝ) * shortLower ρ N k ≤ 4 * N

/-- One cutoff precedes every mesh, prefix and occupied mother cell. -/
theorem uniform_occupied_geometry :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ ρ ε : ℝ,
      1 < ρ → ρ ≤ 3/2 → ∀ k : ℕ × ℕ,
      (motherCell ρ N ε k).Nonempty → SourceGeometry ρ N ε k := by
  have hg : ∀ᶠ N : ℕ in atTop, (6 : ℝ) ≤ (N : ℝ)^(4/53 : ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 4/53)).comp
      tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop _)
  obtain ⟨A,hA⟩ := eventually_atTop.mp hg
  refine ⟨max 4 A, le_max_left _ _, ?_⟩
  intro N hN ρ ε hρ hu k hk
  obtain ⟨⟨m,r⟩,hp⟩ := hk
  have hs := hA N (by omega)
  have hM := occupied_long_lower hρ hu hp hs
  have hTl := short_lower_valid ρ N k
  have hT : 3 ≤ shortLower ρ N k := by
    have hh : (3 : ℝ) ≤ shortLower ρ N k := by linarith
    exact_mod_cast hh
  have hUd := long_dyadic hρ hu N k hM
  have hVd := short_dyadic hρ hu N k hT
  have hb := (mem_filter.mp hp).2
  have ho := occupied_endpoint_order hb
  obtain ⟨hm,hr⟩ := mem_product.mp hb
  have hm' : longLower ρ k < m ∧ m ≤ longUpper ρ N k := mem_Ioc.mp hm
  have hr' : shortLower ρ N k < r ∧ r ≤ shortUpper ρ N k := mem_Ioc.mp hr
  obtain ⟨_,_,_,_,_,he,hn,_⟩ := mem_filter.mp (mem_filter.mp hp).1
  have hmr : (r : ℝ) * m < N := by exact_mod_cast hn
  have hmlo : (longLower ρ k : ℝ) ≤ m := by exact_mod_cast hm'.1.le
  have hrlo : (shortLower ρ N k : ℝ) ≤ r := by exact_mod_cast hr'.1.le
  have hmhi : (m : ℝ) ≤ 2 * longLower ρ k := by exact_mod_cast hm'.2.trans hUd
  have hrhi : (r : ℝ) ≤ 2 * shortLower ρ N k := by exact_mod_cast hr'.2.trans hVd
  refine ⟨hM,hT,ho.1.le,hUd,ho.2.le,hVd,hTl,
    short_upper_valid ρ (by omega) k,?_,?_⟩
  · have hp' := mul_le_mul hrhi hmhi (Nat.cast_nonneg m)
      (show (0 : ℝ) ≤ 2 * shortLower ρ N k by positivity)
    change ε * N < (r : ℝ) * m at he
    nlinarith
  · have hp' := mul_le_mul hmlo hrlo (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    nlinarith

/-- The actual atom supplies the source prime, not an artificial endpoint. -/
theorem occupied_atom_coordinates {ρ ε : ℝ} {N : ℕ} {k p : ℕ × ℕ}
    (hp : p ∈ motherCell ρ N ε k) :
    shortLower ρ N k < p.2 ∧ p.2 ≤ shortUpper ρ N k ∧
      (N : ℝ)^(4/53 : ℝ) ≤ (p.2 : ℝ) ∧
      (N : ℝ)^(4/53 : ℝ) ≤ (p.1 : ℝ) := by
  have hr : shortLower ρ N k < p.2 ∧ p.2 ≤ shortUpper ρ N k :=
    mem_Ioc.mp (mem_product.mp (mem_filter.mp hp).2).2
  exact ⟨hr.1,hr.2,(short_lower_valid ρ N k).trans (by exact_mod_cast hr.1.le),
    mother_long_scale (mem_filter.mp hp).1⟩

end G12FineGrid
