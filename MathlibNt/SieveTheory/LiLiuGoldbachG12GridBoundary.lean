import MathlibNt.SieveTheory.LiLiuGoldbachG12FineGridSafety
import MathlibNt.SieveTheory.LiLiuGoldbachG12ThinIntegralBudget

noncomputable section
open Classical Finset
open scoped BigOperators
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

namespace G12FineGrid

/-- The actual boundary mask depends only on the long coordinate. -/
def boundaryMask (ρ : ℝ) (N : ℕ) (ε : ℝ) (k : ℕ × ℕ) (m : ℕ) : Prop :=
  m ∈ Ioc (longLower ρ k) (longUpper ρ N k) ∧
    ¬ G12FlexibleRectangle.longOK N ε (shortLower ρ N k) (shortUpper ρ N k) m

/-- The original normalized coefficient, with only a long-variable mask. -/
def boundaryCoefficient (ρ : ℝ) (N : ℕ) (ε : ℝ) (k : ℕ × ℕ) (m : ℕ) : ℝ :=
  if boundaryMask ρ N ε k m then goldbachG12NormalizedCoefficient N m else 0

/-- Original PiLi endpoints clipped at the actual short-cell endpoints.
Coprimality is retained on the short side, never asserted to inherit SW. -/
def boundaryWindow (ρ : ℝ) (N : ℕ) (ε : ℝ) (k : ℕ × ℕ) (m : ℕ) : Finset ℕ :=
  (range (N+1)).filter fun r => r.Prime ∧ r.Coprime N ∧
    max (goldbachG11PiLiLo N ε m) (shortLower ρ N k : ℝ) < r ∧
    (r : ℝ) ≤ min (goldbachG11PiLiHi N m) (shortUpper ρ N k : ℝ)

theorem boundaryMask_iff (ρ : ℝ) (N : ℕ) (ε : ℝ) (k : ℕ × ℕ) (m r : ℕ)
    (hp : (m,r) ∈ motherCell ρ N ε k) :
    (m,r) ∈ boundaryCell ρ N ε k ↔ boundaryMask ρ N ε k m := by
  have hm := (mem_product.mp (mem_filter.mp (mem_filter.mp hp).1).1).1
  have hl : m ∈ Ioc (longLower ρ k) (longUpper ρ N k) :=
    (mem_product.mp (mem_filter.mp hp).2).1
  rw [boundaryCell_iff ρ N ε k m r hp]
  simp only [boundaryMask, hl, true_and, G12FlexibleRectangle.longOK, hm,
    true_and, not_and_or, not_le, not_lt]

theorem boundaryCoefficient_bounds (ρ : ℝ) (N : ℕ) (ε : ℝ) (k : ℕ × ℕ) (m : ℕ) :
    0 ≤ boundaryCoefficient ρ N ε k m ∧ boundaryCoefficient ρ N ε k m ≤ 1 := by
  unfold boundaryCoefficient
  split_ifs
  · exact goldbachG12NormalizedCoefficient_bounds N m
  · norm_num

/-- Coprimality removes the apparent closed product endpoint in PiLiHi. -/
theorem motherCell_window_iff (ρ : ℝ) {N : ℕ} (hN : 1 ≤ N) (ε : ℝ)
    (k : ℕ × ℕ) {m r : ℕ} (hm : m ∈ goldbachG12ActiveProductSupport N) :
    (m,r) ∈ motherCell ρ N ε k ↔
      m ∈ Ioc (longLower ρ k) (longUpper ρ N k) ∧
        r ∈ boundaryWindow ρ N ε k m := by
  have hm0 : (0 : ℝ) < m := by
    exact_mod_cast (goldbachG12ActiveProductSupport_data hm).1
  constructor
  · intro hp
    obtain ⟨hl, hr⟩ := mem_product.mp (mem_filter.mp hp).2
    obtain ⟨hb, hp, hc, hz, hq, he, hn, _⟩ := mem_filter.mp (mem_filter.mp hp).1
    have hrI : r ∈ Ioc (shortLower ρ N k) (shortUpper ρ N k) := hr
    have hTr : (shortLower ρ N k : ℝ) < r := by exact_mod_cast (mem_Ioc.mp hrI).1
    have hrV : (r : ℝ) ≤ shortUpper ρ N k := by exact_mod_cast (mem_Ioc.mp hrI).2
    refine ⟨hl, mem_filter.mpr ⟨(mem_product.mp hb).2, hp, hc, ?_, ?_⟩⟩
    · exact max_lt ((min_le_right _ _).trans_lt
        (max_lt hz ((div_lt_iff₀ hm0).mpr he))) hTr
    · exact le_min (le_min (by exact_mod_cast hq)
        ((le_div_iff₀ hm0).mpr (by exact_mod_cast hn.le))) hrV
  · rintro ⟨hl, hr⟩
    obtain ⟨hrange, hp, hc, hlo, hhi⟩ := mem_filter.mp hr
    obtain ⟨hlo,hTr⟩ := max_lt_iff.mp hlo
    obtain ⟨hhi,hrV⟩ := le_min_iff.mp hhi
    have hmax : max ((N : ℝ)^(4/53 : ℝ)) (ε*N/m) < (r : ℝ) := by
      rcases min_lt_iff.mp hlo with hh | hh
      · exact False.elim ((not_lt_of_ge hhi) hh)
      · exact hh
    obtain ⟨hz,he⟩ := max_lt_iff.mp hmax
    obtain ⟨hq,hn⟩ := le_min_iff.mp hhi
    have hn' : r*m ≤ N := by exact_mod_cast (le_div_iff₀ hm0).mp hn
    have hne : r*m ≠ N := by
      intro heq
      have hd : r ∣ N := heq ▸ dvd_mul_right r m
      exact hp.not_dvd_one (hc.gcd_eq_one ▸ Nat.dvd_gcd (dvd_refl r) hd)
    have hprod : r*m < N := lt_of_le_of_ne hn' hne
    have hrI : r ∈ Ioc (shortLower ρ N k) (shortUpper ρ N k) :=
      mem_Ioc.mpr ⟨by exact_mod_cast hTr, by exact_mod_cast hrV⟩
    refine mem_filter.mpr ⟨mem_filter.mpr ⟨mem_product.mpr ⟨hm,hrange⟩,
      hp,hc,hz,by exact_mod_cast hq,(div_lt_iff₀ hm0).mp he,hprod,
      hrV.trans_lt (short_upper_valid ρ hN k)⟩,mem_product.mpr ⟨hl,hrI⟩⟩

/-- Literal finite-set representation, with the original active support. -/
theorem boundaryCell_eq_masked_window (ρ : ℝ) {N : ℕ} (hN : 1 ≤ N) (ε : ℝ)
    (k : ℕ × ℕ) :
    boundaryCell ρ N ε k =
      ((goldbachG12ActiveProductSupport N) ×ˢ range (N+1)).filter
        (fun p => boundaryMask ρ N ε k p.1 ∧ p.2 ∈ boundaryWindow ρ N ε k p.1) := by
  ext ⟨m,r⟩
  constructor
  · intro hb
    have hp := (mem_sdiff.mp hb).1
    have hm := (mem_product.mp (mem_filter.mp (mem_filter.mp hp).1).1).1
    have hw := ((motherCell_window_iff ρ hN ε k hm).mp hp).2
    exact mem_filter.mpr ⟨mem_product.mpr ⟨hm,(mem_filter.mp hw).1⟩,
      (boundaryMask_iff ρ N ε k m r hp).mp hb,hw⟩
  · intro hb
    obtain ⟨hb,hmask,hw⟩ := mem_filter.mp hb
    have hp := (motherCell_window_iff ρ hN ε k (mem_product.mp hb).1).mpr ⟨hmask.1,hw⟩
    exact (boundaryMask_iff ρ N ε k m r hp).mpr hmask

/-- Exact weighted identity for any test: AP, coprimality, or output-prime.
No cancellation is lost and the physical coefficient is unchanged. -/
theorem boundaryCell_weighted_window (ρ : ℝ) {N : ℕ} (hN : 1 ≤ N) (ε : ℝ)
    (k : ℕ × ℕ) (f : ℕ → ℕ → ℝ) :
    (∑ p ∈ boundaryCell ρ N ε k, goldbachG12NormalizedCoefficient N p.1 * f p.1 p.2) =
      ∑ m ∈ goldbachG12ActiveProductSupport N, ∑ r ∈ boundaryWindow ρ N ε k m,
        boundaryCoefficient ρ N ε k m * f m r := by
  rw [boundaryCell_eq_masked_window ρ hN ε k, sum_filter, sum_product]
  apply sum_congr rfl
  intro m _
  rw [boundaryWindow, sum_filter]
  apply sum_congr rfl
  intro r hr
  have hh : r ∈ range (N+1) := hr
  by_cases hm : boundaryMask ρ N ε k m <;>
    simp [boundaryCoefficient, boundaryWindow, hm, hh]

end G12FineGrid
