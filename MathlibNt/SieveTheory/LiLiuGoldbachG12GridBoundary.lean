import MathlibNt.SieveTheory.LiLiuGoldbachG12FineGridSafety
import MathlibNt.SieveTheory.LiLiuGoldbachG12ThinIntegralBudget

noncomputable section
open Classical Finset
open scoped BigOperators
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

namespace G12FineGrid


/-- Original PiLi endpoints clipped at the actual short-cell endpoints.
Coprimality is retained on the short side, never asserted to inherit SW. -/
def boundaryWindow (ρ : ℝ) (N : ℕ) (ε : ℝ) (k : ℕ × ℕ) (m : ℕ) : Finset ℕ :=
  (range (N+1)).filter fun r => r.Prime ∧ r.Coprime N ∧
    max (goldbachG11PiLiLo N ε m) (shortLower ρ N k : ℝ) < r ∧
    (r : ℝ) ≤ min (goldbachG11PiLiHi N m) (shortUpper ρ N k : ℝ)


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


end G12FineGrid
