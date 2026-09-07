import MathlibNt.SieveTheory.LiLiuGoldbachIntermediateSums

open scoped BigOperators
open Finset
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
noncomputable local instance (P : Prop) : Decidable P := Classical.propDecidable P

private theorem mem_goldbachHalfOpenPrimes {N p : ℕ} {z y : ℝ} :
    p ∈ goldbachHalfOpenPrimes N z y ↔
      p.Prime ∧ Nat.Coprime p N ∧ z ≤ (p : ℝ) ∧ (p : ℝ) < y := by
  simp only [goldbachHalfOpenPrimes, Finset.mem_filter, mem_siftingPrimes]
  constructor
  · rintro ⟨⟨hp, hpy, hpN⟩, hzp⟩
    exact ⟨hp, hp.coprime_iff_not_dvd.mpr hpN, hzp, hpy⟩
  · rintro ⟨hp, hpN, hzp, hpy⟩
    exact ⟨⟨hp, hpy, hp.coprime_iff_not_dvd.mp hpN⟩, hzp⟩

 theorem goldbachS4Pairs_low_eq {N : ℕ} {z y : ℝ}
    (hy : 2 ≤ y) (hyN : y ^ 3 ≤ (N : ℝ)) :
    (goldbachS4Pairs N z).filter (fun rs => (rs.2 : ℝ) < y) =
      ((goldbachHalfOpenPrimes N z y) ×ˢ (goldbachHalfOpenPrimes N z y)).filter
        (fun rs => rs.1 ≤ rs.2) := by
  have hy0 : 0 ≤ y := by linarith
  have hyN' : y ≤ (N : ℝ) := by
    have hsq : 1 ≤ y ^ 2 := by nlinarith
    have hmul := mul_le_mul_of_nonneg_left hsq hy0
    nlinarith
  ext rs
  rcases rs with ⟨r,s⟩
  simp only [Finset.mem_filter, Finset.mem_product]
  constructor
  · rintro ⟨hmem, hsy⟩
    have hp := (Finset.mem_filter.mp hmem).2
    rcases hp with ⟨hr, hs, hcop, hzr, hrs, hbound⟩
    have hrsR : (r : ℝ) ≤ s := by exact_mod_cast hrs
    have hc := Nat.coprime_mul_iff_left.mp hcop
    exact ⟨⟨mem_goldbachHalfOpenPrimes.mpr ⟨hr,hc.1,hzr,hrsR.trans_lt hsy⟩,
      mem_goldbachHalfOpenPrimes.mpr ⟨hs,hc.2,hzr.trans hrsR,hsy⟩⟩,hrs⟩
  · rintro ⟨⟨hr,hs⟩,hrs⟩
    rcases mem_goldbachHalfOpenPrimes.mp hr with ⟨hrP,hrN,hzr,hry⟩
    rcases mem_goldbachHalfOpenPrimes.mp hs with ⟨hsP,hsN,hzs,hsy⟩
    have hrle : r ≤ N := by exact_mod_cast (hry.le.trans hyN')
    have hsle : s ≤ N := by exact_mod_cast (hsy.le.trans hyN')
    have hprodR : (r : ℝ) * (s : ℝ) ^ 2 ≤ y ^ 3 := by
      calc
        (r : ℝ) * (s : ℝ)^2 ≤ y * y^2 := by gcongr
        _ = y^3 := by ring
    have hprod : r * s ^ 2 ≤ N := by exact_mod_cast (hprodR.trans hyN)
    refine ⟨?_, hsy⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr (by omega),Finset.mem_range.mpr (by omega)⟩,
      hrP,hsP,Nat.coprime_mul_iff_left.mpr ⟨hrN,hsN⟩,hzr,hrs,hprod⟩

 theorem goldbachS4_low_sum_eq_V (A : Finset ℕ) (N : ℕ) {z y : ℝ}
    (hy : 2 ≤ y) (hyN : y ^ 3 ≤ (N : ℝ)) :
    (∑ rs ∈ (goldbachS4Pairs N z).filter (fun rs => (rs.2 : ℝ) < y),
      literalH A (N * rs.1) (rs.1 * rs.2) rs.2) = goldbachV A N z y := by
  rw [goldbachS4Pairs_low_eq hy hyN, Finset.sum_filter, Finset.sum_product,
    Finset.sum_comm]
  simp only [goldbachV, Finset.sum_filter]

/-- Exact three-region split, retaining the s=y boundary in the middle part.
The cubic condition makes the old root restriction automatic in the low block. -/
 theorem goldbachS4_split_exact (A : Finset ℕ) (N : ℕ) {z y : ℝ}
    (hzy : z ≤ y) (hy : 2 ≤ y) (hyN : y ^ 3 ≤ (N : ℝ)) :
    goldbachS4 A N z = goldbachV A N z y + goldbachS5HalfOpen A N z y +
      goldbachS4 A N y := by
  let T := goldbachS4Pairs N z
  let f : ℕ × ℕ → ℤ := fun rs => literalH A (N * rs.1) (rs.1 * rs.2) rs.2
  have hmid : (T.filter (fun rs => ¬(rs.2 : ℝ) < y)).filter
      (fun rs => (rs.1 : ℝ) < y) =
      T.filter (fun rs => (rs.1 : ℝ) < y ∧ y ≤ (rs.2 : ℝ)) := by
    ext rs
    simp only [Finset.mem_filter, not_lt]
    tauto
  have hhigh : (T.filter (fun rs => ¬(rs.2 : ℝ) < y)).filter
      (fun rs => ¬(rs.1 : ℝ) < y) = goldbachS4Pairs N y := by
    ext rs
    rcases rs with ⟨r,s⟩
    simp only [Finset.mem_filter, not_lt]
    constructor
    · rintro ⟨⟨hm, hys⟩, hyr⟩
      rcases Finset.mem_filter.mp hm with ⟨hbox,hr,hs,hcop,hzr,hrs,hbd⟩
      exact Finset.mem_filter.mpr ⟨hbox,hr,hs,hcop,hyr,hrs,hbd⟩
    · intro hm
      rcases Finset.mem_filter.mp hm with ⟨hbox,hr,hs,hcop,hyr,hrs,hbd⟩
      have hrsR : (r : ℝ) ≤ s := by exact_mod_cast hrs
      exact ⟨⟨Finset.mem_filter.mpr ⟨hbox,hr,hs,hcop,hzy.trans hyr,hrs,hbd⟩,
        hyr.trans hrsR⟩,hyr⟩
  have h1 := Finset.sum_filter_add_sum_filter_not T (fun rs => (rs.2 : ℝ) < y) f
  have h2 := Finset.sum_filter_add_sum_filter_not
    (T.filter (fun rs => ¬(rs.2 : ℝ) < y)) (fun rs => (rs.1 : ℝ) < y) f
  rw [hmid,hhigh] at h2
  have hlo := goldbachS4_low_sum_eq_V A N hy hyN (z := z)
  change (∑ rs ∈ T.filter (fun rs => (rs.2 : ℝ) < y), f rs) = _ at hlo
  change (∑ rs ∈ T, f rs) = _
  change (∑ rs ∈ T.filter (fun rs => (rs.2 : ℝ) < y), f rs) +
    (∑ rs ∈ T.filter (fun rs => ¬(rs.2 : ℝ) < y), f rs) = _ at h1
  change (∑ rs ∈ T.filter (fun rs => (rs.1 : ℝ) < y ∧ y ≤ (rs.2 : ℝ)), f rs) +
    goldbachS4 A N y = _ at h2
  change goldbachS5HalfOpen A N z y + goldbachS4 A N y = _ at h2
  omega

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig