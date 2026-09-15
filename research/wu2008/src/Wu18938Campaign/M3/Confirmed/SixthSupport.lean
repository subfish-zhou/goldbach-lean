import WRMapMSixthClassical
import MathlibNt.Wu2008DoubleSieve.TruncatedSixthLowerPrimeGeometry

noncomputable section

namespace Wu18938Campaign.M3.Confirmed

open Set Real MeasureTheory Wu2008DoubleSieve
open QuarterTrim DirectFiniteF6 Wu08G6High Wu08G6TableGeometryRecovery
open WuSource.SrcSixthGain
open scoped Classical

theorem sixth_region_eq_published (x y : ℝ) :
    truncatedSixthLowerRegion 0 x y ↔ (x, y) ∈ publishedReducedDomain := by
  simp only [truncatedSixthLowerRegion, publishedReducedDomain, mem_ofPred_eq,
    truncatedSixthLowerC, sub_zero]
  change (alpha ≤ x ∧ x ≤ beta ∧ beta ≤ y ∧
    y ≤ 1 / 2 - 3 * alpha ∧ x + y ≤ 1 / 2 - 2 * alpha) ↔
      (alpha ≤ x ∧ x ≤ beta ∧ beta ≤ y ∧ x + y ≤ 1 / 2 - 2 * alpha)
  constructor
  · rintro ⟨hx, hxb, hy, _, hxy⟩
    exact ⟨hx, hxb, hy, hxy⟩
  · rintro ⟨hx, hxb, hy, hxy⟩
    exact ⟨hx, hxb, hy, by linarith, hxy⟩

theorem sixth_kept_coordinate {N : ℕ} {t : ℕ × ℕ} (hN : 1 < N)
    (ht : t ∈ truncatedSixthKept N
      ((N : ℝ) ^ truncatedSixthLowerAlpha) ((N : ℝ) ^ truncatedSixthLowerBeta)
      ((N : ℝ) ^ truncatedSixthLowerSigma) ((N : ℝ) ^ truncatedSixthLowerLambda)) :
    (log (t.1 : ℝ) / log N, log (t.2 : ℝ) / log N) ∈ publishedReducedDomain := by
  apply (sixth_region_eq_published _ _).mp
  apply truncatedSixthLower_prime_region hN
  obtain ⟨hp, hprod⟩ := Finset.mem_filter.mp ht
  apply Finset.mem_filter.mpr
  exact ⟨hp, by
    simpa only [truncatedSixthLowerC, sub_zero, truncatedSixthLowerLambda] using hprod.le⟩

theorem sixth_original_support :
    QuarterTrim.originalP = {v | truncatedSixthLowerRegion 0 v.1 v.2} := by
  rw [source_reduced_domain]
  ext v
  exact (sixth_region_eq_published v.1 v.2).symm

theorem sixth_classical_on_kept_support :
    WuPaper.RMapMSixth.paperC6 wuLowerCoefficient =
      4 * ∫ x in truncatedSixthLowerAlpha..truncatedSixthLowerBeta,
        ∫ y in truncatedSixthLowerBeta..truncatedSixthLowerSigma,
          if (x, y) ∈ publishedReducedDomain then
            wuLowerCoefficient (truncatedSixthLowerS 0 x y) /
              (x * y * (truncatedSixthLowerC 0 - x - y)) else 0 := by
  rw [WuPaper.RMapMSixth.c6_eq_existing_classical]
  change truncatedSixthLowerF6lin = _
  unfold truncatedSixthLowerF6lin truncatedSixthLowerFdelta
  simp_rw [sixth_region_eq_published]

theorem sixth_twentyone_on_kept_support (w : Fin 21 → ℝ) :
    4 * (∫ v : ℝ × ℝ,
      if truncatedSixthLowerRegion 0 v.1 v.2 then
        kernel (profile w) v.1 v.2 else 0) =
      8 * ∑ j : Fin 21, g6Weight j * w j := by
  simp_rw [sixth_region_eq_published]
  exact published_twentyone w

end Wu18938Campaign.M3.Confirmed
