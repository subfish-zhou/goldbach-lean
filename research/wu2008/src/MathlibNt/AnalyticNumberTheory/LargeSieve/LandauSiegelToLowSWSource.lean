import MathlibNt.AnalyticNumberTheory.LargeSieve.DirichLTwistedQuadraticPointwiseSiegelWalfisz
import MathlibNt.AnalyticNumberTheory.LargeSieve.DirichLTwistedNonquadraticPointwiseSiegelWalfisz
import MathlibNt.AnalyticNumberTheory.LargeSieve.PointwisePrimitivePrefixAmplitudeBridge
import MathlibNt.AnalyticNumberTheory.LargeSieve.StandardBVFinalNonprincipalOnly

/-!
# Raw Landau--Siegel lower bounds supply the low Siegel--Walfisz source

The quadratic and nonquadratic uniform pointwise estimates are combined at the
same requested exponents and ambient endpoint.  The finite pointwise-to-prefix
amplitude bridge then supplies the exact low source used by Standard BV.
-/

open Set Function Filter Complex Real MeasureTheory

namespace AnalyticNumberTheory.LargeSieve

noncomputable section

/-- A raw Landau--Siegel lower bound supplies the nonprincipal primitive
prefix-amplitude Siegel--Walfisz source.  The split is the literal dichotomy
`χ² = 1` versus `χ² ≠ 1`; both branches use one shared eventual endpoint and
the common constant `Kn + Kq`. -/
theorem nonprincipalPrimitivePsiSiegelWalfiszSource_of_rawLandauSiegelLowerBound
    (hLandauSiegel : RawLandauSiegelLowerBound)
    {ν : ℝ → ℝ} (diffν : ContDiff ℝ 1 ν)
    (νpos : ∀ x > 0, 0 ≤ ν x)
    (suppν : support ν ⊆ Icc (1 / 2) 2)
    (mass_one : ∫ x in Ioi (0 : ℝ), ν x / x = 1) :
    NonprincipalPrimitivePsiSiegelWalfiszSource := by
  apply nonprincipalPrimitivePsiSiegelWalfiszSource_of_pointwise_lambdaCharacterPrefix
  intro C D
  obtain ⟨Kn, hKn, hn⟩ :=
    exists_nonquadraticPointwiseSiegelWalfisz_uniform
      diffν νpos suppν mass_one C D
  obtain ⟨Kq, hKq, hq⟩ :=
    exists_quadraticPointwiseSiegelWalfisz_uniform_of_rawLandauSiegelLowerBound
      hLandauSiegel diffν νpos suppν mass_one C D
  refine ⟨Kn + Kq, add_pos hKn hKq, ?_⟩
  filter_upwards [hn, hq] with N hnN hqN
  intro hN2 q hqmem ψ hψ y hy
  obtain ⟨hq2, hthreshold⟩ := Finset.mem_Icc.mp hqmem
  let : NeZero q := ⟨by omega⟩
  by_cases hquad : ψ.1 ^ 2 = 1
  · calc
      ‖lambdaCharacterPrefix y q ψ.1‖ ≤
          Kq * (N : ℝ) / Real.log (N : ℝ) ^ D :=
        hqN q (inferInstance : NeZero q) hthreshold ψ.1 ψ.2 hquad hψ y hy
      _ ≤ (Kn + Kq) * (N : ℝ) / Real.log (N : ℝ) ^ D := by
        gcongr
        exact le_add_of_nonneg_left hKn.le
  · calc
      ‖lambdaCharacterPrefix y q ψ.1‖ ≤
          Kn * (N : ℝ) / Real.log (N : ℝ) ^ D :=
        hnN q (inferInstance : NeZero q) hthreshold ψ.1 hquad y hy
      _ ≤ (Kn + Kq) * (N : ℝ) / Real.log (N : ℝ) ^ D := by
        gcongr
        exact le_add_of_nonneg_right hKq.le

/-- Honest conditional Standard Bombieri--Vinogradov headline: after the
fixed smoothing data, the only analytic hypothesis is the raw Landau--Siegel
lower bound. -/
theorem standardBombieriVinogradov_of_rawLandauSiegelLowerBound
    (hLandauSiegel : RawLandauSiegelLowerBound)
    {ν : ℝ → ℝ} (diffν : ContDiff ℝ 1 ν)
    (νpos : ∀ x > 0, 0 ≤ ν x)
    (suppν : support ν ⊆ Icc (1 / 2) 2)
    (mass_one : ∫ x in Ioi (0 : ℝ), ν x / x = 1) :
    MathlibNt.SieveTheory.BombieriVinogradov.StandardBombieriVinogradov :=
  standardBombieriVinogradov_of_nonprincipalPrimitivePsi
    (nonprincipalPrimitivePsiSiegelWalfiszSource_of_rawLandauSiegelLowerBound
      hLandauSiegel diffν νpos suppν mass_one)

end

end AnalyticNumberTheory.LargeSieve