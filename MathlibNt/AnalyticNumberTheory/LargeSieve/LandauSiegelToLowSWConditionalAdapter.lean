import MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLQuadraticConditionalPowerZeroFree
import MathlibNt.AnalyticNumberTheory.LargeSieve.DirichLTwistedNonquadraticPointwiseSiegelWalfisz
import MathlibNt.AnalyticNumberTheory.LargeSieve.PointwisePrimitivePrefixAmplitudeBridge

/-!
# Conditional Landau--Siegel to low Siegel--Walfisz adapter

This module deliberately does **not** claim that the raw Landau--Siegel lower
bound alone has already been connected to a quadratic pointwise prime-number
theorem.  The existing quadratic theorem supplies a power-width zero-free
region, but the quadratic rectangle/logarithmic-derivative estimates, Perron
contour bounds, smoothing removal, and scalar error payment have not yet been
assembled in the production graph.

Accordingly, the theorem below leaves that exact analytic implication as the
explicit argument `hquadraticZeroFreeToPointwise`.  The Landau--Siegel premise
itself is written with its raw quantifiers and is not packaged as a `Source`.
The conclusion is the genuine prefix-maximal low source only after this
additional premise is supplied.
-/

open Set Function Filter Complex Real MeasureTheory

namespace AnalyticNumberTheory.LargeSieve

noncomputable section

/-- Honest conditional adapter from a raw, uniform Landau--Siegel lower bound
at `1` to the actual nonprincipal primitive low Siegel--Walfisz source.

The second premise exposes the remaining quadratic analytic assembly: it must
turn the concrete power-width zero-free region into a pointwise bound for every
prefix.  This is intentionally stronger and more explicit than merely assuming
holomorphy, since the current production graph has no quadratic counterpart of
its nonquadratic contour/error-assembly chain. -/
theorem nonprincipalPrimitivePsiSiegelWalfiszSource_of_landauSiegelLowerBound
    {ν : ℝ → ℝ} (diffν : ContDiff ℝ 1 ν)
    (νpos : ∀ x > 0, 0 ≤ ν x)
    (suppν : support ν ⊆ Icc (1 / 2) 2)
    (mass_one : ∫ x in Ioi (0 : ℝ), ν x / x = 1)
    (hLandauSiegel :
      ∀ η : ℝ, 0 < η → ∃ c : ℝ, 0 < c ∧
        ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
          χ.IsPrimitive → χ ^ 2 = 1 → χ ≠ 1 →
          c * (q : ℝ) ^ (-η) ≤ (χ.LFunction 1).re)
    (hquadraticZeroFreeToPointwise :
      ∀ (C D : ℕ) (η A : ℝ), 0 < η → 0 < A →
        (∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
          χ.IsPrimitive → χ ^ 2 = 1 → χ ≠ 1 →
          ∀ (β t : ℝ),
            β ∈ Ico
              (1 - A * (q : ℝ) ^ (-2 * η) /
                (dirichletLQuadraticConditionalPowerZeroFreeH q t) ^ 12) 1 →
            χ.LFunction (β + I * t) ≠ 0) →
        ∃ K : ℝ, 0 < K ∧
          ∀ᶠ N : ℕ in atTop, ∀ (q : ℕ), ∀ _inst : NeZero q,
            q ≤ logConductorThreshold N C →
            ∀ (χ : DirichletCharacter ℂ q),
              χ.IsPrimitive → χ ^ 2 = 1 → χ ≠ 1 →
              ∀ y : ℕ, y ≤ N →
                ‖lambdaCharacterPrefix y q χ‖ ≤
                  K * (N : ℝ) / Real.log (N : ℝ) ^ D) :
    NonprincipalPrimitivePsiSiegelWalfiszSource := by
  -- Fix η = 1 before choosing C and D, keeping the zero-free region uniform.
  obtain ⟨c, hc, hlower⟩ := hLandauSiegel 1 (by norm_num)
  obtain ⟨A, hA, hzero⟩ :=
    exists_dirichletL_quadratic_conditional_powerZeroFree c 1 hc (by norm_num)
  have hquadraticZero :
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
        χ.IsPrimitive → χ ^ 2 = 1 → χ ≠ 1 →
        ∀ (β t : ℝ),
          β ∈ Ico
            (1 - A * (q : ℝ) ^ (-2 * (1 : ℝ)) /
              (dirichletLQuadraticConditionalPowerZeroFreeH q t) ^ 12) 1 →
          χ.LFunction (β + I * t) ≠ 0 := by
    intro q _ χ hprimitive hquad hχ β t hβ
    exact hzero q χ β t hquad hχ
      (hlower q χ hprimitive hquad hχ) hβ
  apply nonprincipalPrimitivePsiSiegelWalfiszSource_of_pointwise_lambdaCharacterPrefix
  intro C D
  obtain ⟨Kn, hKn, hn⟩ :=
    exists_nonquadraticPointwiseSiegelWalfisz_uniform
      diffν νpos suppν mass_one C D
  obtain ⟨Kq, hKq, hq⟩ :=
    hquadraticZeroFreeToPointwise C D 1 A (by norm_num) hA hquadraticZero
  refine ⟨Kn + Kq, add_pos hKn hKq, ?_⟩
  -- Use a common eventual range and constant for both character cases.
  filter_upwards [hn, hq] with N hnN hqN
  intro hN2 q hqmem ψ hψ y hy
  let : NeZero q := ⟨by
    have hq2 : 2 ≤ q := (Finset.mem_Icc.mp hqmem).1
    omega⟩
  have hthreshold : q ≤ logConductorThreshold N C :=
    (Finset.mem_Icc.mp hqmem).2
  by_cases hquad : ψ.1 ^ 2 = 1
  · have hb := hqN q (inferInstance : NeZero q) hthreshold ψ.1 ψ.2 hquad hψ y hy
    calc
      ‖lambdaCharacterPrefix y q ψ.1‖ ≤
          Kq * (N : ℝ) / Real.log (N : ℝ) ^ D := hb
      _ ≤ (Kn + Kq) * (N : ℝ) / Real.log (N : ℝ) ^ D := by
        gcongr
        exact le_add_of_nonneg_left hKn.le
  · have hb := hnN q (inferInstance : NeZero q) hthreshold ψ.1 hquad y hy
    calc
      ‖lambdaCharacterPrefix y q ψ.1‖ ≤
          Kn * (N : ℝ) / Real.log (N : ℝ) ^ D := hb
      _ ≤ (Kn + Kq) * (N : ℝ) / Real.log (N : ℝ) ^ D := by
        gcongr
        exact le_add_of_nonneg_right hKq.le

end

end AnalyticNumberTheory.LargeSieve
