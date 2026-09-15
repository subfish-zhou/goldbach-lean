import FirstCRationalIdentity

noncomputable section
open Real Set MeasureTheory
open scoped Interval
open FirstIntegralRecovery Wu08OriginalFirstSteps Wu2008DoubleSieve
namespace FirstCRationalPayment

/-- Exact finite endpoints of the original full interval; no numerical integration. -/
def endpointMass : ℝ := fixedPrimitive (927/200) - fixedPrimitive 2

theorem fixedPrimitive_derivative_original {u : ℝ} (hu : u ∈ Icc 2 (927/200)) :
    HasDerivAt fixedPrimitive (cLowerKernel (1327/200) u) u := by
  rw [cLowerKernel_literal hu,literalKernel_principalParts hu.1]
  exact fixedPrimitive_hasDerivAt hu.1

/-- Complete FTC payment of cLowerMass, with no changed domain or envelope order. -/
theorem cLowerMass_eq_endpointMass : cLowerMass (1327/200) = endpointMass := by
  have hc : ContinuousOn (cLowerKernel (1327/200)) (uIcc 2 (927/200)) := by
    convert cLowerKernel_continuousOn (1327/200) using 1
    norm_num
  have hd : ∀ u ∈ uIcc (2:ℝ) (927/200),
      HasDerivAt fixedPrimitive (cLowerKernel (1327/200) u) u := by
    intro u hu
    rw [uIcc_of_le (by norm_num : (2:ℝ) ≤ 927/200)] at hu
    exact fixedPrimitive_derivative_original hu
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable
  convert h using 1 <;> norm_num [cLowerMass,endpointMass]

/-- This exact endpoint constant remains strictly below the original actual C. -/
theorem endpointMass_lt_C : endpointMass < C (1327/200) := by
  rw [← cLowerMass_eq_endpointMass]
  exact cLowerMass_lt_C (by norm_num)

/-- Literal new endpoint count coefficient. E is retained once. -/
def endpointFirst : ℝ := 8*(log (1127/200)+endpointMass+E (1327/200))

theorem endpointFirst_eq_firstLower : endpointFirst = firstLower := by
  rw [endpointFirst,firstLower,cLowerMass_eq_endpointMass]

theorem endpointFirst_actual_count {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (endpointFirst-ε)*wuSingularSeries N*N/log N^(2 : ℕ) ≤
        (sieveCount N 1 N ((N : ℝ)^truncatedSixthLowerAlpha) : ℝ) := by
  rw [endpointFirst_eq_firstLower]
  exact firstLower_actual_count hε

/-- Exact remaining finite-endpoint publication obligation, not an assumed payment. -/
theorem publication_count_of_endpoint_payment
    (h : (14900897:ℝ)/8000000-log (1127/200) ≤ endpointMass+E (1327/200))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ((14900897:ℝ)/1000000-ε)*wuSingularSeries N*N/log N^(2 : ℕ) ≤
        (sieveCount N 1 N ((N : ℝ)^truncatedSixthLowerAlpha) : ℝ) := by
  apply new_mass_suffices_for_publication_count ?_ hε
  rwa [cLowerMass_eq_endpointMass]

end FirstCRationalPayment
