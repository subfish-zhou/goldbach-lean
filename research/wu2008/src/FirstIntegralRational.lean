import FirstIntegralMass

noncomputable section
open Real Set MeasureTheory
open scoped Interval
open Wu2008DoubleSieve SharpLogRecurrence Wu08OriginalFirstSteps
namespace FirstIntegralRecovery

/-- Literal rational form of the same prescribed one-split envelope. -/
theorem splitL_rational {x : ℝ} (hx : 1 ≤ x) : splitL x =
    2*((x-1)/(x+3))+2*((x-1)/(x+3))^3/3+
    (2*((x-1)/(3*x+1))+2*((x-1)/(3*x+1))^3/3) := by
  have h1 : (((1+x)/2-1)/((1+x)/2+1)) = (x-1)/(x+3) := by
    field_simp
    ring
  have hn : 1+x ≠ 0 := by linarith
  have hn3 : 3*x+1 ≠ 0 := by linarith
  have h2 : (2*x/(1+x)-1)/(2*x/(1+x)+1) = (x-1)/(3*x+1) := by
    field_simp
    ring
  simp only [splitL,lowerLog,h1,h2]

/-- The remaining mass question is recorded with literal fixed endpoint. -/
theorem new_mass_suffices_for_publication_count
    (hmass : (14900897:ℝ)/8000000-log (1127/200) ≤
      cLowerMass (1327/200)+E (1327/200))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ((14900897:ℝ)/1000000-ε)*wuSingularSeries N*N/log N^(2 : ℕ) ≤
        (sieveCount N 1 N ((N : ℝ)^truncatedSixthLowerAlpha) : ℝ) := by
  have hm : (14900897:ℝ)/1000000 ≤ firstLower := by
    unfold firstLower
    linarith only [hmass]
  have hδ : 0 < firstLower-(14900897:ℝ)/1000000+ε := by linarith only [hm,hε]
  obtain ⟨T,hT,h⟩ := firstLower_actual_count hδ
  refine ⟨T,hT,?_⟩
  intro N hN hEven
  have heq : firstLower-(firstLower-(14900897:ℝ)/1000000+ε) =
      (14900897:ℝ)/1000000-ε := by ring
  simpa only [heq] using h N hN hEven

end FirstIntegralRecovery
