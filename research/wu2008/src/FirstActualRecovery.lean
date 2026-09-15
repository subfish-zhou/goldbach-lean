import FirstCRationalExactCount

namespace FirstActualRecovery
open Real Wu08OriginalFirstSteps FirstCRationalPayment Wu2008DoubleSieve
noncomputable section

/-- The genuine positive kernel mass omitted by the chosen rational envelope. -/
def kernelRecovery : ℝ := C (1327/200)-endpointMass

theorem kernelRecovery_pos : 0 < kernelRecovery := sub_pos.mpr endpointMass_lt_C

theorem actual_first_identity :
    Wu08TerminalAlignment.firstMain = endpointFirst+8*kernelRecovery := by
  unfold Wu08TerminalAlignment.firstMain endpointFirst kernelRecovery
  ring

/-- The actual first coefficient, not just its selected rational-kernel lower bound. -/
theorem actual_first_recoveries : Wu08TerminalAlignment.firstMain =
    8*(rationalMainPayment+logRecovery+kernelRecovery+E (1327/200)) := by
  rw [actual_first_identity,endpointFirst_exact_recoveries,finiteMainPayment_exact]
  ring

theorem actual_publication_gap :
    (14900897:ℝ)/1000000-Wu08TerminalAlignment.firstMain =
      8*(rationalPublicationDebit-logRecovery-kernelRecovery-E (1327/200)) := by
  rw [actual_first_identity]
  have h := exact_publication_gap
  linarith only [h]

/-- Exact remaining original obligation; it does not require the lower envelope to suffice alone. -/
theorem actual_publication_iff :
    (14900897:ℝ)/1000000 ≤ Wu08TerminalAlignment.firstMain ↔
      rationalPublicationDebit ≤ logRecovery+kernelRecovery+E (1327/200) := by
  have h := actual_publication_gap
  constructor <;> intro hbound <;> linarith only [h,hbound]

theorem actual_publication_count
    (hpaid : rationalPublicationDebit ≤ logRecovery+kernelRecovery+E (1327/200))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ((14900897:ℝ)/1000000-ε)*wuSingularSeries N*N/log N^(2 : ℕ) ≤
        (sieveCount N 1 N ((N : ℝ)^truncatedSixthLowerAlpha) : ℝ) := by
  have hm := actual_publication_iff.mpr hpaid
  have he : 0 < Wu08TerminalAlignment.firstMain-(14900897:ℝ)/1000000+ε := by linarith only [hm,hε]
  obtain ⟨T,hT,h⟩ := Wu08TerminalAlignment.first_actual_count he
  refine ⟨T,hT,?_⟩
  intro N hN hEven
  have hcancel : Wu08TerminalAlignment.firstMain-
      (Wu08TerminalAlignment.firstMain-(14900897:ℝ)/1000000+ε) = (14900897:ℝ)/1000000-ε := by ring
  simpa only [hcancel] using h N hN hEven

end
end FirstActualRecovery
