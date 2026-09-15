import F1CrossMass
noncomputable section
namespace F1CrossMass
open Real Wu2008DoubleSieve SharpLogRecurrence

theorem actual_count {ε : ℝ} (hε : 0<ε) :
    ∃ T : ℕ, 4≤T ∧ ∀ N : ℕ, T≤N → Even N →
      (8*joint-ε)*wuSingularSeries N*N/log N^(2 : ℕ) ≤
        (sieveCount N 1 N ((N : ℝ)^truncatedSixthLowerAlpha) : ℝ) := by
  have he : 0<Wu08TerminalAlignment.firstMain-8*joint+ε := by
    linarith only [joint_le_actual,hε]
  obtain ⟨T,hT,h⟩ := Wu08TerminalAlignment.first_actual_count he
  refine ⟨T,hT,?_⟩
  intro N hN hEven
  have hid : Wu08TerminalAlignment.firstMain-(Wu08TerminalAlignment.firstMain-8*joint+ε)=
      8*joint-ε := by ring
  simpa only [hid] using h N hN hEven
end F1CrossMass
