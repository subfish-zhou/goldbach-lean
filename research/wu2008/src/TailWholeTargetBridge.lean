import TailWholeSignedPayment

noncomputable section
open Real Wu2008DoubleSieve
namespace TailWholeCommonLog

def targetGap : ℝ := 8*finite-14900897/1000000

theorem original_target_of_gap (h : 0 ≤ targetGap) :
    (14900897:ℝ)/1000000 ≤ Wu08TerminalAlignment.firstMain := by
  unfold targetGap at h
  linarith only [h,finite_le_actual]

/-- The scalar premise is exposed; it is not a completed constant certificate. -/
theorem original_target_count_of_gap (h : 0 ≤ targetGap) {ε : ℝ} (hε : 0<ε) :
    ∃ T : ℕ, 4≤T ∧ ∀ N : ℕ, T≤N → Even N →
      (14900897/1000000-ε)*wuSingularSeries N*N/log N^(2 : ℕ) ≤
        (sieveCount N 1 N ((N : ℝ)^truncatedSixthLowerAlpha) : ℝ) := by
  have he : 0<Wu08TerminalAlignment.firstMain-14900897/1000000+ε := by
    linarith only [original_target_of_gap h,hε]
  obtain ⟨T,hT,hcount⟩ := Wu08TerminalAlignment.first_actual_count he
  refine ⟨T,hT,?_⟩
  intro N hN hEven
  have hid : Wu08TerminalAlignment.firstMain-
      (Wu08TerminalAlignment.firstMain-14900897/1000000+ε)=14900897/1000000-ε := by ring
  simpa only [hid] using hcount N hN hEven
end TailWholeCommonLog
