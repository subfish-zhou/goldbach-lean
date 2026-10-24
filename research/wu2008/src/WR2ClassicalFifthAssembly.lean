import WR2ClassicalFifthQuadrature
import WR2ClassicalFifthIntegral
import WR2ClassicalFifthRational

noncomputable section
namespace WuPaper.ClassicalFifthAssembly
open Real Set Finset
open ClassicalFifthSource ClassicalFifthKernel ClassicalUniformMidpoint ClassicalFifthRational

private theorem initial_bound {s : ℝ} (hs : lo ≤ s) (he : s ≤ 4) :
    |ClassicalFifthProfile.initial s| ≤ 3 ∧ |ClassicalFifthProfile.initialD1 s| ≤ 2 ∧
      |ClassicalFifthProfile.initialD2 s| ≤ 2 := by
  obtain ⟨h,h1,h2⟩ := ClassicalFifthProfile.initial_bounds (by linarith [geometry.1]) (show s ≤ 5 by linarith)
  exact ⟨h.trans (by norm_num),h1.trans (by norm_num),h2.trans (by norm_num)⟩

private theorem lower_bound {s : ℝ} (hs : lo ≤ s) (he : s ≤ cut) :
    |ClassicalFifthBranch.lower s| ≤ 1 ∧ |ClassicalFifthBranch.lowerD1 s| ≤ 1 ∧
      |ClassicalFifthBranch.lowerD2 s| ≤ 1 :=
  ⟨(ClassicalFifthBranch.lower_bounds hs he).2,ClassicalFifthBranch.lower_derivative_bounds he⟩

private theorem upper_bound {s : ℝ} (hs : cut ≤ s) (he : s ≤ hi) :
    |ClassicalFifthBranch.upper s| ≤ 1 ∧ |ClassicalFifthBranch.upperD1 s| ≤ 1 ∧
      |ClassicalFifthBranch.upperD2 s| ≤ 1 :=
  ⟨(ClassicalFifthBranch.upper_bounds hs he).2,ClassicalFifthBranch.upper_derivative_bounds he⟩

/-- Three finite midpoint certificates discharge the fifth classical lower bound. -/
theorem fifth_lower_of_payments (q0 q1 q2 : ℕ → ℝ)
    (hq0 : ∀ i < 1024, q0 i ≤ initialValue ((point lo 4 1024 i+point lo 4 1024 (i+1))/2))
    (hq1 : ∀ i < 1024, q1 i ≤ middleValue ((point 4 cut 1024 i+point 4 cut 1024 (i+1))/2))
    (hq2 : ∀ i < 1024, q2 i ≤ terminalValue ((point cut hi 1024 i+point cut hi 1024 (i+1))/2))
    (hs0 : (273358482524540:ℝ)/1000000000000 ≤ ∑ i ∈ range 1024, q0 i)
    (hs1 : (661191362320992:ℝ)/1000000000000 ≤ ∑ i ∈ range 1024, q1 i)
    (hs2 : (405237426677551:ℝ)/1000000000000 ≤ ∑ i ∈ range 1024, q2 i) :
    (165533:ℝ)/100000 ≤ Wu08TerminalAlignment.fifthMain := by
  have hn : 0 < (1024:ℕ) := by norm_num
  have h0 := ClassicalFifthQuadrature.uniform_lower hn le_rfl
    (geometry.2.2.1.trans geometry.2.2.2.1) geometry.2.1
    (fun s hs => ClassicalFifthProfile.initial_deriv (by linarith [hs.1,geometry.1]))
    (fun s hs => ClassicalFifthProfile.initialD1_deriv (by linarith [hs.1,geometry.1]))
    (fun _s hs => ClassicalFifthBranch.lower_deriv (hs.2.trans geometry.2.2.1))
    (fun _s hs => ClassicalFifthBranch.lowerD1_deriv (hs.2.trans geometry.2.2.1))
    (fun _s hs => initial_bound hs.1 hs.2)
    (fun _s hs => lower_bound hs.1 (hs.2.trans geometry.2.2.1)) q0
    (fun i hi => (hq0 i hi).trans (initial_value_le (midpoint_mem hn geometry.2.1 hi).1 (midpoint_mem hn geometry.2.1 hi).2))
  have h1 := ClassicalFifthQuadrature.uniform_lower hn geometry.2.1 geometry.2.2.2.1 geometry.2.2.1
    (fun _s hs => ClassicalFifthProfile.terminal_deriv hs.1)
    (fun _s hs => ClassicalFifthProfile.terminalD1_deriv hs.1)
    (fun _s hs => ClassicalFifthBranch.lower_deriv hs.2)
    (fun _s hs => ClassicalFifthBranch.lowerD1_deriv hs.2)
    (fun _s hs => ClassicalFifthProfile.terminal_bounds hs.1 (hs.2.trans (geometry.2.2.2.1.trans geometry.2.2.2.2.1)))
    (fun _s hs => lower_bound (geometry.2.1.trans hs.1) hs.2) q1
    (fun i hi => (hq1 i hi).trans (middle_value_le (midpoint_mem hn geometry.2.2.1 hi).1 (midpoint_mem hn geometry.2.2.1 hi).2))
  have h2 := ClassicalFifthQuadrature.uniform_lower hn (geometry.2.1.trans geometry.2.2.1) le_rfl geometry.2.2.2.1
    (fun _s hs => ClassicalFifthProfile.terminal_deriv (geometry.2.2.1.trans hs.1))
    (fun _s hs => ClassicalFifthProfile.terminalD1_deriv (geometry.2.2.1.trans hs.1))
    (fun _s hs => ClassicalFifthBranch.upper_deriv hs.2)
    (fun _s hs => ClassicalFifthBranch.upperD1_deriv hs.2)
    (fun _s hs => ClassicalFifthProfile.terminal_bounds (geometry.2.2.1.trans hs.1) (hs.2.trans geometry.2.2.2.2.1))
    (fun _s hs => upper_bound hs.1 hs.2) q2
    (fun i hi => (hq2 i hi).trans (terminal_value_le (midpoint_mem hn geometry.2.2.2.1 hi).1 (midpoint_mem hn geometry.2.2.2.1 hi).2))
  have hw0 := mul_le_mul_of_nonneg_left hs0 (show 0 ≤ step lo 4 1024 from div_nonneg (sub_nonneg.mpr geometry.2.1) (by norm_num))
  have hw1 := mul_le_mul_of_nonneg_left hs1 (show 0 ≤ step 4 cut 1024 from div_nonneg (sub_nonneg.mpr geometry.2.2.1) (by norm_num))
  have hw2 := mul_le_mul_of_nonneg_left hs2 (show 0 ≤ step cut hi 1024 from div_nonneg (sub_nonneg.mpr geometry.2.2.2.1) (by norm_num))
  have h := ClassicalFifthIntegral.fifth_lower
  norm_num [step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
    ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta] at h0 h1 h2 hw0 hw1 hw2 h
  linarith only [h0,h1,h2,hw0,hw1,hw2,h]

end WuPaper.ClassicalFifthAssembly
#print axioms WuPaper.ClassicalFifthAssembly.fifth_lower_of_payments
