import FeedbackIntegral

namespace FeedbackLimit
open Wu2008DoubleSieve NodeExtension ActualNineFeedback DirectFiniteF6 Filter
open scoped Topology
noncomputable section

/-- First select a symbolic finite iterate using convergence, and only then
select the actual counting threshold. No iterate is evaluated. -/
theorem supplied_sixth : SixthSlotAssembly.SixthLower Cinf := by
  intro ε hε
  have he : Cinf - ε/2 < Cinf := by linarith
  obtain ⟨n, hn⟩ := (C_tendsto.eventually_const_lt he).exists
  obtain ⟨T, hT, hcount⟩ := actual_count_lower n (half_pos hε)
  refine ⟨T, hT, ?_⟩
  intro N hN hEven
  have hcoef : truncatedSixthLowerF6lin + Cinf - ε ≤
      truncatedSixthLowerF6lin + C n - ε/2 := by linarith only [hn]
  have hm := mul_le_mul_of_nonneg_right hcoef
    (truncatedSixthClosure_scale_nonneg (show 4 ≤ N by omega))
  have hm' : (truncatedSixthLowerF6lin+Cinf-ε)*wuSingularSeries N*N/Real.log N^(2 : ℕ) ≤
      (truncatedSixthLowerF6lin+C n-ε/2)*wuSingularSeries N*N/Real.log N^(2 : ℕ) := by
    simpa only [truncatedSixthMassScale, mul_div_assoc, mul_assoc] using hm
  exact hm'.trans (hcount N hN hEven)

def Qinf : ℝ := LogP2.Qlog + (Cinf - FullSourceLog.GammaLog6)/4

def Qbestinf : ℝ := max LogP2.Qlog Qinf

theorem Qn_le_Qinf (n : ℕ) : FiniteSameMother.Qn n ≤ Qinf := by
  have h := C_le_Cinf n
  unfold FiniteSameMother.Qn Qinf
  linarith only [h]

theorem Qbest_le_Qbestinf (n : ℕ) : FiniteSameMother.Qbest n ≤ Qbestinf :=
  max_le_max le_rfl (Qn_le_Qinf n)

/-- The already proved single-slot mother is consumed once, replacing rather
than adding sixth gains. Ordinary P2 allows complement one and excludes zero. -/
theorem ordinary_P2 (η : ℝ) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1/100 ∧
      ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
        (Qinf-η)*U8CanonicalMother.M N ≤
          ((Finset.filter (fun p => Nat.Prime p ∧ 0 < N-p ∧
            ArithmeticFunction.cardFactors (N-p) ≤ 2) (Finset.range (N+1))).card : ℝ) :=
  SixthSlotAssembly.ordinary_P2 supplied_sixth η hη

theorem best_ordinary_P2 (η : ℝ) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1/100 ∧
      ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
        (Qbestinf-η)*U8CanonicalMother.M N ≤
          ((Finset.filter (fun p => Nat.Prime p ∧ 0 < N-p ∧
            ArithmeticFunction.cardFactors (N-p) ≤ 2) (Finset.range (N+1))).card : ℝ) := by
  by_cases h : LogP2.Qlog ≤ Qinf
  · simpa only [Qbestinf, max_eq_right h] using ordinary_P2 η hη
  · simpa only [Qbestinf, max_eq_left (le_of_not_ge h)] using LogP2.improved_ordinary_P2 η hη

end
end FeedbackLimit
