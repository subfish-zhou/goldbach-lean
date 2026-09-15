import SixthSlotAssembly
import DirectCount

open Wu2008DoubleSieve

namespace FiniteSameMother
noncomputable section

/-- The exact finite coefficient; the old and new sixth gains are not added. -/
def Qn (n : ℕ) : ℝ := LogP2.Qlog + (DirectFiniteF6.C n-FullSourceLog.GammaLog6)/4

def Qbest (n : ℕ) : ℝ := max LogP2.Qlog (Qn n)

theorem Qn_identity (n : ℕ) :
    Qn n = LogP2.Qlog + (DirectFiniteF6.C n-FullSourceLog.GammaLog6)/4 := rfl

theorem Qn_monotone : Monotone Qn := by
  intro n m hnm
  have h := DirectFiniteF6.C_monotone hnm
  unfold Qn
  linarith only [h]

theorem Qbest_monotone : Monotone Qbest := by
  intro n m hnm
  exact max_le_max le_rfl (Qn_monotone hnm)

theorem Qlog_le_Qbest (n : ℕ) : LogP2.Qlog ≤ Qbest n := le_max_left _ _

theorem Qn_le_Qbest (n : ℕ) : Qn n ≤ Qbest n := le_max_right _ _

/-- Discharge the only slot with the unconditional, symbolic finite F6 theorem. -/
theorem supplied_sixth (n : ℕ) : SixthSlotAssembly.SixthLower (DirectFiniteF6.C n) := by
  intro ε hε
  exact DirectFiniteF6.actual_count_lower n hε

/-- Unconditional ordinary P2, with positive complement and at most two prime
factors counted with multiplicity. The complement one remains allowed. -/
theorem ordinary_P2 (n : ℕ) (η : ℝ) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1/100 ∧
      ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
        (Qn n-η)*U8CanonicalMother.M N ≤
          ((Finset.filter (fun p => Nat.Prime p ∧ 0 < N-p ∧
            ArithmeticFunction.cardFactors (N-p) ≤ 2) (Finset.range (N+1))).card : ℝ) :=
  SixthSlotAssembly.ordinary_P2 (supplied_sixth n) η hη

/-- Select the stronger proved bound; never add two bounds for the same count.
This proves non-deterioration, not a strict numerical improvement. -/
theorem best_ordinary_P2 (n : ℕ) (η : ℝ) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1/100 ∧
      ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
        (Qbest n-η)*U8CanonicalMother.M N ≤
          ((Finset.filter (fun p => Nat.Prime p ∧ 0 < N-p ∧
            ArithmeticFunction.cardFactors (N-p) ≤ 2) (Finset.range (N+1))).card : ℝ) := by
  by_cases h : LogP2.Qlog ≤ Qn n
  · simpa only [Qbest, max_eq_right h] using ordinary_P2 n η hη
  · simpa only [Qbest, max_eq_left (le_of_not_ge h)] using LogP2.improved_ordinary_P2 η hη

end
end FiniteSameMother
