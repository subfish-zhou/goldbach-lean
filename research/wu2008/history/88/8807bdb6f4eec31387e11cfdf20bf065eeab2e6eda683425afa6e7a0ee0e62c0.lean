import W04AcceptedCount
import W15Root

noncomputable section
namespace WuTarget.W15Accepted
open Wu2008DoubleSieve Wu08TerminalAlignment ActualNineFeedback NodeExtension
open PositiveTwoPayment PositiveCoreResume PositiveSecondPayment Wu08OriginalFourWeights

/-- All other signed terms, leaving this independent block out exactly once. -/
def remainingCoefficient (x : Fin 9 → ℝ) : ℝ :=
  (3*firstMain+secondMain-thirdMain-fourthMain+fifthMain+sixthMain-
    2*seventhMain-eighthMain-ninthMain-original10-original11+
    8*secondGain+fifthGain+W01.lowGain x)/4

def paidCoefficient (x : Fin 9 → ℝ) : ℝ :=
  remainingCoefficient x + 2493/4000000

theorem coefficient_split (x : Fin 9 → ℝ) :
    W01.ordinaryCoefficient x = remainingCoefficient x +
      (4*Phase20.rawPsi+4*Phase18.g18+HighConsumer.highGain)/4 := by
  unfold W01.ordinaryCoefficient remainingCoefficient
  ring

theorem paidCoefficient_lt (x : Fin 9 → ℝ) :
    paidCoefficient x < W01.ordinaryCoefficient x := by
  rw [coefficient_split]
  unfold paidCoefficient
  linarith only [W15.independent_rational]

theorem ordinary_P2_paid {x : Fin 9 → ℝ} {d0 ε dmax : ℝ}
    (hn : ∀ i, 0 ≤ x i) (hd0 : 0 < d0)
    (hx : ∀ δ : ℝ, 0 < δ → δ ≤ d0 → ∀ i, x i ≤ actualNine δ i)
    (hε : 0 < ε) (hdmax : 0 < dmax) :
    ∃ δ : ℝ, 0 < δ ∧ δ < dmax ∧ δ < d0 ∧ δ ≤ 1/100 ∧
      ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
        (paidCoefficient x-ε)*U8CanonicalMother.M N ≤
          ((Finset.filter (fun p => Nat.Prime p ∧ 0 < N-p ∧
            ArithmeticFunction.cardFactors (N-p) ≤ 2) (Finset.range (N+1))).card : ℝ) := by
  obtain ⟨δ,hδ,hmax,hδ0,hsmall,T,hT,h⟩ := W01.ordinary_P2 hn hd0 hx hε hdmax
  refine ⟨δ,hδ,hmax,hδ0,hsmall,T,hT,?_⟩
  intro N hN he
  have hM := (HighSixPhase6.original_scale_positive (hT.trans hN)).le
  change 0 ≤ U8CanonicalMother.M N at hM
  exact (mul_le_mul_of_nonneg_right
    (sub_le_sub_right (paidCoefficient_lt x).le ε) hM).trans (h N hN he)

/-- The W15 scalar is consumed with the concrete W04-enhanced finite certificate. -/
theorem enhanced_P2_paid {ε dmax : ℝ} (hε : 0 < ε) (hdmax : 0 < dmax) :
    ∃ δ : ℝ, 0 < δ ∧ δ < dmax ∧ δ ≤ 1/100 ∧
      ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
        (paidCoefficient W04Accepted.enhanced-ε)*U8CanonicalMother.M N ≤
          ((Finset.filter (fun p => Nat.Prime p ∧ 0 < N-p ∧
            ArithmeticFunction.cardFactors (N-p) ≤ 2) (Finset.range (N+1))).card : ℝ) := by
  obtain ⟨d,hd,_,hx⟩ := W04Accepted.enhanced_actual
  obtain ⟨δ,hδ,hmax,_,hsmall,T,hT,h⟩ :=
    ordinary_P2_paid W04Accepted.enhanced_nonneg hd hx hε hdmax
  exact ⟨δ,hδ,hmax,hsmall,T,hT,h⟩

end WuTarget.W15Accepted
