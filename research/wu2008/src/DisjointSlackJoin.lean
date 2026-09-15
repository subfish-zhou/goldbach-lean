import BaseSharedSlack
import SixthRetainedSlack

/-! Compose only disjoint block payments in the exact actual coefficient. -/
noncomputable section
open Real Set MeasureTheory
open Wu2008DoubleSieve
namespace DisjointSlackJoin

def coefficient : ℝ := GlobalLowerSlack.lowerCoefficient +
  BaseSharedSlack.gain + SixthRetainedSlack.gain

theorem shared_literal : BaseSharedSlack.block = SixthRetainedSlack.sharedBlock := rfl

theorem actual_lower : coefficient < U8CanonicalMother.improvedCoefficient := by
  have hp : BaseSharedSlack.gain ≤ SixthRetainedSlack.sharedBlock := by
    rw [← shared_literal]
    exact BaseSharedSlack.block_payment
  exact SixthRetainedSlack.combine_shared hp

theorem remaining_identity : U8CanonicalMother.improvedCoefficient-coefficient =
    (BaseSharedSlack.block-BaseSharedSlack.gain)+
    (SixthRetainedSlack.block-SixthRetainedSlack.gain)+
    SixthRetainedSlack.otherRemainder := by
  have he := SixthRetainedSlack.actual_partition
  rw [← shared_literal] at he
  unfold coefficient
  linarith only [he]

theorem strict_improvement : GlobalLowerSlack.lowerCoefficient < coefficient := by
  unfold coefficient
  linarith only [BaseSharedSlack.gain_positive,SixthRetainedSlack.gain_positive]

theorem strict_ordinary_P2 :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1/100 ∧
      ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
        coefficient*U8CanonicalMother.M N <
          ((Finset.filter (fun p => Nat.Prime p ∧ 0 < N-p ∧
            ArithmeticFunction.cardFactors (N-p) ≤ 2) (Finset.range (N+1))).card : ℝ) := by
  have hp : 0 < (U8CanonicalMother.improvedCoefficient-coefficient)/2 :=
    half_pos (sub_pos.mpr actual_lower)
  obtain ⟨δ,hδ,hδhi,T,hT,h⟩ := U8CanonicalMother.improved_ordinary_P2 _ hp
  refine ⟨δ,hδ,hδhi,T,hT,?_⟩
  intro N hN he
  have hs : 0 < U8CanonicalMother.M N := HighSixPhase6.original_scale_positive (hT.trans hN)
  have hc : coefficient < U8CanonicalMother.improvedCoefficient-
      (U8CanonicalMother.improvedCoefficient-coefficient)/2 := by linarith only [hp]
  exact (mul_lt_mul_of_pos_right hc hs).trans_le (h N hN he)

theorem coefficient_bounds : (831692/1000000:ℝ) < coefficient ∧
    coefficient < 831695/1000000 := by
  unfold coefficient
  constructor <;> linarith only [GlobalLowerSlack.lowerCoefficient_bounds.1,
    GlobalLowerSlack.lowerCoefficient_bounds.2,BaseSharedSlack.gain_bounds.1,
    BaseSharedSlack.gain_bounds.2,SixthRetainedSlack.gain_bounds.1,
    SixthRetainedSlack.gain_bounds.2]

def residual : ℝ := GlobalLowerSlack.residual-BaseSharedSlack.gain-SixthRetainedSlack.gain

theorem actual_target_residual : 8*log (5000/4469)-U8CanonicalMother.improvedCoefficient < residual := by
  have ht := JointLogTotalComparison.log_le_V (show (1:ℝ) ≤ 5000/4469 by norm_num)
  have he := GlobalLowerSlack.residual_identity
  have ha := actual_lower
  unfold residual coefficient at *
  linarith only [ht,he,ha]

theorem certificate_below_target : coefficient < 8*log (5000/4469) := by
  have hl := SharpLogRecurrence.log_lower (show (1:ℝ) ≤ 5000/4469 by norm_num)
  have hc : (831695/1000000:ℝ) < 8*SharpLogRecurrence.lowerLog (5000/4469) := by
    norm_num [SharpLogRecurrence.lowerLog]
  linarith only [coefficient_bounds.2,hl,hc]

end DisjointSlackJoin
