import W17AcceptedCount
import W13TightAcceptedBudget

noncomputable section
namespace WuTarget.W17Accepted
open Wu2008DoubleSieve

/-- Only the difference in already normalized low-domain coefficients is added. -/
def jointCredit : ℝ :=
  W01.ordinaryCoefficient enhanced - W01.ordinaryCoefficient W04Accepted.enhanced

theorem jointCredit_nonneg : 0 ≤ jointCredit :=
  sub_nonneg.mpr coefficient_not_weaker

theorem jointCredit_eq : jointCredit =
    (W01.lowGain enhanced - W01.lowGain W04Accepted.enhanced)/4 := by
  unfold jointCredit W01.ordinaryCoefficient
  ring

def paidCoefficient : ℝ := W13TightAccepted.paidCoefficient + jointCredit

def remainingCoefficient : ℝ := W13TightAccepted.remainingCoefficient + jointCredit

theorem previous_paid_le : W13TightAccepted.paidCoefficient ≤ paidCoefficient :=
  le_add_of_nonneg_right jointCredit_nonneg

theorem paid_lt_actual : paidCoefficient < W01.ordinaryCoefficient enhanced := by
  have h := W13TightAccepted.paid_lt_actual
  unfold paidCoefficient jointCredit
  linarith only [h]

theorem ordinary_P2_paid {ε dmax : ℝ} (hε : 0 < ε) (hdmax : 0 < dmax) :
    ∃ δ : ℝ, 0 < δ ∧ δ < dmax ∧ δ ≤ 1/100 ∧
      ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
        (paidCoefficient-ε)*U8CanonicalMother.M N ≤
          ((Finset.filter (fun p => Nat.Prime p ∧ 0 < N-p ∧
            ArithmeticFunction.cardFactors (N-p) ≤ 2) (Finset.range (N+1))).card : ℝ) := by
  obtain ⟨δ, hd, hm, hs, _, _, T, hT, hc⟩ := enhanced_ordinary_P2 hε hdmax
  refine ⟨δ, hd, hm, hs, T, hT, ?_⟩
  intro N hN he
  have hM : 0 ≤ U8CanonicalMother.M N :=
    (HighSixPhase6.original_scale_positive (hT.trans hN)).le
  exact (mul_le_mul_of_nonneg_right (sub_le_sub_right paid_lt_actual.le ε) hM).trans
    (hc N hN he)

theorem paid_threshold_iff : (4491/5000 : ℝ) ≤ paidCoefficient ↔
    (840977/800000 : ℝ) ≤ remainingCoefficient := by
  unfold paidCoefficient remainingCoefficient W13TightAccepted.paidCoefficient
  constructor <;> intro h <;> linarith

theorem refined_target (h : (840977/800000 : ℝ) ≤ remainingCoefficient) :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      RefinedExit.margin/2*U8CanonicalMother.M N ≤
        ((Wu2004MeanValue.refinedGood N (9469/5000)).card : ℝ) ∧
      ∃ p r q : ℕ, p.Prime ∧ (r=1 ∨ r.Prime) ∧ q.Prime ∧
        N=p+r*q ∧ (r : ℝ) ≤ (q : ℝ)^(4469/5000 : ℝ) := by
  apply RefinedExit.from_actual_count (paid_threshold_iff.mpr h)
  intro ε hε
  obtain ⟨_, _, _, _, T, hT, hc⟩ := ordinary_P2_paid hε (by norm_num : (0 : ℝ) < 1)
  exact ⟨T, hT, hc⟩

end WuTarget.W17Accepted
