import W17JointRecoveryRoot
import W04AcceptedCount

noncomputable section
namespace WuTarget.W17Accepted
open Wu2008DoubleSieve ActualNineFeedback NodeExtension

/-- An unevaluated analytic lower vector; no new numerical iteration is run. -/
def enhanced (i : Fin 9) : ℝ :=
  max (W04Accepted.enhanced i)
    (W09.seed i + matrixApply W17Joint.jointMatrix W04Accepted.enhanced i)

theorem previous_le_enhanced (i : Fin 9) :
    W04Accepted.enhanced i ≤ enhanced i := le_max_left _ _

theorem enhanced_nonneg (i : Fin 9) : 0 ≤ enhanced i :=
  (W04Accepted.enhanced_nonneg i).trans (previous_le_enhanced i)

theorem enhanced_actual :
    ∃ d : ℝ, 0 < d ∧ d ≤ 1/10 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ d → ∀ i, enhanced i ≤ actualNine δ i := by
  obtain ⟨a, ha, ha1, hx⟩ := W04Accepted.enhanced_actual
  refine ⟨min a W09.commonRadius, lt_min ha W09.commonRadius_pos,
    (min_le_left _ _).trans ha1, ?_⟩
  intro δ hd hr
  have old := hx δ hd (hr.trans (min_le_left _ _))
  have step := W17Joint.symbolic_paid_update hd (hr.trans (min_le_right _ _))
    old (fun _ => le_rfl)
  intro i
  exact max_le (old i) (step i)

theorem coefficient_not_weaker :
    W01.ordinaryCoefficient W04Accepted.enhanced ≤ W01.ordinaryCoefficient enhanced :=
  W01.ordinaryCoefficient_mono previous_le_enhanced

theorem enhanced_ordinary_P2 {ε dmax : ℝ} (hε : 0 < ε) (hdmax : 0 < dmax) :
    ∃ δ : ℝ, 0 < δ ∧ δ < dmax ∧ δ ≤ 1/100 ∧
      (∀ i : Fin 9, enhanced i ≤ actualNine δ i) ∧
      (∀ j : Fin 21, matrixApply transferMatrix enhanced j ≤
        wuImprovementLimit false δ (rNode (j.val+1))) ∧
      ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
        (W01.ordinaryCoefficient enhanced-ε)*U8CanonicalMother.M N ≤
          ((Finset.filter (fun p => Nat.Prime p ∧ 0 < N-p ∧
            ArithmeticFunction.cardFactors (N-p) ≤ 2) (Finset.range (N+1))).card : ℝ) := by
  obtain ⟨d, hd, _, hx⟩ := enhanced_actual
  obtain ⟨δ, hδ, hmax, hδd, hdhi, T, hT, h⟩ :=
    W01.ordinary_P2 enhanced_nonneg hd hx hε hdmax
  have hnodes := hx δ hδ hδd.le
  exact ⟨δ, hδ, hmax, hdhi, hnodes,
    W01.transferred_actual hδ (by linarith) hnodes, T, hT, h⟩

end WuTarget.W17Accepted
