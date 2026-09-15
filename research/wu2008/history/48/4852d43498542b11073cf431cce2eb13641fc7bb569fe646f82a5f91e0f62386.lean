import W01Root
import W04Root

noncomputable section
namespace WuTarget.W04Accepted
open Wu2008DoubleSieve ActualNineFeedback NodeExtension

/-- One exact update, retaining the already certified vector coordinatewise. -/
def enhanced (i : Fin 9) : ℝ :=
  max (Wu04Bypass.v8 i)
    (Wu04Bypass.v0 i + matrixApply W04.augmentedMatrix Wu04Bypass.v8 i)

theorem old_le_enhanced (i : Fin 9) : Wu04Bypass.v8 i ≤ enhanced i :=
  le_max_left _ _

theorem enhanced_nonneg (i : Fin 9) : 0 ≤ enhanced i :=
  (Wu04Bypass.v8_nonneg i).trans (old_le_enhanced i)

theorem enhanced_actual :
    ∃ d : ℝ, 0 < d ∧ d ≤ 1/10 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ d → ∀ i, enhanced i ≤ actualNine δ i := by
  obtain ⟨a,ha,ha1,hv⟩ := Wu04Bypass.new_nine_actual
  obtain ⟨b,hb,_,hs⟩ := NineFeedbackStrength.actual_same_delta
  refine ⟨min a b,lt_min ha hb,(min_le_left _ _).trans ha1,?_⟩
  intro δ hδ hδd
  have hnodes := hv δ hδ (hδd.trans (min_le_left _ _))
  have hsys := hs δ hδ (hδd.trans (min_le_right _ _))
  have hu : ∀ i, Wu04Bypass.v0 i +
      matrixApply W04.augmentedMatrix Wu04Bypass.v8 i ≤ actualNine δ i :=
    W04.augmented_paid_update hsys hnodes Wu04Bypass.v8_nonneg (fun _ => le_rfl)
  intro i
  exact max_le (hnodes i) (hu i)

theorem coefficient_not_weaker :
    W01.ordinaryCoefficient Wu04Bypass.v8 ≤ W01.ordinaryCoefficient enhanced :=
  W01.ordinaryCoefficient_mono old_le_enhanced

/-- The new physical matrix block is consumed by the real signed P2 count. -/
theorem enhanced_ordinary_P2 {ε dmax : ℝ} (hε : 0 < ε) (hdmax : 0 < dmax) :
    ∃ δ : ℝ, 0 < δ ∧ δ < dmax ∧ δ ≤ 1/100 ∧
      (∀ i : Fin 9, enhanced i ≤ actualNine δ i) ∧
      (∀ j : Fin 21, matrixApply transferMatrix enhanced j ≤
        wuImprovementLimit false δ (rNode (j.val+1))) ∧
      ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
        (W01.ordinaryCoefficient enhanced-ε)*U8CanonicalMother.M N ≤
          ((Finset.filter (fun p => Nat.Prime p ∧ 0 < N-p ∧
            ArithmeticFunction.cardFactors (N-p) ≤ 2) (Finset.range (N+1))).card : ℝ) := by
  obtain ⟨d,hd,_,hx⟩ := enhanced_actual
  obtain ⟨δ,hδ,hmax,hδd,hdhi,T,hT,h⟩ :=
    W01.ordinary_P2 enhanced_nonneg hd hx hε hdmax
  have hnodes := hx δ hδ hδd.le
  exact ⟨δ,hδ,hmax,hdhi,hnodes,
    W01.transferred_actual hδ (by linarith) hnodes,T,hT,h⟩

end WuTarget.W04Accepted
