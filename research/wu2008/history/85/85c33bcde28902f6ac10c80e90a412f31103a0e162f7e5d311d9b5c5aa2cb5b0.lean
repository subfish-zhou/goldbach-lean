import W11AcceptedCount
import W02Root

noncomputable section
namespace WuTarget.W02Accepted
open Wu2008DoubleSieve ActualNineFeedback NodeExtension DirectFiniteF6

/-- Apply the certified transfer to the enhanced vector, retaining its Sigma term. -/
def enhancedNodes (j : Fin 21) : ℝ :=
  matrixApply W02.rationalMatrix W04Accepted.enhanced j +
    aProfile (nineProfile W04Accepted.enhanced) * W02.sigmaWeight j

theorem sigma_nonneg : 0 ≤ aProfile (nineProfile W04Accepted.enhanced) :=
  (profiles_nonneg (fun t _ => nineProfile_nonneg W04Accepted.enhanced_nonneg t)).1

theorem enhancedNodes_nonneg (j : Fin 21) : 0 ≤ enhancedNodes j :=
  add_nonneg
    (matrixApply_nonneg W02.rationalMatrix_nonneg W04Accepted.enhanced_nonneg j)
    (mul_nonneg sigma_nonneg (W02.sigmaWeight_nonneg j))

theorem table_le_enhancedNodes (j : Fin 21) :
    (W02.lowerVector j : ℝ) ≤ enhancedNodes j := by
  have h : (W02.lowerVector j : ℝ) ≤ (W02.qOutput j : ℝ) := by
    exact_mod_cast W02.output_lower j
  rw [W02.qOutput_cast] at h
  have hm := matrixApply_mono W02.rationalMatrix_nonneg W04Accepted.old_le_enhanced j
  exact (h.trans hm).trans
    (le_add_of_nonneg_right (mul_nonneg sigma_nonneg (W02.sigmaWeight_nonneg j)))

theorem enhancedNodes_le_transfer (j : Fin 21) :
    enhancedNodes j ≤ matrixApply transferMatrix W04Accepted.enhanced j :=
  W02.apply_lower_keeps_sigma W04Accepted.enhanced_nonneg j

theorem enhancedNodes_actual :
    ∃ d : ℝ, 0 < d ∧ d ≤ 1/10 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ d → ∀ j : Fin 21,
        enhancedNodes j ≤ wuImprovementLimit false δ (rNode (j.val+1)) := by
  obtain ⟨d,hd,hdhi,hx⟩ := W04Accepted.enhanced_actual
  refine ⟨d,hd,hdhi,?_⟩
  intro δ hδ hδd j
  exact (enhancedNodes_le_transfer j).trans
    (W01.transferred_actual hδ (hδd.trans hdhi) (hx δ hδ hδd) j)

def nodeGain : ℝ := Gamma enhancedNodes 0

theorem nodeGain_nonneg : 0 ≤ nodeGain :=
  Gamma_nonneg enhancedNodes_nonneg le_rfl

theorem tableGain_le_nodeGain :
    Gamma (fun j => (W02.lowerVector j : ℝ)) 0 ≤ nodeGain :=
  Gamma_mono table_le_enhancedNodes le_rfl

theorem nodeGain_le_full : nodeGain ≤ W01.lowGain W04Accepted.enhanced :=
  Gamma_mono enhancedNodes_le_transfer le_rfl

/-- Alternative computable-profile budget, not an extra gain added to the old one. -/
def paidCoefficient : ℝ :=
  W11Accepted.paidCoefficient W04Accepted.enhanced +
    (nodeGain-W01.lowGain W04Accepted.enhanced)/4

theorem paid_lt_actual : paidCoefficient < W01.ordinaryCoefficient W04Accepted.enhanced := by
  unfold paidCoefficient
  linarith only [nodeGain_le_full, W11Accepted.paid_lt_actual W04Accepted.enhanced]

theorem enhanced_P2_paid {ε dmax : ℝ} (hε : 0 < ε) (hdmax : 0 < dmax) :
    ∃ δ : ℝ, 0 < δ ∧ δ < dmax ∧ δ ≤ 1/100 ∧
      ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
        (paidCoefficient-ε)*U8CanonicalMother.M N ≤
          ((Finset.filter (fun p => Nat.Prime p ∧ 0 < N-p ∧
            ArithmeticFunction.cardFactors (N-p) ≤ 2) (Finset.range (N+1))).card : ℝ) :=
  ParentScalarCount.from_enhanced paid_lt_actual.le hε hdmax

end WuTarget.W02Accepted
