import RemainingHfJ
namespace RemainingHf
open Real Wu2008DoubleSieve NodeExtension ActualNineFeedback FirstFeedbackIntegrals
open SharpLogRecurrence Wu04FactorEnvelopes F1FullRecoveryPayment
open FiniteEndpointPayment CoupledIntegralRecovery
open scoped BigOperators
noncomputable section

theorem splitLower_nonneg {x : ℝ} (hx : 1 ≤ x) : 0 ≤ splitLower x := by
  have hb {y : ℝ} (hy : 1 ≤ y) : 0 ≤ basicLower y := by
    have hy0 : 0 < y := by linarith
    have hl : 0 ≤ lowerLog y := by unfold lowerLog; positivity
    have hg : 0 ≤ upperLog y-lowerLog y := by
      rw [OriginalFirstErrorRecovery.envelope_gap hy0]
      positivity
    have hp : 0 ≤ F1LowerResidual.payment y := by
      unfold F1LowerResidual.payment F1LowerResidual.denom
      positivity
    unfold basicLower lowerGapPayment
    positivity
  exact add_nonneg (hb (factors hx).1) (hb (factors hx).2.1)

def tailPaid (z : Fin 9 → ℝ) (a : ℝ) : ℝ :=
  ∑ k : Fin 9,z k*splitLower (right a 3 k/left a 3 k)

theorem tailPaid_bounds {z : Fin 9 → ℝ} (hz : ∀ k,0 ≤ z k) {a : ℝ}
    (ha : 1 ≤ a) (ha3 : a ≤ 3) : 0 ≤ tailPaid z a ∧ tailPaid z a ≤ tail z a := by
  have harg (k : Fin 9) : 1 ≤ right a 3 k/left a 3 k := by
    have hl : 0 < left a 3 k := by
      have hh := (clip_bounds (x := upperLeft k) ha3).1
      change a ≤ left a 3 k at hh
      linarith
    exact (one_le_div hl).mpr (cell_order a 3 k)
  constructor
  · exact Finset.sum_nonneg (fun k _ => mul_nonneg (hz k) (splitLower_nonneg (harg k)))
  · exact Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_left (splitLower_le (harg k)) (hz k))

def jCellsPaid (z : Fin 9 → ℝ) (s S : ℝ) : ℝ :=
  ∑ k : Fin 9,z k*jPaid S (jStart s S)
    (left (jStart s S-1) (S-2) k) (right (jStart s S-1) (S-2) k)

theorem jCellsPaid_le {z : Fin 9 → ℝ} (hz : ∀ k,0 ≤ z k) {s S : ℝ}
    (hA : 2 ≤ jStart s S) (hAS : jStart s S ≤ S-1) :
    jCellsPaid z s S ≤ ∑ k : Fin 9,z k*
      (CoupledJLogRecovery.fullPrimitive S (jStart s S) (right (jStart s S-1) (S-2) k)-
       CoupledJLogRecovery.fullPrimitive S (jStart s S) (left (jStart s S-1) (S-2) k)) := by
  have hab : jStart s S-1 ≤ S-2 := by linarith
  exact Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_left
    (jPaid_le hA hAS (clip_bounds hab).1 (cell_order _ _ k) (clip_bounds hab).2) (hz k))

def finite (s S : ℝ) : ℝ :=
  splitLower (4/(S-1))*SigmaExistingLogError.finiteLower NineFeedbackStrength.originalH+
  splitLower ((S-1)/(s-1))*(SigmaExistingLogError.finiteLower NineFeedbackStrength.originalH+
    tailPaid NineFeedbackStrength.originalH (S-2))/2+
  paidCells NineFeedbackStrength.originalH S+jCellsPaid NineFeedbackStrength.originalH s S/2

theorem finite_le_lower {s S : ℝ} (hs : 2 ≤ s) (hS : 3 ≤ S) (hS5 : S ≤ 5)
    (hsS : s ≤ S) (hr : 2 ≤ S-S/s) : finite s S ≤ lower s S := by
  have ha : 0 ≤ SigmaExistingLogError.finiteLower NineFeedbackStrength.originalH := by
    rw [SigmaJScalar.profile_value]
    positivity
  have h0 : 1 ≤ 4/(S-1) := (one_le_div (by linarith : 0 < S-1)).mpr (by linarith)
  have h1 : 1 ≤ (S-1)/(s-1) := (one_le_div (by linarith : 0 < s-1)).mpr (by linarith)
  have ht := tailPaid_bounds originalH_nonneg (by linarith : 1 ≤ S-2) (by linarith : S-2 ≤ 3)
  have he := mul_le_mul_of_nonneg_right (splitLower_le h0) ha
  have hm := mul_le_mul (splitLower_le h1) (show SigmaExistingLogError.finiteLower NineFeedbackStrength.originalH+tailPaid NineFeedbackStrength.originalH (S-2) ≤
      SigmaExistingLogError.finiteLower NineFeedbackStrength.originalH+tail NineFeedbackStrength.originalH (S-2)
      from add_le_add le_rfl ht.2)
    (add_nonneg ha ht.1) (log_nonneg h1)
  have hAS : jStart s S ≤ S-1 := by
    have h := (one_le_div (by linarith : 0 < s)).mpr hsS
    unfold jStart
    linarith
  have hj := jCellsPaid_le originalH_nonneg hr hAS
  unfold finite lower SigmaJJoint.firstCoefficient CoupledJLogRecovery.jRest
  linarith only [he,hm,hj]

theorem finite_original_rows (i : Fin 5) : finite (firstNode i) (firstS i) ≤
    firstFeedback NineFeedbackStrength.originalH (firstNode i) (firstS i) := by
  refine (finite_le_lower ?_ ?_ ?_ ?_ ?_).trans (lower_original_rows i)
  all_goals
    rcases i with ⟨i,hi⟩
    have h : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 := by omega
    rcases h with rfl | rfl | rfl | rfl | rfl
    all_goals norm_num [firstNode,firstS]
end
end RemainingHf
