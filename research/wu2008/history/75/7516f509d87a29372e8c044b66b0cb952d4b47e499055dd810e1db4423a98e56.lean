import W04ExactMatrix
import W05JTableConsumer
import W06Consumers
import W07DensityMatrices
import W08Envelope
import W09ActualV2

noncomputable section
namespace WuTarget.W17Joint
open Real Set MeasureTheory Wu2008DoubleSieve NodeExtension ActualNineFeedback
open scoped Interval BigOperators

theorem paidCell_le_eRemainder {S : ℝ} (hS : 3 ≤ S)
    (hc : S - 2 ≤ upperNode 0) (k : Fin 9) :
    RemainingHf.paidCell S (FirstFeedbackIntegrals.cellLeft (S - 2) k) (upperNode k) ≤
      W06.eRemainder (nodeBasis k) S := by
  have h := W08.paidCells_le_kernel (nodeBasis_nonneg k) hS hc
  rw [W08.paidCells_basis] at h
  simpa only [W06.eRemainder, div_mul_eq_mul_div, mul_div_assoc] using h

theorem rationalJ_le_jRemainder {s S : ℝ}
    (hs : 2 ≤ s) (hS : 3 ≤ S) (hS5 : S ≤ 5)
    (hsS : s ≤ S) (hr : 2 ≤ S - S / s) (k : Fin 9) :
    W05.rationalJCoefficient s S k ≤ W06.jRemainder (nodeBasis k) s S := by
  have h := W05.rationalJCoefficients_paid (nodeBasis_nonneg k) hs hS hS5 hsS hr
  classical
  simp only [nodeBasis, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true] at h
  rw [W06.profileJ_split (nodeBasis k) hs hS hS5 hsS hr] at h
  unfold W06.jCoefficient at h
  linarith only [h]

def remainderMatrix (i k : Fin 9) : ℝ :=
  W08.paidMatrix i k + W04.extraMatrix i k + W05.jTable i k + W07.paidMatrix i k

theorem remainderMatrix_nonneg (i k : Fin 9) : 0 ≤ remainderMatrix i k :=
  add_nonneg (add_nonneg (add_nonneg (W08.paidMatrix_nonneg i k)
    (W04.extraMatrix_nonneg i k)) (W05.jTable_nonneg i k)) (W07.paidMatrix_nonneg i k)

/-- Each summand is paid from a different term of the same non-Sigma remainder. -/
theorem remainderMatrix_le (i k : Fin 9) :
    remainderMatrix i k ≤ W06.nonSigmaMatrix i k := by
  unfold remainderMatrix
  rw [W05.jTable_eq]
  unfold W08.paidMatrix W04.extraMatrix W04.coupledExtra
    W05.rationalJMatrix W05.assembleJ W07.paidMatrix
    W06.nonSigmaMatrix W06.rowRemainder
  split_ifs with h
  · let j : Fin 4 := ⟨i.val, h⟩
    have hp := coupledRow_geometry j
    have hg := coupled_geometry_bounds hp
    have hS := W04.clippedCell_le_eKernel hp.1.three_le_S hp.1.S_le_five k
    change W04.clippedCell (coupledRow j).S k ≤
      W06.eRemainder (nodeBasis k) (coupledRow j).S at hS
    have hE := paidCell_le_eRemainder hp.2.1 (Wu04Bypass.coupled_kappa_cell j) k
    have hj0 := rationalJ_le_jRemainder hg.1 hp.1.three_le_S hp.1.S_le_five
      hg.2.1 hp.2.2.1 k
    have hj2 := rationalJ_le_jRemainder hg.2.2.1 hp.1.three_le_S hp.1.S_le_five
      hg.2.2.2.1 hp.2.2.2.1 k
    have hj3 := rationalJ_le_jRemainder hg.2.2.2.2.1 hp.1.three_le_S hp.1.S_le_five
      hg.2.2.2.2.2.1 hp.2.2.2.2 k
    have hd := W07.paidTable_le_densityEntry j k
    rw [W07.densityEntry_eq_basis _ hp.1] at hd
    unfold W06.coupledRemainder
    linarith only [hS, hE, hj0, hj2, hj3, hd]
  · let j : Fin 5 := ⟨i.val - 4, by omega⟩
    have hg := first_geometry j
    have hE := paidCell_le_eRemainder hg.2.2.1 (Wu04Bypass.first_cell j) k
    have hJ := rationalJ_le_jRemainder hg.1 hg.2.2.1 hg.2.2.2.1
      (hg.2.1.trans hg.2.2.1) hg.2.2.2.2 k
    unfold W06.firstRemainder
    linarith only [hE, hJ]

def eWeightLower (S : ℝ) : ℝ := (5 - S) / 4
def jWeightLower (s S : ℝ) : ℝ := (S - s) / (S - 1)

theorem eWeightLower_bounds {S : ℝ} (hS : 3 ≤ S) (hS5 : S ≤ 5) :
    0 ≤ eWeightLower S ∧ eWeightLower S ≤ W06.eCoefficient S := by
  constructor
  · unfold eWeightLower
    positivity
  · have h := W05.endpoint_log_lower (by linarith : 0 < S - 1)
      (by linarith : S - 1 ≤ 4)
    unfold eWeightLower W06.eCoefficient
    linarith only [h]

theorem jWeightLower_bounds {s S : ℝ} (hs : 2 ≤ s) (hsS : s ≤ S) :
    0 ≤ jWeightLower s S ∧ jWeightLower s S ≤ W06.jCoefficient s S := by
  constructor
  · unfold jWeightLower
    exact div_nonneg (sub_nonneg.mpr hsS) (by linarith)
  · have h := W05.endpoint_log_lower (by linarith : 0 < s - 1)
      (by linarith : s - 1 ≤ S - 1)
    unfold jWeightLower W06.jCoefficient
    convert h using 1 <;> congr 1 <;> ring

def rowWeightLower (i : Fin 9) : ℝ :=
  if h : i.val < 4 then
    (4 * eWeightLower (coupledRow ⟨i.val, h⟩).S +
      eWeightLower (coupledRow ⟨i.val, h⟩).kappa1 +
      jWeightLower (coupledRow ⟨i.val, h⟩).s (coupledRow ⟨i.val, h⟩).S +
      jWeightLower (coupledRow ⟨i.val, h⟩).kappa2 (coupledRow ⟨i.val, h⟩).S +
      jWeightLower (coupledRow ⟨i.val, h⟩).kappa3 (coupledRow ⟨i.val, h⟩).S) / 5
  else eWeightLower (firstS ⟨i.val - 4, by omega⟩) +
    jWeightLower (firstNode ⟨i.val - 4, by omega⟩) (firstS ⟨i.val - 4, by omega⟩) / 2

theorem rowWeightLower_bounds (i : Fin 9) :
    0 ≤ rowWeightLower i ∧ rowWeightLower i ≤ W06.rowCoefficient i := by
  unfold rowWeightLower W06.rowCoefficient
  split_ifs with h
  · have hp := coupledRow_geometry ⟨i.val, h⟩
    have hg := coupled_geometry_bounds hp
    have h0 := eWeightLower_bounds hp.1.three_le_S hp.1.S_le_five
    have h1 := eWeightLower_bounds hp.2.1 hg.2.2.2.2.2.2
    have hj0 := jWeightLower_bounds hg.1 hg.2.1
    have hj2 := jWeightLower_bounds hg.2.2.1 hg.2.2.2.1
    have hj3 := jWeightLower_bounds hg.2.2.2.2.1 hg.2.2.2.2.2.1
    unfold W06.coupledCoefficient
    constructor <;> linarith only [h0.1, h0.2, h1.1, h1.2,
      hj0.1, hj0.2, hj2.1, hj2.2, hj3.1, hj3.2]
  · have hg := first_geometry (⟨i.val - 4, by omega⟩ : Fin 5)
    have hE := eWeightLower_bounds hg.2.2.1 hg.2.2.2.1
    have hJ := jWeightLower_bounds hg.1 (hg.2.1.trans hg.2.2.1)
    unfold W06.firstCoefficient
    constructor <;> linarith only [hE.1, hE.2, hJ.1, hJ.2]

def rationalSigmaMatrix (i k : Fin 9) : ℝ := rowWeightLower i * W06.sigmaCoeff k

theorem rationalSigmaMatrix_nonneg (i k : Fin 9) : 0 ≤ rationalSigmaMatrix i k :=
  mul_nonneg (rowWeightLower_bounds i).1 (W06.sigmaCoeff_pos k).le

theorem rationalSigmaMatrix_le (i k : Fin 9) :
    rationalSigmaMatrix i k ≤ W06.sigmaMatrix i k :=
  mul_le_mul_of_nonneg_right (rowWeightLower_bounds i).2 (W06.sigmaCoeff_pos k).le

def jointMatrix (i k : Fin 9) : ℝ := rationalSigmaMatrix i k + remainderMatrix i k

theorem jointMatrix_nonneg (i k : Fin 9) : 0 ≤ jointMatrix i k :=
  add_nonneg (rationalSigmaMatrix_nonneg i k) (remainderMatrix_nonneg i k)

theorem jointMatrix_le_feedbackMatrix (i k : Fin 9) :
    jointMatrix i k ≤ feedbackMatrix i k :=
  (add_le_add (rationalSigmaMatrix_le i k) (remainderMatrix_le i k)).trans
    (W06.sigmaMatrix_add_nonSigma_le i k)

theorem baseline_le_jointMatrix (i k : Fin 9) : Wu04Bypass.M i k ≤ jointMatrix i k := by
  have h := (W04.oldMatrix_le_elementary i k).trans (W08.elementaryMatrix_le_paidMatrix i k)
  have h0 := rationalSigmaMatrix_nonneg i k
  have h1 := W04.extraMatrix_nonneg i k
  have h2 := W05.jTable_nonneg i k
  have h3 := W07.paidMatrix_nonneg i k
  unfold jointMatrix remainderMatrix
  linarith only [h, h0, h1, h2, h3]

end WuTarget.W17Joint
