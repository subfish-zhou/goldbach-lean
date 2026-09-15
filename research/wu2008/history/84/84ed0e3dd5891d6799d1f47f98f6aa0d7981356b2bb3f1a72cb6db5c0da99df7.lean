import Hf4QuadAggregate
import Hf4DEDenominator

noncomputable section
namespace WuTarget.W06
open Real Set MeasureTheory NodeExtension FirstFeedbackIntegrals
open SigmaActualBlockSeparable
open scoped Interval BigOperators

def massLower : Fin 9 → ℝ :=
  ![111258826147199/6000000000000000, 11015108859877/3000000000000000,
    795917363183/200000000000000, 400954892897/93750000000000,
    27380225768713/6000000000000000, 75612009467/15625000000000,
    10208761954023/2000000000000000, 267961103141/50000000000000,
    700494974059/125000000000000]

theorem massLower_pos (k : Fin 9) : 0 < massLower k := by
  fin_cases k <;> norm_num [massLower]

theorem massLower_le (k : Fin 9) :
    massLower k ≤ endpointCellMass (upperLeft k) (upperNode k) := by
  fin_cases k
  · simpa [massLower, upperLeft, upperNode] using Hf4Quad.cell0_bounds.1
  · simpa [massLower, upperLeft, upperNode] using Hf4Quad.cell1_bounds.1
  · simpa [massLower, upperLeft, upperNode] using Hf4Quad.cell2_bounds.1
  · simpa [massLower, upperLeft, upperNode] using Hf4Quad.cell3_bounds.1
  · simpa [massLower, upperLeft, upperNode] using Hf4Quad.cell4_bounds.1
  · simpa [massLower, upperLeft, upperNode] using Hf4Quad.cell5_bounds.1
  · simpa [massLower, upperLeft, upperNode] using Hf4Quad.cell6_bounds.1
  · simpa [massLower, upperLeft, upperNode] using Hf4Quad.cell7_bounds.1
  · simpa [massLower, upperLeft, upperNode] using Hf4Quad.cell8_bounds.1

def numeratorLower (z : Fin 9 → ℝ) : ℝ := ∑ k, z k * massLower k

theorem numeratorLower_nonneg {z : Fin 9 → ℝ} (hz : ∀ k, 0 ≤ z k) :
    0 ≤ numeratorLower z :=
  Finset.sum_nonneg (fun k _ => mul_nonneg (hz k) (massLower_pos k).le)

theorem numeratorLower_le_endpoint {z : Fin 9 → ℝ} (hz : ∀ k, 0 ≤ z k) :
    numeratorLower z ≤ endpointNumerator z :=
  Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_left (massLower_le k) (hz k))

theorem endpointNumerator_le_actual {z : Fin 9 → ℝ} (hz : ∀ k, 0 ≤ z k) :
    endpointNumerator z ≤
      ∫ t in (1:ℝ)..3, nineProfile z t / t * sigma 3 (t+2) (t+1) := by
  rw [endpointNumerator_eq_integral]
  have hp := nineProfile_integrable z
  apply intervalIntegral.integral_mono_on (by norm_num)
    (hp.mul_continuousOn SigmaVariableOuterPayment.paidWeight_continuous)
    ((profile_div_integrable hp).mul_continuousOn
      OriginalProfileSigmaPayment.original_sigma_continuous)
  intro t ht
  have h := mul_le_mul_of_nonneg_left
    ((SigmaVariableOuterPayment.paidWeight_le ht).trans
      (SigmaVariableFull.weight_le_sigma ht)) (nineProfile_nonneg hz t)
  convert h using 1 <;> first | rfl | ring

theorem numeratorLower_le_actual {z : Fin 9 → ℝ} (hz : ∀ k, 0 ≤ z k) :
    numeratorLower z ≤
      ∫ t in (1:ℝ)..3, nineProfile z t / t * sigma 3 (t+2) (t+1) :=
  (numeratorLower_le_endpoint hz).trans (endpointNumerator_le_actual hz)

def denominatorLower : ℝ := 858467/5000000

theorem denominatorLower_le : denominatorLower ≤ D0 :=
  Hf4DE.dPaid_bounds.1.trans D0FullDensity.dPaid_le

theorem denominator_pos : 0 < 1 - denominatorLower := by
  norm_num [denominatorLower]

def sigmaCoeff (k : Fin 9) : ℝ := massLower k / (1 - denominatorLower)

def sigmaLower (z : Fin 9 → ℝ) : ℝ := ∑ k, sigmaCoeff k * z k

theorem sigmaCoeff_pos (k : Fin 9) : 0 < sigmaCoeff k :=
  div_pos (massLower_pos k) denominator_pos

theorem sigmaLower_nonneg {z : Fin 9 → ℝ} (hz : ∀ k, 0 ≤ z k) :
    0 ≤ sigmaLower z :=
  Finset.sum_nonneg (fun k _ => mul_nonneg (sigmaCoeff_pos k).le (hz k))

theorem sigmaLower_eq (z : Fin 9 → ℝ) :
    sigmaLower z = numeratorLower z / (1 - denominatorLower) := by
  unfold sigmaLower sigmaCoeff numeratorLower
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem sigmaLower_le_aProfile {z : Fin 9 → ℝ} (hz : ∀ k, 0 ≤ z k) :
    sigmaLower z ≤ aProfile (nineProfile z) := by
  rw [sigmaLower_eq, aProfile_eq]
  calc
    _ ≤ numeratorLower z / (1-D0) :=
      div_le_div_of_nonneg_left (numeratorLower_nonneg hz)
        (sub_pos.mpr D0_lt_one) (by linarith only [denominatorLower_le])
    _ ≤ _ := div_le_div_of_nonneg_right (numeratorLower_le_actual hz)
      (sub_pos.mpr D0_lt_one).le

theorem sigmaLower_basis (k : Fin 9) : sigmaLower (nodeBasis k) = sigmaCoeff k := by
  simp [sigmaLower, nodeBasis]

theorem sigmaCoeff_le_aProfile (k : Fin 9) :
    sigmaCoeff k ≤ aProfile (nineProfile (nodeBasis k)) := by
  rw [← sigmaLower_basis]
  exact sigmaLower_le_aProfile (nodeBasis_nonneg k)

end WuTarget.W06
