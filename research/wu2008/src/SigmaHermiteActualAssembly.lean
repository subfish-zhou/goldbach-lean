import SigmaHermiteActualComponent0
import SigmaHermiteActualComponent1
import SigmaHermiteActualComponent2
import SigmaHermiteActualComponent3
import SigmaHermiteActualComponent4
import SigmaHermiteActualComponent5
import SigmaHermiteActualComponent6
import SigmaHermiteActualComponent7
import SigmaHermiteComponent8

noncomputable section
namespace SigmaHermiteActualFTC
open Polynomial Real Set SigmaRationalOuterFTC SigmaVariableOuterPayment

theorem splitLower_fraction {n d : ℝ} (hn : 0<n) (hd : 0<d) :
    splitLowerNum n d/splitLowerDen n d =
      lowerNum (n+d) (2*d)/lowerDen (n+d) (2*d)+
      lowerNum (2*n) (n+d)/lowerDen (2*n) (n+d) := by
  unfold splitLowerNum splitLowerDen
  rw [div_add_div _ _ (lowerDen_pos (add_pos hn hd) (by positivity)).ne'
    (lowerDen_pos (by positivity) (add_pos hn hd)).ne']
  ring

theorem splitUpper_fraction {n d : ℝ} (hn : 0<n) (hd : 0<d) :
    splitUpperNum n d/splitUpperDen n d =
      upperNum (n+d) (2*d)/upperDen (n+d) (2*d)+
      upperNum (2*n) (n+d)/upperDen (2*n) (n+d) := by
  unfold splitUpperNum splitUpperDen
  rw [div_add_div _ _ (upperDen_pos (add_pos hn hd) (by positivity)).ne'
    (upperDen_pos (by positivity) (add_pos hn hd)).ne']
  ring

theorem component8_actual (t : ℝ) :
    jointNum t/jointDen t = component8Kernel t := by
  unfold jointNum jointDen component8Kernel
  simp only [block0, block1, block3, eval_mul, eval_add, eval_C, eval_X]
  ring

/-- Exact assembly of all eight original split contributions and both joint endpoints. -/
theorem paidWeight_components {t : ℝ} (ht : t ∈ Icc 1 3) :
    paidWeight t = component0Kernel t+component1Kernel t+
      component2Kernel t+component3Kernel t+component4Kernel t+
      component5Kernel t+component6Kernel t+component7Kernel t+component8Kernel t := by
  rw [paidWeight_homogeneous ht]
  have hnD : 0<negD t := by unfold negD; linarith [ht.1]
  have hnN : 0<negN t := by unfold negN; have h := ht.1; positivity
  have hqD : 0<quadD t := by unfold quadD; have h := ht.1; positivity
  have hqN : 0<quadN t := by unfold quadN; have h := ht.1; positivity
  have hrD := radD_pos ht.1
  have hrN : 0<radN t := by
    unfold radN
    have hr := TerminalE.radical_pos
    have hm : 0<t+9-2*TerminalE.radical := by linarith [ht.1, TerminalE.radical_lt_four]
    positivity
  unfold homogeneousWeight
  rw [splitUpper_fraction (by linarith [ht.1] : 0<t+2) (by norm_num : (0:ℝ)<3),
    splitLower_fraction hnN hnD, splitLower_fraction hqN hqD,
    splitLower_fraction hrN hrD, component8_actual]
  rw [←actual0_weight_kernel, ←actual1_weight_kernel, ←actual2_weight_kernel,
    ←actual3_weight_kernel, ←actual4_weight_kernel, ←actual5_weight_kernel,
    ←actual6_weight_kernel, ←actual7_weight_kernel]
  unfold actual0Weight actual1Weight actual2Weight actual3Weight actual4Weight
    actual5Weight actual6Weight actual7Weight
  ring

/-- The fixed Hermite kernel retains every simple remainder and every rational principal part. -/
def completeHermiteKernel (t : ℝ) : ℝ :=
  component0HermiteKernel t+component1HermiteKernel t+
  component2HermiteKernel t+component3HermiteKernel t+component4HermiteKernel t+
  component5HermiteKernel t+component6HermiteKernel t+component7HermiteKernel t+
  component8HermiteKernel t

theorem paidWeight_completeHermite {t : ℝ} (ht : t ∈ Icc 1 3) :
    paidWeight t = completeHermiteKernel t := by
  rw [paidWeight_components ht]
  rw [component0_hermite ht, component1_hermite ht, component2_hermite ht,
    component3_hermite ht, component4_hermite ht, component5_hermite ht,
    component6_hermite ht, component7_hermite ht, component8_hermite ht]
  rfl

end SigmaHermiteActualFTC
