import SigmaJEndpointRows

namespace SigmaJEndpoint
open Real Set MeasureTheory Wu2008DoubleSieve NodeExtension ActualNineFeedback
open CoupledIntegralRecovery FiniteEndpointPayment FirstErrorFullPayment
noncomputable section

theorem maxima_attained {S A : ℝ} (hAS : A ≤ S-1) :
    (((S-2)+1)/A=(S-1)/A) ∧ ((S-A)/(S-1-(S-2))=S-A) ∧
      S-2 ∈ Icc (A-1) (S-2) := by
  constructor
  · congr 1; ring
  constructor
  · rw [show S-1-(S-2)=(1:ℝ) by ring,div_one]
  · exact ⟨by linarith,le_rfl⟩

theorem scales_ge_one {S A : ℝ} (hA : 2 ≤ A) (hAS : A ≤ S-1) (hS5 : S ≤ 5) :
    1 ≤ firstScale S A ∧ 1 ≤ secondScale S A := by
  have hx : 1 ≤ (S-1)/A := (one_le_div (by linarith : 0 < A)).mpr hAS
  have hx2 : (S-1)/A ≤ 2 := (div_le_iff₀ (by linarith : 0 < A)).mpr (by linarith)
  have hy : 1 ≤ S-A := by linarith
  have hy3 : S-A ≤ 3 := by linarith
  have hf := coefficient_antitone hx hx2
  have hs := coefficient_antitone hy hy3
  norm_num [coefficient] at hf hs
  constructor
  · exact (one_le_div (by norm_num : (0:ℝ) < 4/7)).mpr hf
  · exact (one_le_div (by norm_num : (0:ℝ) < 9/17)).mpr hs

theorem old_kernel_le_endpoint {S A u : ℝ} (hA : 2 ≤ A) (hAS : A ≤ S-1)
    (hS5 : S ≤ 5) (hu : u ∈ Icc (A-1) (S-2)) :
    CoupledJLogRecovery.kernel S A u ≤ endpointKernel S A u := by
  obtain ⟨hf,hs⟩ := scales_ge_one hA hAS hS5
  have he := CoupledJLogRecovery.firstError_nonneg hA hu.1
  have ht := CoupledJLogRecovery.secondError_nonneg hA hAS hu
  have h1 := mul_le_mul_of_nonneg_right hf he
  have h2 := mul_le_mul_of_nonneg_right hs ht
  unfold CoupledJLogRecovery.kernel endpointKernel
  linarith only [h1,h2]

theorem primitive_replacement_exact (S A a b : ℝ) :
    (endpointPrimitive S A b-endpointPrimitive S A a)-
      (CoupledJLogRecovery.fullPrimitive S A b-CoupledJLogRecovery.fullPrimitive S A a)=
    (firstScale S A-1)*(errorPrimitive (A+1) b-errorPrimitive (A+1) a)+
    (secondScale S A-1)*(CoupledJLogRecovery.secondPrimitive S A b-CoupledJLogRecovery.secondPrimitive S A a) := by
  unfold endpointPrimitive CoupledJLogRecovery.fullPrimitive
  ring

end
end SigmaJEndpoint
