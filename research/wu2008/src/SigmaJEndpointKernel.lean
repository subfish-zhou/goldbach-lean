import SigmaJJoint

namespace SigmaJEndpoint
open Real Set Wu2008DoubleSieve SharpLogRecurrence
open CoupledJLogRecovery FirstErrorFullPayment FiniteEndpointPayment CoupledIntegralRecovery
noncomputable section

def coefficient (x : ℝ) : ℝ := 6*x/(x^2+8*x+1)

theorem coefficient_antitone {x B : ℝ} (hx : 1 ≤ x) (hxB : x ≤ B) :
    coefficient B ≤ coefficient x := by
  have hB : 1 ≤ B := hx.trans hxB
  have hd : 0 < x^2+8*x+1 := by positivity
  have he : 0 < B^2+8*B+1 := by positivity
  unfold coefficient
  apply (div_le_div_iff₀ he hd).mpr
  have hprod : 0 ≤ B*x-1 := by nlinarith [mul_nonneg (by linarith : 0 ≤ B-1) (by linarith : 0 ≤ x-1)]
  nlinarith [mul_nonneg (sub_nonneg.mpr hxB) hprod]

theorem endpoint_error {x B : ℝ} (hx : 1 ≤ x) (hxB : x ≤ B) :
    coefficient B*(upperLog x-lowerLog x) ≤ log x-lowerLog x := by
  have hgap : 0 ≤ upperLog x-lowerLog x := by
    rw [OriginalFirstErrorRecovery.envelope_gap (by linarith : 0 < x)]
    positivity
  exact (mul_le_mul_of_nonneg_right (coefficient_antitone hx hxB) hgap).trans
    (F1FullRecoveryPayment.lowerGapPayment_le hx)

def firstScale (S A : ℝ) : ℝ := coefficient ((S-1)/A)/(4/7)
def secondScale (S A : ℝ) : ℝ := coefficient (S-A)/(9/17)
def endpointKernel (S A u : ℝ) : ℝ :=
  jKernel S A u+firstScale S A*errorDensity (A+1) u+
    secondScale S A*secondError S A u

theorem actual_argument_bounds {S A u : ℝ} (hA : 2 ≤ A) (hAS : A ≤ S-1)
    (hu : u ∈ Icc (A-1) (S-2)) :
    (1 ≤ (u+1)/A ∧ (u+1)/A ≤ (S-1)/A) ∧
    (1 ≤ (S-A)/(S-1-u) ∧ (S-A)/(S-1-u) ≤ S-A) := by
  have hA0 : 0 < A := by linarith
  have hd : 0 < S-1-u := by linarith [hu.2]
  refine ⟨⟨(one_le_div hA0).mpr (by linarith [hu.1]),
    (div_le_div_iff_of_pos_right hA0).mpr (by linarith [hu.2])⟩,
    ⟨(one_le_div hd).mpr (by linarith [hu.1]), ?_⟩⟩
  apply (div_le_iff₀ hd).mpr
  nlinarith [mul_nonneg (by linarith : 0 ≤ S-A) (by linarith [hu.2] : 0 ≤ S-2-u)]

theorem endpointKernel_le {S A u : ℝ} (hA : 2 ≤ A) (hAS : A ≤ S-1)
    (hu : u ∈ Icc (A-1) (S-2)) :
    endpointKernel S A u ≤ odds S A (u+1)/u := by
  obtain ⟨hx,hy⟩ := actual_argument_bounds hA hAS hu
  have hu0 : 0 ≤ u := by linarith [hu.1]
  have h1 := div_le_div_of_nonneg_right (endpoint_error hx.1 hx.2) hu0
  have h2 := div_le_div_of_nonneg_right (endpoint_error hy.1 hy.2) hu0
  unfold endpointKernel firstScale secondScale errorDensity secondError
  rw [jKernel_eq hA hAS hu]
  unfold odds
  simp only [add_sub_cancel_right]
  rw [show S-(u+1)=S-1-u by ring]
  simp only [sub_div,add_div] at h1 h2 ⊢
  ring_nf at h1 h2 ⊢
  linarith only [h1,h2]

end
end SigmaJEndpoint
