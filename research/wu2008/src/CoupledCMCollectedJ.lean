import CubicMiddleJoint

namespace CoupledCMCollectedJ
open Real FiniteEndpointPayment Wu04WholeCollection
noncomputable section

/-- Common endpoint logarithms are combined before any signed payment. -/
def cell (S A a b : ℝ) : ℝ :=
  (pa (1+A) (2*A)-pa (-(2*S-A-1)) (-2*(S-A)))*log (b/a)+
  pb (1+A) (2*A)*log ((b+(1+A))/(a+(1+A)))-
  pb (-(2*S-A-1)) (-2*(S-A))*log ((b-(2*S-A-1))/(a-(2*S-A-1)))-
  pc (1+A) (2*A)*(1/(b+(1+A))-1/(a+(1+A)))+
  pc (-(2*S-A-1)) (-2*(S-A))*(1/(b-(2*S-A-1))-1/(a-(2*S-A-1)))-
  pd (1+A) (2*A)/2*(1/(b+(1+A))^2-1/(a+(1+A))^2)+
  pd (-(2*S-A-1)) (-2*(S-A))/2*
    (1/(b-(2*S-A-1))^2-1/(a-(2*S-A-1))^2)

theorem cell_exact {S A a b : ℝ} (ha : a≠0) (hb : b≠0)
    (haq : a+(1+A)≠0) (hbq : b+(1+A)≠0)
    (har : a-(2*S-A-1)≠0) (hbr : b-(2*S-A-1)≠0) :
    cell S A a b=jPrimitive S A b-jPrimitive S A a := by
  unfold cell jPrimitive primitive
  rw [log_div hb ha,log_div hbq haq,log_div hbr har]
  simp only [sub_eq_add_neg,div_eq_mul_inv,mul_inv_rev]
  ring

/-- Signed, once-split logarithmic payment for this collected original J cell. -/
def paidCell (S A a b : ℝ) : ℝ :=
  signedLow (pa (1+A) (2*A)-pa (-(2*S-A-1)) (-2*(S-A))) (b/a)+
  signedLow (pb (1+A) (2*A)) ((b+(1+A))/(a+(1+A)))+
  signedLow (-pb (-(2*S-A-1)) (-2*(S-A))) ((b-(2*S-A-1))/(a-(2*S-A-1)))-
  pc (1+A) (2*A)*(1/(b+(1+A))-1/(a+(1+A)))+
  pc (-(2*S-A-1)) (-2*(S-A))*(1/(b-(2*S-A-1))-1/(a-(2*S-A-1)))-
  pd (1+A) (2*A)/2*(1/(b+(1+A))^2-1/(a+(1+A))^2)+
  pd (-(2*S-A-1)) (-2*(S-A))/2*
    (1/(b-(2*S-A-1))^2-1/(a-(2*S-A-1))^2)

theorem paidCell_le {S A a b : ℝ} (h0 : 0<b/a)
    (h1 : 0<(b+(1+A))/(a+(1+A)))
    (h2 : 0<(b-(2*S-A-1))/(a-(2*S-A-1))) :
    paidCell S A a b≤cell S A a b := by
  have h := signed_bound (pa (1+A) (2*A)-pa (-(2*S-A-1)) (-2*(S-A))) h0
  have h' := signed_bound (pb (1+A) (2*A)) h1
  have h'' := signed_bound (-pb (-(2*S-A-1)) (-2*(S-A))) h2
  unfold paidCell cell
  linarith only [h,h',h'']

end
end CoupledCMCollectedJ
