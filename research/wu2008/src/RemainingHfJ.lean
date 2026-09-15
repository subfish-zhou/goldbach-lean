import RemainingHfRows
namespace RemainingHf
open Real Wu2008DoubleSieve FiniteEndpointPayment FirstErrorFullPayment CoupledJLogRecovery
noncomputable section

def jPaid (S A a b : ℝ) : ℝ :=
  let q := -(2*S-A-1)
  let v := -2*(S-A)
  let d := 2/(21*A)
  let e := 3/(34*(S-A))
  signed (pa (A+1) (2*A)-pa q v+d*qa (A+1)+e*ra (S-A) (S-1)) (b/a)+
  signed (pb (A+1) (2*A)+d*qc (A+1)) ((b+A+1)/(a+A+1))+
  signed (pb q v+e*rc (S-A) (S-1)) ((a+q)/(b+q))+
  signed (d*qb (A+1)) ((b+1)/(a+1))+
  signed (e*rb (S-A) (S-1)) ((S-1-a)/(S-1-b))+
  (d+e)*(b-a)-
  (pc (A+1) (2*A)+d*qd (A+1))*(1/(b+A+1)-1/(a+A+1))-
  (pd (A+1) (2*A)+d*qe (A+1))/2*(1/(b+A+1)^2-1/(a+A+1)^2)+
  (pc q v-e*rd (S-A) (S-1))*(1/(b+q)-1/(a+q))+
  (pd q v+e*re (S-A) (S-1))/2*(1/(b+q)^2-1/(a+q)^2)

theorem jPaid_le {S A a b : ℝ} (hA : 2 ≤ A) (hAS : A ≤ S-1)
    (ha : A-1 ≤ a) (hab : a ≤ b) (hb : b ≤ S-2) :
    jPaid S A a b ≤ fullPrimitive S A b-fullPrimitive S A a := by
  let q := -(2*S-A-1)
  let v := -2*(S-A)
  let d := 2/(21*A)
  let e := 3/(34*(S-A))
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have ha1 : 0 < a+1 := by linarith
  have hb1 : 0 < b+1 := by linarith
  have haA : 0 < a+A+1 := by linarith
  have hbA : 0 < b+A+1 := by linarith
  have haQ : a+q < 0 := by dsimp [q]; linarith
  have hbQ : b+q < 0 := by dsimp [q]; linarith
  have hda : 0 < S-1-a := by linarith
  have hdb : 0 < S-1-b := by linarith
  have h0 := signed_le (pa (A+1) (2*A)-pa q v+d*qa (A+1)+e*ra (S-A) (S-1))
    ((one_le_div ha0).mpr hab)
  have h1 := signed_le (pb (A+1) (2*A)+d*qc (A+1))
    ((one_le_div haA).mpr (by linarith : a+A+1 ≤ b+A+1))
  have h2 := signed_le (pb q v+e*rc (S-A) (S-1))
    ((one_le_div_of_neg hbQ).mpr (by linarith : a+q ≤ b+q))
  have h3 := signed_le (d*qb (A+1))
    ((one_le_div ha1).mpr (by linarith : a+1 ≤ b+1))
  have h4 := signed_le (e*rb (S-A) (S-1))
    ((one_le_div hdb).mpr (by linarith : S-1-b ≤ S-1-a))
  rw [log_div hb0.ne' ha0.ne'] at h0
  rw [log_div hbA.ne' haA.ne'] at h1
  rw [log_div haQ.ne hbQ.ne] at h2
  rw [log_div hb1.ne' ha1.ne'] at h3
  rw [log_div hda.ne' hdb.ne'] at h4
  have heA : A+1-1=A := by ring
  have hea : S-1+(S-A)-a=-(a+q) := by dsimp [q]; ring
  have heb : S-1+(S-A)-b=-(b+q) := by dsimp [q]; ring
  unfold fullPrimitive jPrimitive FiniteEndpointPayment.primitive errorPrimitive secondPrimitive
  dsimp only
  rw [hea,heb,log_neg_eq_log,log_neg_eq_log]
  dsimp [jPaid,q,v,d,e] at h0 h1 h2 h3 h4 ⊢
  simp only [heA,div_eq_mul_inv,mul_inv_rev,inv_neg] at h0 h1 h2 h3 h4 ⊢
  ring_nf at h0 h1 h2 h3 h4 ⊢
  linarith only [h0,h1,h2,h3,h4]
end
end RemainingHf
