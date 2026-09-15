import RemainingHfFinite
import ResidualEndpointJoint

namespace SigmaRemaining
open Real OriginalSigmaStrength NodeExtension FirstFeedbackIntegrals
open scoped BigOperators
noncomputable section

/-- Pay each complete collected pole with the inherited single split. -/
def polePaid (r c1 c2 c3 a b : ℝ) : ℝ :=
  RemainingHf.signed c1 ((b+r)/(a+r))-c2*(1/(b+r)-1/(a+r))-
    c3/2*(1/(b+r)^2-1/(a+r)^2)

theorem polePaid_le (r c1 c2 c3 : ℝ) {a b : ℝ}
    (ha : 0<a+r) (hab : a≤b) :
    polePaid r c1 c2 c3 a b ≤ polePrimitive r c1 c2 c3 b-polePrimitive r c1 c2 c3 a := by
  have hb : 0<b+r := by linarith
  have hx : 1≤(b+r)/(a+r) := (one_le_div ha).mpr (by linarith)
  have h := RemainingHf.signed_le c1 hx
  rw [log_div hb.ne' ha.ne'] at h
  unfold polePaid polePrimitive
  simp only [div_eq_mul_inv,mul_inv_rev] at h ⊢
  linarith only [h]

/-- The old primitive, not an additional whole-sigma lower bound. -/
def cellPaid (a b : ℝ) : ℝ :=
  (80/1323)*(b-a)+(b^2-a^2)/1323+
  polePaid 0 (1818722/12403125) (1556/6890625) (-106/1378125) a b-
  (4/275625)/3*(1/b^3-1/a^3)+
  polePaid 1 (-227/2646) 0 0 a b+
  polePaid 3 (-20576/19845) (2752/1323) (-512/441) a b+
  polePaid 5 (1129701/306250) (-1270998/153125) (525528/30625) a b+
  polePaid (5/3) (-286208/212625) (2584576/11390625) (-1212416/6834375) a b

theorem cellPaid_le {a b : ℝ} (ha : 0<a) (hab : a≤b) :
    cellPaid a b ≤ SigmaExistingLogError.primitive b-SigmaExistingLogError.primitive a := by
  have h0 := polePaid_le 0 (1818722/12403125) (1556/6890625) (-106/1378125)
    (by linarith : 0<a+0) hab
  have h1 := polePaid_le 1 (-227/2646) 0 0 (by linarith : 0<a+1) hab
  have h3 := polePaid_le 3 (-20576/19845) (2752/1323) (-512/441)
    (by linarith : 0<a+3) hab
  have h5 := polePaid_le 5 (1129701/306250) (-1270998/153125) (525528/30625)
    (by linarith : 0<a+5) hab
  have h53 := polePaid_le (5/3) (-286208/212625) (2584576/11390625) (-1212416/6834375)
    (by linarith : 0<a+5/3) hab
  unfold cellPaid SigmaExistingLogError.primitive
  simp only [div_eq_mul_inv,mul_inv_rev]
  linarith only [h0,h1,h3,h5,h53]

def numerator (z : Fin 9 → ℝ) : ℝ :=
  ∑ k : Fin 9,z k*cellPaid (upperLeft k) (upperNode k)

theorem numerator_le {z : Fin 9 → ℝ} (hz : ∀ k,0≤z k) :
    numerator z ≤ SigmaExistingLogError.numerator z := by
  apply Finset.sum_le_sum
  intro k _
  have hc := cell_bounds (a := 1) le_rfl (by norm_num [upperNode]) k
  have he : cellLeft 1 k=upperLeft k := by
    unfold cellLeft upperLeft
    split_ifs <;> rfl
  rw [he] at hc
  exact mul_le_mul_of_nonneg_left (cellPaid_le (by linarith [hc.1]) hc.2.1) (hz k)

end
end SigmaRemaining
