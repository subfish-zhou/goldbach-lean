import SigmaSignedCellsAlgebra
namespace SigmaSignedCells
open Real SigmaRemaining OriginalSigmaStrength
noncomputable section

/-- Complete new primitive payment, retaining the fourth-order contribution. -/
def cellPaid (a b : ℝ) : ℝ :=
  (22/189)*(b-a)+
  polePaid 0 (3117833702/21271359375) (740716/3038765625) (-2306/28940625) a b-
  (4/275625)/3*(1/b^3-1/a^3)+
  polePaid 3 (-4432/2835) (352/189) (-128/63) a b+
  polePaid 5 (4752318/1164625) (-23702004/2646875) (850824/48125) a b+
  polePaid (5/3) (-73544192/186046875) (22433792/79734375) (-557056/6834375) a b+
  quadraticPaid (-438353120/201331053) (-21945288920/1811979477) a b

theorem cellPaid_le {a b : ℝ} (ha : 1≤a) (hab : a≤b) :
    cellPaid a b ≤ SigmaPrimitiveCells.cellMass a b := by
  have h0 := polePaid_le 0 (3117833702/21271359375) (740716/3038765625) (-2306/28940625)
    (by linarith : 0<a+0) hab
  have h3 := polePaid_le 3 (-4432/2835) (352/189) (-128/63)
    (by linarith : 0<a+3) hab
  have h5 := polePaid_le 5 (4752318/1164625) (-23702004/2646875) (850824/48125)
    (by linarith : 0<a+5) hab
  have h53 := polePaid_le (5/3) (-73544192/186046875) (22433792/79734375) (-557056/6834375)
    (by linarith : 0<a+5/3) hab
  have hq := quadraticPaid_le (-438353120/201331053) (-21945288920/1811979477) ha hab
  unfold cellPaid SigmaPrimitiveCells.cellMass SigmaInnerPaid.primitive
  simp only [div_eq_mul_inv,mul_inv_rev]
  linarith only [h0,h3,h5,h53,hq]
end
end SigmaSignedCells
