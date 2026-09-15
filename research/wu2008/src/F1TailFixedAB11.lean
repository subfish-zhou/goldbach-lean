import F1TailPolynomialFTC

noncomputable section
open Real Set MeasureTheory Polynomial
namespace F1TailFixedAB11

/-- Numerator forced by the original reduced denominator's monic normalization. -/
def P : ℝ[X] := C (36020403044979695187527821/69457500000000000000)+C (-168911804590077320435708501/156279375000000000000)*X+C (16464564430971311257139741/41674500000000000000)*X^2+C (166674037133775995342793889/267907500000000000000)*X^3+C (-357071369486233961518799671/714420000000000000000)*X^4+C (-81806631076655738540317727/1071630000000000000000)*X^5+C (712676315527108717079288543/4286520000000000000000)*X^6+C (-19046055973629192296306999/1200225600000000000000)*X^7+C (-12499748470719186757834301729/480090240000000000000000)*X^8+C (18926408459065473795151327/3750705000000000000000)*X^9+C (23857573539370765302571/10716300000000000000)*X^10+C (-6859355296772558831/13395375000000000)*X^11+C (-12209498883530569/107163000000000)*X^12+C (1571303220371/66976875000)*X^13+C (164737204301/46883812500)*X^14+C (-185246072/468838125)*X^15+C (-990436/18753525)*X^16
/-- Every original pole and its multiplicity is retained. -/
def D : ℝ[X] := (X-C 0)^5*(X-C (-2))^4*(X-C (-1327/200))^2*(X-C (-1727/600))^4*(C 4+C 16*X+C 1*X^2)^1*(C (881047/120000)+C (683/100)*X+C 1*X^2)^1

theorem denominator_pos {u : ℝ} (hu : 2 ≤ u) : 0 < D.eval u := by
  have hu0 : 0 < u := by linarith
  have hu1 : 0 < u-1 := by linarith
  have ht : 0 < u-2/3 := by linarith
  have hq : 0 < (4:ℝ)/21+(-8/7)*u+u^2 := by
    nlinarith [sq_nonneg (u-2)]
  simp only [D, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub,
    Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X]
  simp only [neg_div, sub_neg_eq_add, sub_zero]
  positivity

theorem kernel_exact {u : ℝ} (hu : 2 ≤ u) :
    TailFiniteFTC.AB11.kernel u=P.eval u/D.eval u := by
  have hu0 : 0 < u := by linarith
  have hu1 : 0 < u-1 := by linarith
  have ht : 0 < u-2/3 := by linarith
  have hq : 0 < 21*u^2-24*u+4 := by nlinarith [sq_nonneg (u-2)]
  have hqm : 0 < (4:ℝ)/21+(-8/7)*u+u^2 := by
    nlinarith [sq_nonneg (u-2)]
  simp only [P, D, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub,
    Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X]
  unfold TailFiniteFTC.AB11.kernel F1BFullFTC.quadOne
  simp only [neg_div, sub_neg_eq_add, sub_zero]
  field_simp (disch := positivity)
  ring

theorem numerator_nonneg {u : ℝ} (hu : u ∈ Icc 2 (927/200)) : 0 ≤ P.eval u := by
  have hk := F1TailPolynomialSigns.AB11_nonneg hu
  rw [kernel_exact hu.1] at hk
  simpa only [zero_mul] using (le_div_iff₀ (denominator_pos hu.1)).mp hk

def W : ℝ := F1TailPolynomialFTC.moment P
def J : ℝ := F1TailPolynomialFTC.moment (P*D)
def a : ℝ := W/J
def payment : ℝ := W^2/J

theorem W_exact : (∫ u in (2:ℝ)..(927/200), P.eval u)=W :=
  F1TailPolynomialFTC.moment_exact P

theorem J_exact : (∫ u in (2:ℝ)..(927/200), P.eval u*D.eval u)=J := by
  simpa only [Polynomial.eval_mul, J] using F1TailPolynomialFTC.moment_exact (P*D)

theorem payment_le_mass : payment ≤ TailFiniteFTC.AB11.mass := by
  rw [← TailFiniteFTC.AB11.integral_exact]
  exact F1TailPolynomialFTC.fixed_payment P D TailFiniteFTC.AB11.kernel
    (TailFiniteFTC.AB11.kernel_continuousOn.intervalIntegrable_of_Icc (by norm_num))
    (fun u hu => numerator_nonneg hu) (fun u hu => denominator_pos hu.1)
    (fun u hu => kernel_exact hu.1)

end F1TailFixedAB11
