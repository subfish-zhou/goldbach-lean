import F1TailPolynomialFTC

noncomputable section
open Real Set MeasureTheory Polynomial
namespace F1TailFixedBA11

/-- Numerator forced by the original reduced denominator's monic normalization. -/
def P : ℝ[X] := C (-249338355119524476963/3062500000000000000)+C (625901135235311173563/2679687500000000000)*X+C (-102942521559023668171821/42875000000000000000)*X^2+C (-296920049662587264255639/42875000000000000000)*X^3+C (-132691473239114300945883/42875000000000000000)*X^4+C (7251657498950427235379/1500000000000000000)*X^5+C (9130543459789759149891871/2646000000000000000000)*X^6+C (-45684485156029949044975993/23814000000000000000000)*X^7+C (-14518853422125178846026470593/12002256000000000000000000)*X^8+C (3927428120076154958415513907/6001128000000000000000000)*X^9+C (53007421150348368914216863/480090240000000000000000)*X^10+C (-6285145554241416405509/60011280000000000000)*X^11+C (3275777690761603231/428652000000000000)*X^12+C (318214740586063/51030000000000)*X^13+C (-10726027790903/7144200000000)*X^14+C (1709092939/62511750000)*X^15+C (11309077/375070500)*X^16+C (-25124/6251175)*X^17+C (124/750141)*X^18
/-- Every original pole and its multiplicity is retained. -/
def D : ℝ[X] := (X-C 0)^3*(X-C (-2))^4*(X-C (-1327/200))^4*(X-C (-1727/600))^4*(C 4+C 16*X+C 1*X^2)^1*(C (881047/120000)+C (683/100)*X+C 1*X^2)^1

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
    TailFiniteFTC.BA11.kernel u=P.eval u/D.eval u := by
  have hu0 : 0 < u := by linarith
  have hu1 : 0 < u-1 := by linarith
  have ht : 0 < u-2/3 := by linarith
  have hq : 0 < 21*u^2-24*u+4 := by nlinarith [sq_nonneg (u-2)]
  have hqm : 0 < (4:ℝ)/21+(-8/7)*u+u^2 := by
    nlinarith [sq_nonneg (u-2)]
  simp only [P, D, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub,
    Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X]
  unfold TailFiniteFTC.BA11.kernel F1BFullFTC.quadOne
  simp only [neg_div, sub_neg_eq_add, sub_zero]
  apply (div_eq_div_iff (by positivity) (by positivity)).2
  ring

theorem numerator_nonneg {u : ℝ} (hu : u ∈ Icc 2 (927/200)) : 0 ≤ P.eval u := by
  have hk := F1TailPolynomialSigns.BA11_nonneg hu
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

theorem payment_le_mass : payment ≤ TailFiniteFTC.BA11.mass := by
  rw [← TailFiniteFTC.BA11.integral_exact]
  exact F1TailPolynomialFTC.fixed_payment P D TailFiniteFTC.BA11.kernel
    (TailFiniteFTC.BA11.kernel_continuousOn.intervalIntegrable_of_Icc (by norm_num))
    (fun u hu => numerator_nonneg hu) (fun u hu => denominator_pos hu.1)
    (fun u hu => kernel_exact hu.1)

end F1TailFixedBA11
