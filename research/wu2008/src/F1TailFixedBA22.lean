import F1TailPolynomialFTC

noncomputable section
open Real Set MeasureTheory Polynomial
namespace F1TailFixedBA22

/-- Numerator forced by the original reduced denominator's monic normalization. -/
def P : ℝ[X] := C (13611081350610342648513337437/8853393489405808000000000000)+C (-2061428715931288372670181416661/110667418617572600000000000000)*X+C (6305874648626961087150760691697/63238524924327200000000000000)*X^2+C (-138010621481348282813424673298961/442669674470290400000000000000)*X^3+C (28055706205099745759661980669247/44266967447029040000000000000)*X^4+C (-2732240074605924667430873224867/3097397139150720000000000000)*X^5+C (3362355592696098457712178970307171/3902720395329907200000000000000)*X^6+C (-1023057362574119952867920949120256541/1721099694340489075200000000000000)*X^7+C (35493748746548067833874776766968304073/123919177992515213414400000000000000)*X^8+C (-4088168419968041990195556390596771/44256849283041147648000000000000)*X^9+C (53758661479050068007445746671381/3097979449812880335360000000000)*X^10+C (-1191251020749924410762944631/1936237156133050209600000000)*X^11+C (-3213192601359695719478153/5532106160380143456000000)*X^12+C (2084537336547571904039/13830265400950358640000)*X^13+C (-4352383744325129333/322706192688841701600)*X^14+C (-11067833722111/14940101513372301)*X^15+C (49286072693675/172878317511879483)*X^16+C (-3418124930000/134460913620350709)*X^17+C (990377000000/1210148222583156381)*X^18
/-- Every original pole and its multiplicity is retained. -/
def D : ℝ[X] := (X-C 0)^1*(X-C 1)^2*(X-C (2/3))^4*(X-C (-3581/200))^4*(C (4/21)+C (-8/7)*X+C 1*X^2)^1*(C (30769909/40000)+C (10343/100)*X+C 1*X^2)^1

theorem denominator_pos {u : ℝ} (hu : 2 ≤ u) : 0 < D.eval u := by
  have hu0 : 0 < u := by linarith
  have hu1 : 0 < u-1 := by linarith
  have ht : 0 < u-2/3 := by linarith
  have hq : 0 < (4:ℝ)/21+(-(8/7))*u+1*u^2 := by
    nlinarith [sq_nonneg (u-2)]
  simp only [D, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub,
    Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X]
  simp only [neg_div, sub_neg_eq_add, sub_zero]
  positivity

theorem kernel_exact {u : ℝ} (hu : 2 ≤ u) :
    TailFiniteFTC.BA22.kernel u=P.eval u/D.eval u := by
  have hu0 : 0 < u := by linarith
  have hu1 : 0 < u-1 := by linarith
  have ht : 0 < u-2/3 := by linarith
  have hq : 0 < 21*u^2-24*u+4 := by nlinarith [sq_nonneg (u-2)]
  have hqm : 0 < (4:ℝ)/21+(-(8/7))*u+1*u^2 := by
    nlinarith [sq_nonneg (u-2)]
  simp only [P, D, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub,
    Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X]
  unfold TailFiniteFTC.BA22.kernel F1BFullFTC.quadTwo
  simp only [neg_div, sub_neg_eq_add, sub_zero]
  apply (div_eq_div_iff (by positivity) (by positivity)).2
  ring

theorem numerator_nonneg {u : ℝ} (hu : u ∈ Icc 2 (927/200)) : 0 ≤ P.eval u := by
  have hk := F1TailPolynomialSigns.BA22_nonneg hu
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

theorem payment_le_mass : payment ≤ TailFiniteFTC.BA22.mass := by
  rw [← TailFiniteFTC.BA22.integral_exact]
  exact F1TailPolynomialFTC.fixed_payment P D TailFiniteFTC.BA22.kernel
    (TailFiniteFTC.BA22.kernel_continuousOn.intervalIntegrable_of_Icc (by norm_num))
    (fun u hu => numerator_nonneg hu) (fun u hu => denominator_pos hu.1)
    (fun u hu => kernel_exact hu.1)

end F1TailFixedBA22
