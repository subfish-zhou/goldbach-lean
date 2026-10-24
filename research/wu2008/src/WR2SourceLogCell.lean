import WR2SourceLogChord

noncomputable section
namespace WuPaper.SourceLogChord
open Real Set MeasureTheory
open scoped Interval

def cell (a b A B : ℝ) : ℝ :=
  (b-a)*(A+B)/(a+b)-(B-A)*(b-a)^2/(3*(a+b)^2)

def polynomial (a b A B t : ℝ) : ℝ :=
  (((b-t)*A+(t-a)*B)/(b-a))*(4*(a+b-t)/(a+b)^2)

def primitive (a b A B t : ℝ) : ℝ :=
  4/((b-a)*(a+b)^2)*((b*A-a*B)*(a+b)*t+
    ((B-A)*(a+b)-(b*A-a*B))*t^2/2-(B-A)*t^3/3)

theorem primitive_derivative (a b A B t : ℝ) :
    HasDerivAt (primitive a b A B) (polynomial a b A B t) t := by
  have h := (((((hasDerivAt_id t).const_mul ((b*A-a*B)*(a+b))).add
    ((((hasDerivAt_id t).pow 2).const_mul ((B-A)*(a+b)-(b*A-a*B))).div_const 2)).sub
    ((((hasDerivAt_id t).pow 3).const_mul (B-A)).div_const 3)).const_mul
      (4/((b-a)*(a+b)^2)))
  change HasDerivAt (primitive a b A B) _ t at h
  apply h.congr_deriv
  dsimp [polynomial]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem polynomial_integral {a b A B : ℝ} (ha : 0 < a) (hab : a < b) :
    (∫ t in a..b, polynomial a b A B t) = cell a b A B := by
  have hi : IntervalIntegrable (polynomial a b A B) volume a b :=
    (by unfold polynomial; fun_prop : Continuous (polynomial a b A B)).intervalIntegrable a b
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => primitive_derivative a b A B t) hi]
  unfold primitive cell
  have hw : b-a ≠ 0 := (sub_pos.mpr hab).ne'
  have hs : a+b ≠ 0 := by linarith
  field_simp
  ring

/-- A rational endpoint certificate pays the entire original tail integral. -/
theorem cell_le_integral {a b c A B : ℝ} (ha : 0 < a) (hab : a < b)
    (hc : 0 < c) (hA0 : 0 ≤ A) (hB0 : 0 ≤ B)
    (hA : A ≤ log ((a+1)/c)) (hB : B ≤ log ((b+1)/c)) :
    cell a b A B ≤ ∫ t in a..b, log ((t+1)/c)/t := by
  rw [← polynomial_integral ha hab]
  apply intervalIntegral.integral_mono_on hab.le
  · exact (by unfold polynomial; fun_prop : Continuous (polynomial a b A B)).intervalIntegrable a b
  · apply ContinuousOn.intervalIntegrable_of_Icc (h := hab.le)
    intro t ht
    have ht0 : 0 < t := ha.trans_le ht.1
    fun_prop (disch := positivity)
  · intro t ht
    exact kernel_lower ha hab hc ht hA0 hB0 hA hB

end WuPaper.SourceLogChord
#print axioms WuPaper.SourceLogChord.cell_le_integral
