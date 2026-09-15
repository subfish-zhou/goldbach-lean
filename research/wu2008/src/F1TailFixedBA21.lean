import F1TailPolynomialFTC

noncomputable section
open Real Set MeasureTheory Polynomial
namespace F1TailFixedBA21

/-- Numerator forced by the original reduced denominator's monic normalization. -/
def P : ℝ[X] := C (31808596743643040271/24010000000000000000)+C (-517764967567375648761/37515625000000000000)*X+C (10166412124229459039429/171500000000000000000)*X^2+C (-1409024895902675366407109/10804500000000000000000)*X^3+C (12905839312824050916302921/97240500000000000000000)*X^4+C (270027366284158634072269/10206000000000000000000)*X^5+C (-624204536118133321441584421/2571912000000000000000000)*X^6+C (323271948309528050303594993509/1134213192000000000000000000)*X^7+C (-9442109817783674183465021998991/81663349824000000000000000000)*X^8+C (-407198031266567859496705294301/5833096416000000000000000000)*X^9+C (10309334707162243028485536957737/81663349824000000000000000000)*X^10+C (-4424717964199205324449017631/51039593640000000000000000)*X^11+C (2672768332279726145978153/72913705200000000000000)*X^12+C (-1910621178523399717939/182284263000000000000)*X^13+C (3529277224023767413/1701319788000000000)*X^14+C (-8970536318655337/31899746025000000)*X^15+C (126540866737/5063451750000)*X^16+C (-1048116829/797493650625)*X^17+C (990377/31899746025)*X^18
/-- Every original pole and its multiplicity is retained. -/
def D : ℝ[X] := (X-C 0)^1*(X-C 1)^2*(X-C (2/3))^4*(X-C (-1327/200))^4*(X-C (-1727/600))^4*(C (4/21)+C (-8/7)*X+C 1*X^2)^1*(C (881047/120000)+C (683/100)*X+C 1*X^2)^1

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
    TailFiniteFTC.BA21.kernel u=P.eval u/D.eval u := by
  have hu0 : 0 < u := by linarith
  have hu1 : 0 < u-1 := by linarith
  have ht : 0 < u-2/3 := by linarith
  have hq : 0 < 21*u^2-24*u+4 := by nlinarith [sq_nonneg (u-2)]
  have hqm : 0 < (4:ℝ)/21+(-(8/7))*u+1*u^2 := by
    nlinarith [sq_nonneg (u-2)]
  simp only [P, D, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub,
    Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X]
  unfold TailFiniteFTC.BA21.kernel F1BFullFTC.quadOne
  simp only [neg_div, sub_neg_eq_add, sub_zero]
  apply (div_eq_div_iff (by positivity) (by positivity)).2
  ring

theorem numerator_nonneg {u : ℝ} (hu : u ∈ Icc 2 (927/200)) : 0 ≤ P.eval u := by
  have hk := F1TailPolynomialSigns.BA21_nonneg hu
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

theorem payment_le_mass : payment ≤ TailFiniteFTC.BA21.mass := by
  rw [← TailFiniteFTC.BA21.integral_exact]
  exact F1TailPolynomialFTC.fixed_payment P D TailFiniteFTC.BA21.kernel
    (TailFiniteFTC.BA21.kernel_continuousOn.intervalIntegrable_of_Icc (by norm_num))
    (fun u hu => numerator_nonneg hu) (fun u hu => denominator_pos hu.1)
    (fun u hu => kernel_exact hu.1)

end F1TailFixedBA21
