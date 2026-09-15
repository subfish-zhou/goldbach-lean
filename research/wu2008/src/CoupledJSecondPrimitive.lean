import CoupledJErrorKernel

namespace CoupledJLogRecovery
open Real Set MeasureTheory Wu2008DoubleSieve SharpLogRecurrence
open scoped Interval
noncomputable section

def ra (C D : ℝ) : ℝ := -(D-C)^5/(D*(D+C)^3)
def rb (C D : ℝ) : ℝ := C^2/D
def rc (C D : ℝ) : ℝ := 5*(D-C)-D-3*(D+C)+ra C D-rb C D
def rd (C D : ℝ) : ℝ := 48*C^3/(D+C)-32*C^4/(D+C)^2
def re (C D : ℝ) : ℝ := -32*C^4/(D+C)

theorem second_fraction (C D u : ℝ) (hD : D≠0) (hB : D+C≠0)
    (hu : u≠0) (hDu : D-u≠0) (hBu : D+C-u≠0) :
    (u-(D-C))^5/(u*(D-u)*(D+C-u)^3) =
      1+ra C D/u+rb C D/(D-u)+rc C D/(D+C-u)+
        rd C D/(D+C-u)^2+re C D/(D+C-u)^3 := by
  dsimp [rc,ra,rb,rd,re]
  field_simp [hD,hB,hu,hDu,hBu]
  ring

def secondPrimitive (S A u : ℝ) : ℝ :=
  let C := S-A
  let D := S-1
  (3/(34*C))*(u+ra C D*log u-rb C D*log (D-u)-rc C D*log (D+C-u)+
    rd C D/(D+C-u)+re C D/(2*(D+C-u)^2))

theorem secondError_laurent {S A u : ℝ} (hA : 2≤A) (hAS : A≤S-1)
    (hu : u∈Icc (A-1) (S-2)) :
    secondError S A u = (3/(34*(S-A)))*
      (1+ra (S-A) (S-1)/u+rb (S-A) (S-1)/(S-1-u)+
        rc (S-A) (S-1)/(S-1+(S-A)-u)+
        rd (S-A) (S-1)/(S-1+(S-A)-u)^2+
        re (S-A) (S-1)/(S-1+(S-A)-u)^3) := by
  have hC : S-A≠0 := by linarith
  have hD : S-1≠0 := by linarith
  have hB : S-1+(S-A)≠0 := by linarith
  have hDu : S-1-u≠0 := by linarith [hu.2]
  have hBu : S-1+(S-A)-u≠0 := by linarith [hu.2]
  have hu0 : u≠0 := by linarith [hu.1]
  have hx : 0<(S-A)/(S-1-u) := div_pos (by linarith) (by linarith [hu.2])
  rw [← second_fraction (S-A) (S-1) u hD hB hu0 hDu hBu]
  unfold secondError
  rw [OriginalFirstErrorRecovery.envelope_gap hx]
  have he : (S-A)/(S-1-u)+1=(S-1+(S-A)-u)/(S-1-u) := by
    field_simp
    ring
  rw [he]
  field_simp [hC,hDu,hBu,hu0]
  ring

theorem secondError_continuous {S A a b : ℝ} (hA : 2≤A) (hAS : A≤S-1)
    (ha : A-1≤a) (hab : a≤b) (hb : b≤S-2) :
    ContinuousOn (secondError S A) (uIcc a b) := by
  rw [uIcc_of_le hab]
  intro u hu
  have hu0 : u≠0 := by linarith [hu.1]
  have hd : S-1-u≠0 := by linarith [hu.2]
  have hx : (S-A)/(S-1-u)≠0 := div_ne_zero (by linarith) hd
  have hx1 : (S-A)/(S-1-u)+1≠0 := by
    have : 0<(S-A)/(S-1-u) := div_pos (by linarith) (by linarith [hu.2])
    positivity
  have hprod : 6*((S-A)/(S-1-u))*((S-A)/(S-1-u)+1)≠0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) hx) hx1
  apply ContinuousAt.continuousWithinAt
  unfold secondError upperLog lowerLog
  fun_prop (disch := assumption)

theorem secondPrimitive_deriv {S A u : ℝ} (hA : 2≤A) (hAS : A≤S-1)
    (hu : u∈Icc (A-1) (S-2)) :
    HasDerivAt (secondPrimitive S A) (secondError S A u) u := by
  have hu0 : u≠0 := by linarith [hu.1]
  have hd : S-1-u≠0 := by linarith [hu.2]
  have hb : S-1+(S-A)-u≠0 := by linarith [hu.2]
  have dy := (hasDerivAt_id u).const_sub (S-1)
  have dz := (hasDerivAt_id u).const_sub (S-1+(S-A))
  have h := ((((((hasDerivAt_id u).add
    ((hasDerivAt_log hu0).const_mul (ra (S-A) (S-1)))).sub
    ((dy.log hd).const_mul (rb (S-A) (S-1)))).sub
    ((dz.log hb).const_mul (rc (S-A) (S-1)))).add
    ((hasDerivAt_const u (rd (S-A) (S-1))).div dz hb)).add
    ((hasDerivAt_const u (re (S-A) (S-1))).div ((dz.pow 2).const_mul 2)
      (mul_ne_zero (by norm_num) (pow_ne_zero 2 hb)))).const_mul (3/(34*(S-A)))
  convert h using 1 <;> first | rfl | skip
  rw [secondError_laurent hA hAS hu]
  dsimp
  congr 1
  field_simp [hu0,hd,hb]
  ring

theorem second_integral {S A a b : ℝ} (hA : 2≤A) (hAS : A≤S-1)
    (ha : A-1≤a) (hab : a≤b) (hb : b≤S-2) :
    (∫ u in a..b,secondError S A u)=secondPrimitive S A b-secondPrimitive S A a := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro u hu
    rw [uIcc_of_le hab] at hu
    exact secondPrimitive_deriv hA hAS ⟨ha.trans hu.1,hu.2.trans hb⟩
  · exact (secondError_continuous hA hAS ha hab hb).intervalIntegrable

end
end CoupledJLogRecovery
