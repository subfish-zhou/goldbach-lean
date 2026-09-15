import Wu04FactorLPrimitive

namespace Wu04FactorJPrimitive
open Wu2008DoubleSieve Wu04FactorEnvelopes Real Set MeasureTheory SharpLogRecurrence
noncomputable section

def cubic (z : ℝ) : ℝ := 2*z+2*z^3/3
def c0 (k h v : ℝ) : ℝ := cubic (k+h/v)
def c1 (k h u v : ℝ) : ℝ := cubic (k+h/(u+v))
def h2 (k h u v : ℝ) : ℝ :=
  2*k*h^2*(1/(u+v)-1/v)+(2*h^3/3)*(1/(u+v)^2-1/v^2)
def h3 (h u v : ℝ) : ℝ := (2*h^3/3)*(1/(u+v)-1/v)
def mobiusPrim (k h u v t : ℝ) : ℝ :=
  c0 k h v*log t-c1 k h u v*log (1-t)+
  (c1 k h u v-c0 k h v)*log (u*t+v)-h2 k h u v/(u*t+v)-h3 h u v/(2*(u*t+v)^2)

theorem mobius_deriv {k h u v t : ℝ} (hv : v≠0) (hw : u+v≠0)
    (ht : t≠0) (ht1 : 1-t≠0) (hy : u*t+v≠0) :
    HasDerivAt (mobiusPrim k h u v) (cubic (k+h/(u*t+v))/(t*(1-t))) t := by
  have dy := ((hasDerivAt_id t).const_mul u).add_const v
  have hh := (((((hasDerivAt_log ht).const_mul (c0 k h v)).sub
    ((((hasDerivAt_const t (1:ℝ)).sub (hasDerivAt_id t)).log ht1).const_mul (c1 k h u v))).add
    ((dy.log hy).const_mul (c1 k h u v-c0 k h v))).sub
    ((hasDerivAt_const t (h2 k h u v)).div dy hy)).sub
    ((hasDerivAt_const t (h3 h u v)).div ((dy.pow 2).const_mul 2)
      (by simpa using mul_ne_zero (by norm_num : (2:ℝ)≠0) (pow_ne_zero 2 hy)))
  convert hh using 1 <;> first | rfl | skip
  · dsimp [c0,c1,cubic,h2,h3]
    field_simp [hv,hw,ht,ht1,hy]
    ring

theorem cayley_div {p q : ℝ} (hq : q≠0) (hpq : p+q≠0) :
    (p/q-1)/(p/q+1)=(p-q)/(p+q) := by
  field_simp [hq,hpq]

def primitive (B A t : ℝ) : ℝ :=
  let a := Wu04MainClassical.a B A
  log a*(log t-log (1-t))+
    mobiusPrim 1 (-4*a) A (3*a-1) t+
    mobiusPrim (1/3) (-4*a/3) (3*A) (a-3) t

theorem primitive_deriv {A B t : ℝ} (hB : 2<B) (hBA : B≤A)
    (ha : 1<Wu04MainClassical.a B A) (ha3 : Wu04MainClassical.a B A≠3)
    (ht : t ∈ Icc (1-1/B) (1-1/A)) : HasDerivAt (primitive B A) (jDensity B A t) t := by
  let a := Wu04MainClassical.a B A
  have ha1 : 1<a := ha
  obtain ⟨ht0,ht1,hx⟩ := j_domain hB hBA ha ht
  have hA0 : 0<A := by linarith
  have ha0 : 0<a := by linarith
  have hAt : a+1≤A*t := by
    have hh := (one_le_div ha0).1 hx
    linarith
  have hne : a-3≠0 := sub_ne_zero.mpr ha3
  have hy : A*t+(3*a-1)≠0 := by nlinarith
  have hy' : 3*A*t+(a-3)≠0 := by nlinarith
  have hm := mobius_deriv (k:=1) (h:= -4*a) (u:=A) (v:=3*a-1)
    (by linarith) (by linarith) ht0.ne' (by linarith) hy
  have hn := mobius_deriv (k:=(1:ℝ)/3) (h:= -4*a/3) (u:=3*A) (v:=a-3)
    hne (by nlinarith) ht0.ne' (by linarith) hy'
  have hh := ((((hasDerivAt_log ht0.ne').sub
    (((hasDerivAt_const t (1:ℝ)).sub (hasDerivAt_id t)).log (by linarith : 1-t≠0))).const_mul (log a)).add hm).add hn
  have hz1 : (leftFactor ((A*t-1)/a)-1)/(leftFactor ((A*t-1)/a)+1)=
      1+(-4*a)/(A*t+(3*a-1)) := by
    have he : leftFactor ((A*t-1)/a)=(A*t+a-1)/(2*a) := by
      unfold leftFactor
      field_simp [ha0.ne']
      ring
    rw [he,cayley_div (by positivity : 2*a≠0) (by nlinarith : A*t+a-1+2*a≠0)]
    rw [show A*t+a-1+2*a=A*t+(3*a-1) by ring]
    rw [show A*t+a-1-2*a=(A*t+(3*a-1))+(-4*a) by ring,add_div,div_self hy]
  have hz2 : (rightFactor ((A*t-1)/a)-1)/(rightFactor ((A*t-1)/a)+1)=
      1/3+(-4*a/3)/(3*A*t+(a-3)) := by
    have hx2 : A*t-1+a≠0 := by nlinarith
    have he : rightFactor ((A*t-1)/a)=2*(A*t-1)/(A*t-1+a) := by
      unfold rightFactor
      field_simp [ha0.ne',hx2,show a+(A*t-1)≠0 by linarith]
      ring
    rw [he,cayley_div hx2 (by nlinarith : 2*(A*t-1)+(A*t-1+a)≠0)]
    rw [show 2*(A*t-1)+(A*t-1+a)=3*A*t+(a-3) by ring]
    rw [show 2*(A*t-1)-(A*t-1+a)=(1/3)*(3*A*t+(a-3))+(-4*a/3) by ring,
      add_div,mul_div_cancel_right₀ _ hy']
  convert hh using 1 <;> first | rfl | skip
  · change (log a+lower ((A*t-1)/a))/(t*(1-t))=_
    unfold lower lowerLog
    rw [hz1,hz2]
    dsimp [cubic]
    field_simp [ht0.ne',show 1-t≠0 by linarith]
    ring

def lowerJ (B A : ℝ) : ℝ := primitive B A (1-1/A)-primitive B A (1-1/B)

theorem integral_eq {A B : ℝ} (hB : 2<B) (hBA : B≤A)
    (ha : 1<Wu04MainClassical.a B A) (ha3 : Wu04MainClassical.a B A≠3) :
    jIntegral B A=lowerJ B A := by
  have hab : 1-1/B≤1-1/A := sub_le_sub_left (one_div_le_one_div_of_le (by linarith) hBA) 1
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt (f:=primitive B A)
  · intro t ht
    rw [uIcc_of_le hab] at ht
    exact primitive_deriv hB hBA ha ha3 ht
  · exact j_integrable hB hBA ha

theorem actual_lower {A B : ℝ} (hB : 2<B) (hBA : B≤A)
    (ha : 1<Wu04MainClassical.a B A) (ha3 : Wu04MainClassical.a B A≠3) :
    lowerJ B A≤fourthRowClassicalJ B A := by
  rw [← integral_eq hB hBA ha ha3]
  exact j_lower hB hBA ha

end
end Wu04FactorJPrimitive
