import Wu04FactorConsumer

namespace Wu04WholeCollection
open Wu2008DoubleSieve Real SharpLogRecurrence JointLogTotalComparison
open Wu04FactorEnvelopes Wu04FactorJPrimitive
noncomputable section

def low (x : ℝ) : ℝ := if 1≤x then lower x else -upper (1/x)
def up (x : ℝ) : ℝ := if 1≤x then upper x else -lower (1/x)

theorem bounds {x : ℝ} (hx : 0<x) : low x≤log x ∧ log x≤up x := by
  by_cases h : 1≤x
  · simpa [low,up,h] using And.intro (lower_le_log h) (log_le_upper h)
  · have hi : 1≤1/x := (le_div_iff₀ hx).2 (by linarith)
    have hl := lower_le_log hi
    have hu := log_le_upper hi
    simp only [one_div,log_inv] at hl hu
    simp only [low,up,if_neg h,one_div]
    constructor <;> linarith only [hl,hu]

def pay (xs : List ℝ) : ℝ := (xs.map lower).sum
def upperPay (xs : List ℝ) : ℝ := (xs.map upper).sum

theorem product_bounds (xs : List ℝ) (hx : ∀ x∈xs, (1:ℝ)≤x) :
    0≤pay xs ∧ pay xs≤log xs.prod ∧ log xs.prod≤upperPay xs := by
  induction xs with
  | nil => simp [pay,upperPay]
  | cons x xs ih =>
    have hxx := hx x (by simp)
    have hxs : ∀ t∈xs, (1:ℝ)≤t := fun t ht => hx t (by simp [ht])
    obtain ⟨hp,hl,hu⟩ := ih hxs
    have hprod : 0<xs.prod := List.prod_pos (fun t ht => lt_of_lt_of_le (by norm_num) (hxs t ht))
    have hx0 : 0<x := by linarith
    have hll : 0≤lower x := by
      unfold lower lowerLog
      have h1 := (factors hxx).1
      have h2 := (factors hxx).2.1
      positivity
    have hlow := lower_le_log hxx
    have hup := log_le_upper hxx
    simp only [pay,upperPay,List.map_cons,List.sum_cons,List.prod_cons]
    rw [log_mul hx0.ne' hprod.ne']
    change 0≤lower x+pay xs ∧ lower x+pay xs≤log x+log xs.prod ∧
      log x+log xs.prod≤upper x+upperPay xs
    exact ⟨add_nonneg hll hp,add_le_add hlow hl,add_le_add hup hu⟩

def signedLow (c x : ℝ) : ℝ := if 0≤c then c*low x else c*up x

theorem signed_bound (c : ℝ) {x : ℝ} (hx : 0<x) : signedLow c x≤c*log x := by
  by_cases hc : 0≤c
  · simpa [signedLow,hc] using mul_le_mul_of_nonneg_left (bounds hx).1 hc
  · simpa [signedLow,hc] using mul_le_mul_of_nonpos_left (bounds hx).2 (le_of_not_ge hc)

def yl (B u v : ℝ) : ℝ := u*(1-1/B)+v
def yu (A u v : ℝ) : ℝ := u*(1-1/A)+v
def ratio (B A u v : ℝ) : ℝ := (1-1/A)*yl B u v/((1-1/B)*yu A u v)
def rest (B A k h u v : ℝ) : ℝ :=
  -h2 k h u v*(1/yu A u v-1/yl B u v)-
    h3 h u v/2*(1/(yu A u v)^2-1/(yl B u v)^2)
def collected (B A k h u v : ℝ) : ℝ :=
  c0 k h v*log (ratio B A u v)+c1 k h u v*(log (yu A u v/yl B u v)+log (A/B))+
    rest B A k h u v

theorem logs {B A : ℝ} (hB : 1<B) (hA : 1<A) :
    log (A/B)=log (1-(1-1/B))-log (1-(1-1/A)) ∧
    log ((A-1)/(B-1))=log (1-1/A)-log (1-1/B)+log (A/B) := by
  have hB0 : 0<B := by linarith
  have hA0 : 0<A := by linarith
  have htB : 0<1-1/B := sub_pos.mpr (by
    simpa only [one_div_one] using one_div_lt_one_div_of_lt (by norm_num : (0:ℝ)<1) hB)
  have htA : 0<1-1/A := sub_pos.mpr (by
    simpa only [one_div_one] using one_div_lt_one_div_of_lt (by norm_num : (0:ℝ)<1) hA)
  constructor
  · rw [show 1-(1-1/B)=1/B by ring,show 1-(1-1/A)=1/A by ring,
      log_div hA0.ne' hB0.ne']
    simp only [one_div,log_inv]
    ring
  · have heA : A*(1-1/A)=A-1 := by field_simp
    have heB : B*(1-1/B)=B-1 := by field_simp
    have hAl := log_mul hA0.ne' htA.ne'
    have hBl := log_mul hB0.ne' htB.ne'
    rw [heA] at hAl
    rw [heB] at hBl
    rw [log_div (by linarith : A-1≠0) (by linarith : B-1≠0),
      log_div hA0.ne' hB0.ne',hAl,hBl]
    ring

theorem collect {B A k h u v : ℝ} (hB : 1<B) (hA : 1<A)
    (hl : 0<yl B u v) (hu : 0<yu A u v) :
    mobiusPrim k h u v (1-1/A)-mobiusPrim k h u v (1-1/B)=collected B A k h u v := by
  have htB : 0<1-1/B := sub_pos.mpr (by
    simpa only [one_div_one] using one_div_lt_one_div_of_lt (by norm_num : (0:ℝ)<1) hB)
  have htA : 0<1-1/A := sub_pos.mpr (by
    simpa only [one_div_one] using one_div_lt_one_div_of_lt (by norm_num : (0:ℝ)<1) hA)
  unfold collected ratio
  rw [log_div (mul_pos htA hl).ne' (mul_pos htB hu).ne',
    log_mul htA.ne' hl.ne',log_mul htB.ne' hu.ne',log_div hu.ne' hl.ne',(logs hB hA).1]
  unfold mobiusPrim rest yl yu
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

def paid (B A k h u v p : ℝ) : ℝ :=
  signedLow (c0 k h v) (ratio B A u v)+
    signedLow (c1 k h u v) (yu A u v/yl B u v)+c1 k h u v*p+rest B A k h u v

theorem paid_bound {B A k h u v p : ℝ} (hr : 0<ratio B A u v)
    (hy : 0<yu A u v/yl B u v) (he : 0≤c1 k h u v) (hp : p≤log (A/B)) :
    paid B A k h u v p≤collected B A k h u v := by
  have h1 := signed_bound (c0 k h v) hr
  have h2 := signed_bound (c1 k h u v) hy
  have h3 := mul_le_mul_of_nonneg_left hp he
  unfold paid collected
  linarith only [h1,h2,h3]

end
end Wu04WholeCollection
