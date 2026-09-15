import Wu04MainClassical

namespace Wu04MainCollection
open Wu2008DoubleSieve Real Set MeasureTheory SharpLogRecurrence JointLogTotalComparison
open Wu04MainClassical
noncomputable section

def yl (B A : ℝ) : ℝ := A*(1-1/B)+b B A
def yu (B A : ℝ) : ℝ := A*(1-1/A)+b B A
def ratio (B A : ℝ) : ℝ := (1-1/A)*yl B A/((1-1/B)*yu B A)
def rest (B A : ℝ) : ℝ := -h2 B A*(1/yu B A-1/yl B A)-
  h3 B A/2*(1/(yu B A)^2-1/(yl B A)^2)
def collectedJ (B A : ℝ) : ℝ := c B A*log (ratio B A)+
  Wu04MainClassical.e B A*(log (yu B A/yl B A)+log (A/B))+
  log (a B A)*log ((A-1)/(B-1))+rest B A

theorem collect_j {B A : ℝ} (hB : 2 < B) (hBA : B ≤ A) (ha : 1 < a B A) :
    lowerJ B A = collectedJ B A := by
  have hB0 : 0<B := by linarith
  have hA0 : 0<A := hB0.trans_le hBA
  have htB : 0<1-1/B := by
    apply sub_pos.mpr
    simpa only [one_div_one] using one_div_lt_one_div_of_lt (by norm_num : (0:ℝ)<1) (by linarith : (1:ℝ)<B)
  have htA : 0<1-1/A := by
    apply sub_pos.mpr
    simpa only [one_div_one] using one_div_lt_one_div_of_lt (by norm_num : (0:ℝ)<1) (by linarith : (1:ℝ)<A)
  have hyL : 0<yl B A := by unfold yl b; nlinarith
  have hyU : 0<yu B A := by unfold yu b; nlinarith
  have hAB : log (A/B) = log (1-(1-1/B))-log (1-(1-1/A)) := by
    rw [show 1-(1-1/B)=1/B by ring,show 1-(1-1/A)=1/A by ring,
      log_div hA0.ne' hB0.ne']
    simp only [one_div,log_inv]
    ring
  have hAm : 0<A-1 := by linarith
  have hBm : 0<B-1 := by linarith
  have heA : A*(1-1/A)=A-1 := by field_simp
  have heB : B*(1-1/B)=B-1 := by field_simp
  have hAlog := log_mul hA0.ne' htA.ne'
  have hBlog := log_mul hB0.ne' htB.ne'
  rw [heA] at hAlog
  rw [heB] at hBlog
  have hM : log ((A-1)/(B-1)) = log (1-1/A)-log (1-1/B)+log (A/B) := by
    rw [log_div hAm.ne' hBm.ne',log_div hA0.ne' hB0.ne',hAlog,hBlog]
    ring
  unfold collectedJ ratio
  rw [log_div (mul_pos htA hyL).ne' (mul_pos htB hyU).ne',
    log_mul htA.ne' hyL.ne',log_mul htB.ne' hyU.ne',log_div hyU.ne' hyL.ne',hM,hAB]
  unfold lowerJ prim rest yl yu
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

def pay (xs : List ℝ) : ℝ := (xs.map lowerLog).sum

theorem lower_product (xs : List ℝ) (hx : ∀ x ∈ xs, (1:ℝ) ≤ x) :
    0 ≤ pay xs ∧ pay xs ≤ log xs.prod := by
  induction xs with
  | nil => simp [pay]
  | cons x xs ih =>
    have hxx := hx x (by simp)
    have hxs : ∀ t ∈ xs, (1:ℝ)≤t := fun t ht => hx t (by simp [ht])
    obtain ⟨hp,hp'⟩ := ih hxs
    have hprod : 0<xs.prod := List.prod_pos (fun t ht => lt_of_lt_of_le (by norm_num) (hxs t ht))
    have hx0 : 0<x := by linarith
    have hl : 0≤lowerLog x := by unfold lowerLog; positivity
    have hu := log_lower hxx
    simp only [pay,List.map_cons,List.sum_cons,List.prod_cons]
    rw [log_mul hx0.ne' hprod.ne']
    change 0≤lowerLog x+pay xs ∧ lowerLog x+pay xs ≤ log x+log xs.prod
    constructor <;> linarith only [hp,hp',hl,hu]

def upperPay (xs : List ℝ) : ℝ := (xs.map V).sum

theorem upper_product (xs : List ℝ) (hx : ∀ x ∈ xs, (1:ℝ) ≤ x) : log xs.prod ≤ upperPay xs := by
  induction xs with
  | nil => simp [upperPay]
  | cons x xs ih =>
    have hxx := hx x (by simp)
    have hxs : ∀ t ∈ xs, (1:ℝ)≤t := fun t ht => hx t (by simp [ht])
    have hprod : 0<xs.prod := List.prod_pos (fun t ht => lt_of_lt_of_le (by norm_num) (hxs t ht))
    have hx0 : 0<x := by linarith
    simp only [upperPay,List.map_cons,List.sum_cons,List.prod_cons]
    rw [log_mul hx0.ne' hprod.ne']
    exact add_le_add (log_le_V hxx) (ih hxs)

def paidJ (B A p q : ℝ) : ℝ := c B A*V (ratio B A)+
  Wu04MainClassical.e B A*(lowerLog (yu B A/yl B A)+p)+lowerLog (a B A)*q+rest B A

theorem paid_j {B A p q : ℝ} (hB : 2 < B) (hBA : B ≤ A) (ha : 1 < a B A)
    (hc : c B A ≤ 0) (he : 0 ≤ Wu04MainClassical.e B A) (hr : 1 ≤ ratio B A)
    (hy : 1 ≤ yu B A/yl B A) (hp : p ≤ log (A/B))
    (hq : q ≤ log ((A-1)/(B-1))) (hq0 : 0 ≤ q) : paidJ B A p q ≤ lowerJ B A := by
  rw [collect_j hB hBA ha]
  have hr' := mul_le_mul_of_nonpos_left (log_le_V hr) hc
  have he' := mul_le_mul_of_nonneg_left (add_le_add (log_lower hy) hp) he
  have hla := log_lower (by linarith : 1≤a B A)
  have hla0 := log_nonneg (by linarith : 1≤a B A)
  have hq' := mul_le_mul hla hq hq0 hla0
  unfold paidJ collectedJ
  linarith only [hr',he',hq']

def lRest (A : ℝ) : ℝ := (3/5)*((A-3)/6+8/(3*(A-1))-4/3)+
  (2/5)*(8/(A-1)-4/(A-1)^2+16/(9*(A-1)^3)-29/9)

theorem collect_l {A : ℝ} (hA : 3 ≤ A) : upperL A =
    lRest A-(1/10)*log (A-2)+(28/15)*log ((A-1)/2) := by
  rw [log_div (by linarith : A-1≠0) (by norm_num : (2:ℝ)≠0)]
  unfold upperL vPrim upperPrimitive lowerLPrim lRest
  norm_num only [show (2:ℝ)-1=1 by norm_num,log_one]
  rw [show A-1-1=A-2 by ring]
  ring

#print axioms paid_j
#print axioms collect_l
end
end Wu04MainCollection
