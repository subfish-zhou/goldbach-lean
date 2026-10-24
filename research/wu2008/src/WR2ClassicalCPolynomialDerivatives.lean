import WR2ClassicalCPolynomialBounds
import WR2ClassicalSixthKernel

noncomputable section
namespace WuPaper.ClassicalCPolynomial
open Real Set ClassicalPolynomialLower

def reciprocalD1 (a x : ℝ) : ℝ := -1/a^2+2*x/a^3-3*x^2/a^4
def bFirst (x : ℝ) : ℝ := logPoly x*reciprocal 2 x
def cFirst (x : ℝ) : ℝ := bPoly x*reciprocal 3 x
def cSecond (x : ℝ) : ℝ := bFirst x*reciprocal 3 x+bPoly x*reciprocalD1 3 x

theorem reciprocal_deriv (a x : ℝ) : HasDerivAt (reciprocal a) (reciprocalD1 a x) x := by
  have h := (((hasDerivAt_const x (1/a)).sub ((hasDerivAt_id x).div_const (a^2))).add
    (((hasDerivAt_id x).pow 2).div_const (a^3))).sub (((hasDerivAt_id x).pow 3).div_const (a^4))
  change HasDerivAt (reciprocal a) _ x at h
  apply h.congr_deriv
  dsimp [reciprocalD1]
  ring

private theorem reciprocal_upper {a x : ℝ} (ha : 0 < a) (hx : 0 ≤ x) : reciprocal a x ≤ 1/a := by
  exact (reciprocal_le ha hx).trans
    (div_le_div_of_nonneg_left (by norm_num) ha (by linarith))

theorem bFirst_bounds {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) : 0 ≤ bFirst x ∧ bFirst x ≤ 1 := by
  have hp0 := logPoly_nonneg hx hx1
  have hp : logPoly x ≤ 1 := by
    have h := log_le_sub_one_of_pos (by linarith : (0:ℝ)<1+x)
    linarith [logPoly_le hx]
  have hq0 := reciprocal_nonneg (by norm_num : (0:ℝ)<2) (show x ≤ 2 by linarith)
  have hq := reciprocal_upper (by norm_num : (0:ℝ)<2) hx
  refine ⟨mul_nonneg hp0 hq0,?_⟩
  have h := mul_le_mul hp hq hq0 (by norm_num : (0:ℝ) ≤ 1)
  change logPoly x*reciprocal 2 x ≤ 1
  linarith only [h]

private theorem primitive_le_one {f d : ℝ → ℝ} {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1)
    (h0 : f 0 = 0) (hd : ∀ t ∈ Icc 0 x, HasDerivAt f (d t) t)
    (hbound : ∀ t ∈ Icc 0 x, d t ≤ 1) : f x ≤ 1 := by
  have hf (t : ℝ) (ht : t ∈ Icc 0 x) : HasDerivAt (fun t => t-f t) (1-d t) t := by
    exact (hasDerivAt_id t).sub (hd t ht)
  have hm := WuSource.SrcFourEnclosure.monotone_of_derivative hf
    (fun t ht => sub_nonneg.mpr (hbound t ht))
  have h := hm ⟨le_rfl,hx⟩ ⟨hx,le_rfl⟩ hx
  dsimp only at h
  rw [h0] at h
  linarith only [h,hx1]

theorem bPoly_upper {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) : bPoly x ≤ 1 :=
  primitive_le_one hx hx1 bPoly_zero (fun t _ => bPoly_deriv t)
    (fun _t ht => (bFirst_bounds ht.1 (ht.2.trans hx1)).2)

theorem cFirst_bounds {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) : 0 ≤ cFirst x ∧ cFirst x ≤ 1 := by
  have hb0 := bPoly_nonneg hx hx1
  have hb := bPoly_upper hx hx1
  have hq0 := reciprocal_nonneg (by norm_num : (0:ℝ)<3) (show x ≤ 3 by linarith)
  have hq := reciprocal_upper (by norm_num : (0:ℝ)<3) hx
  refine ⟨mul_nonneg hb0 hq0,?_⟩
  have h := mul_le_mul hb hq hq0 (by norm_num : (0:ℝ) ≤ 1)
  change bPoly x*reciprocal 3 x ≤ 1
  linarith only [h]

theorem cPoly_upper {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) : cPoly x ≤ 1 :=
  primitive_le_one hx hx1 cPoly_zero (fun t _ => cPoly_deriv t)
    (fun _t ht => (cFirst_bounds ht.1 (ht.2.trans hx1)).2)

theorem cFirst_deriv (x : ℝ) : HasDerivAt cFirst (cSecond x) x :=
  (bPoly_deriv x).mul (reciprocal_deriv 3 x)

theorem cSecond_bound {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) : |cSecond x| ≤ 1 := by
  have hb : |bPoly x| ≤ 1 := by rw [abs_of_nonneg (bPoly_nonneg hx hx1)]; exact bPoly_upper hx hx1
  have hf : |bFirst x| ≤ 1 := by rw [abs_of_nonneg (bFirst_bounds hx hx1).1]; exact (bFirst_bounds hx hx1).2
  have hq : |reciprocal 3 x| ≤ (1:ℝ)/3 := by
    rw [abs_of_nonneg (reciprocal_nonneg (by norm_num : (0:ℝ)<3) (by linarith))]
    exact reciprocal_upper (by norm_num) hx
  have hq1 : |reciprocalD1 3 x| ≤ (1:ℝ)/3 := by
    norm_num [reciprocalD1]
    apply abs_le.mpr
    constructor <;> nlinarith [sq_nonneg x,show x^2 ≤ 1 by nlinarith]
  exact (ClassicalSixthKernel.first_bound hf hq hb hq1).trans (by norm_num)

end WuPaper.ClassicalCPolynomial
#print axioms WuPaper.ClassicalCPolynomial.cPoly_upper
#print axioms WuPaper.ClassicalCPolynomial.cFirst_deriv
#print axioms WuPaper.ClassicalCPolynomial.cSecond_bound
