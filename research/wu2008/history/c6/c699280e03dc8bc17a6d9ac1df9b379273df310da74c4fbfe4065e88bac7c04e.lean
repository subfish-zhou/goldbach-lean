import WSrcFourEnclosureBounds

noncomputable section
open Real Set MeasureTheory Wu2008DoubleSieve FourRoughClosedMass

namespace WuSource.SrcFourEnclosure

def D (x : ℝ) : ℝ := cross x*x⁻¹
def D1 (x : ℝ) : ℝ := -(lam-x)⁻¹*x⁻¹-(1+cross x)*(x⁻¹)^2
def D2 (x : ℝ) : ℝ :=
  -((lam-x)⁻¹)^2*x⁻¹+2*(lam-x)⁻¹*(x⁻¹)^2+(3+2*cross x)*(x⁻¹)^3
def F1 (W Q : ℝ → ℝ) (x : ℝ) : ℝ :=
  (W x/x^2)*D x+Q x*D1 x
def F2 (w W Q : ℝ → ℝ) (x : ℝ) : ℝ :=
  (w x/x^2-2*W x/x^3)*D x+2*(W x/x^2)*D1 x+Q x*D2 x

theorem cross_derivative {x : ℝ} (hx : x ≠ 0) (hl : lam-x ≠ 0) :
    HasDerivAt cross (-(lam-x)⁻¹-x⁻¹) x := by
  convert (((hasDerivAt_id x).const_sub lam).log hl).sub (hasDerivAt_log hx)
    using 1 <;> first | rfl | (dsimp; ring)

theorem D_derivative {x : ℝ} (hx : x ≠ 0) (hl : lam-x ≠ 0) :
    HasDerivAt D (D1 x) x := by
  have hd := (cross_derivative hx hl).mul (hasDerivAt_inv hx)
  convert hd using 1 <;> first | rfl | (unfold D1; ring)

theorem D1_derivative {x : ℝ} (hx : x ≠ 0) (hl : lam-x ≠ 0) :
    HasDerivAt D1 (D2 x) x := by
  have h1 := (((hasDerivAt_id x).const_sub lam).inv hl).neg
  have hd := (h1.mul (hasDerivAt_inv hx)).sub
    (((cross_derivative hx hl).const_add 1).mul ((hasDerivAt_inv hx).pow 2))
  convert hd using 1 <;> first | rfl | (dsimp; unfold D2; field_simp; ring)

theorem F_derivative {W Q : ℝ → ℝ} {x : ℝ}
    (hx : x ≠ 0) (hl : lam-x ≠ 0)
    (hQ : HasDerivAt Q (W x/x^2) x) :
    HasDerivAt (fun z => Q z*cross z/z) (F1 W Q x) x := by
  have hd := hQ.mul (D_derivative hx hl)
  convert hd using 1
  · rfl
  · rfl
  · funext z
    unfold D
    dsimp
    ring
  · rfl

theorem F1_derivative {W Q w : ℝ → ℝ} {x : ℝ}
    (hx : x ≠ 0) (hl : lam-x ≠ 0)
    (hW : HasDerivAt W (w x) x) (hQ : HasDerivAt Q (W x/x^2) x) :
    HasDerivAt (F1 W Q) (F2 w W Q x) x := by
  have hq1 := hW.div ((hasDerivAt_id x).pow 2) (pow_ne_zero _ hx)
  have hd := (hq1.mul (D_derivative hx hl)).add (hQ.mul (D1_derivative hx hl))
  convert hd using 1 <;> first | rfl | (dsimp; unfold F2; field_simp; ring)

theorem D_bounds {x : ℝ} (hx : x ∈ Icc alpha beta) :
    |D x| ≤ 21 ∧ |D1 x| ≤ 560 ∧ |D2 x| ≤ 18774 := by
  obtain ⟨hxi,hli,hc⟩ := elementary_bounds hx
  have hpow (n : ℕ) : |x⁻¹|^n ≤ (14 : ℝ)^n := pow_le_pow_left₀ (abs_nonneg _) hxi n
  have hlpow : |(lam-x)⁻¹|^2 ≤ (5 : ℝ)^2 :=
    pow_le_pow_left₀ (abs_nonneg _) hli 2
  have hc1 : |1+cross x| ≤ (5/2 : ℝ) := by
    have h := abs_add_le (1 : ℝ) (cross x)
    norm_num at h
    linarith only [h,hc]
  have hc2 : |3+2*cross x| ≤ (6 : ℝ) := by
    have h := abs_add_le (3 : ℝ) (2*cross x)
    rw [abs_mul] at h
    norm_num at h
    linarith only [h,hc]
  constructor
  · unfold D
    rw [abs_mul]
    calc
      _ ≤ (3/2 : ℝ)*14 := mul_le_mul hc hxi (abs_nonneg _) (by norm_num)
      _ = _ := by norm_num
  constructor
  · unfold D1
    calc
      _ ≤ |-(lam-x)⁻¹*x⁻¹|+|(1+cross x)*(x⁻¹)^2| := abs_sub _ _
      _ = |(lam-x)⁻¹| * |x⁻¹|+|1+cross x| * |x⁻¹|^2 := by
        rw [abs_mul,abs_neg,abs_mul,abs_pow]
      _ ≤ 5*14+(5/2 : ℝ)*14^2 :=
        add_le_add (mul_le_mul hli hxi (abs_nonneg _) (by norm_num))
          (mul_le_mul hc1 (hpow 2) (pow_nonneg (abs_nonneg _) _) (by norm_num))
      _ = _ := by norm_num
  · unfold D2
    calc
      _ ≤ |-((lam-x)⁻¹)^2*x⁻¹+2*(lam-x)⁻¹*(x⁻¹)^2|+
          |(3+2*cross x)*(x⁻¹)^3| := abs_add_le _ _
      _ ≤ |-((lam-x)⁻¹)^2*x⁻¹|+|2*(lam-x)⁻¹*(x⁻¹)^2|+
          |(3+2*cross x)*(x⁻¹)^3| := add_le_add (abs_add_le _ _) le_rfl
      _ = |(lam-x)⁻¹|^2 * |x⁻¹|+2*|(lam-x)⁻¹| * |x⁻¹|^2+
          |3+2*cross x| * |x⁻¹|^3 := by
        norm_num only [abs_mul,abs_neg,abs_pow,abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      _ ≤ 5^2*14+2*5*14^2+(6 : ℝ)*14^3 := by
        gcongr
      _ = _ := by norm_num

theorem F2_bound {w W Q : ℝ → ℝ} {x : ℝ} (hx : x ∈ Icc alpha beta)
    (hw : |w x| ≤ 108) (hW : |W x| ≤ 4) (hQ : |Q x| ≤ 11) :
    |F2 w W Q x| ≤ 2000000 := by
  have hxi := (elementary_bounds hx).1
  obtain ⟨hD0,hD1,hD2⟩ := D_bounds hx
  have hpow (n : ℕ) : |x⁻¹|^n ≤ (14 : ℝ)^n := pow_le_pow_left₀ (abs_nonneg _) hxi n
  have hq1 : |W x/x^2| ≤ 784 := by
    rw [div_eq_mul_inv,← inv_pow,abs_mul,abs_pow]
    calc
      _ ≤ 4*(14 : ℝ)^2 := mul_le_mul hW (hpow 2) (pow_nonneg (abs_nonneg _) _) (by norm_num)
      _ = _ := by norm_num
  have hq2 : |w x/x^2-2*W x/x^3| ≤ 43120 := by
    calc
      _ ≤ |w x/x^2|+|2*W x/x^3| := abs_sub _ _
      _ = |w x| * |x⁻¹|^2+2*|W x| * |x⁻¹|^3 := by
        simp only [div_eq_mul_inv,← inv_pow,abs_mul,abs_pow,
          abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      _ ≤ 108*(14 : ℝ)^2+2*4*14^3 := by gcongr
      _ = _ := by norm_num
  unfold F2
  calc
    _ ≤ |(w x/x^2-2*W x/x^3)*D x+2*(W x/x^2)*D1 x|+
        |Q x*D2 x| := abs_add_le _ _
    _ ≤ |(w x/x^2-2*W x/x^3)*D x|+|2*(W x/x^2)*D1 x|+
        |Q x*D2 x| := add_le_add (abs_add_le _ _) le_rfl
    _ = |w x/x^2-2*W x/x^3| * |D x|+2*|W x/x^2| * |D1 x|+
        |Q x| * |D2 x| := by
          simp only [abs_mul,abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    _ ≤ 43120*21+2*784*560+(11 : ℝ)*18774 := by gcongr
    _ ≤ _ := by norm_num

theorem small_derivatives {x : ℝ} (hx : x ∈ Icc alpha cut) :
    HasDerivAt smallF (F1 smallW smallQ x) x ∧
      HasDerivAt (F1 smallW smallQ)
        (F2 (fun z => (36/5)/(z*(1-z))) smallW smallQ x) x ∧
      |F2 (fun z => (36/5)/(z*(1-z))) smallW smallQ x| ≤ 2000000 := by
  have hxb : x ∈ Icc alpha beta := ⟨hx.1,hx.2.trans geometry.2.2.2.2.2.2⟩
  have hx0 := (geometry.1.trans_le hx.1).ne'
  have hx1 : 1-x ≠ 0 := by
    have hxc : x ≤ (1/10 : ℝ) := hx.2
    linarith only [hxc]
  have hxl : lam-x ≠ 0 := by linarith only [hxb.2,geometry.2.2.2.1]
  refine ⟨F_derivative hx0 hxl (smallQ_derivative hx0 hx1),
    F1_derivative hx0 hxl (smallW_derivative hx0 hx1) (smallQ_derivative hx0 hx1),
    F2_bound hxb (w_bounds.1 x hx) ?_ ?_⟩
  · simpa only [abs_of_nonneg (W_bounds.1 x hx).1] using (W_bounds.1 x hx).2
  · simpa only [abs_of_nonneg (Q_bounds.1 x hx).1] using (Q_bounds.1 x hx).2

theorem large_derivatives {x : ℝ} (hx : x ∈ Icc cut beta) :
    HasDerivAt largeF (F1 largeW largeQ x) x ∧
      HasDerivAt (F1 largeW largeQ)
        (F2 (fun z => 8/z) largeW largeQ x) x ∧
      |F2 (fun z => 8/z) largeW largeQ x| ≤ 2000000 := by
  have hxb : x ∈ Icc alpha beta := ⟨geometry.2.2.2.2.2.1.trans hx.1,hx.2⟩
  have hx0 := (geometry.1.trans_le hxb.1).ne'
  have hxl : lam-x ≠ 0 := by linarith only [hx.2,geometry.2.2.2.1]
  refine ⟨F_derivative hx0 hxl (largeQ_derivative hx0),
    F1_derivative hx0 hxl (largeW_derivative hx0) (largeQ_derivative hx0),
    F2_bound hxb (w_bounds.2 x hx) ?_ ?_⟩
  · simpa only [abs_of_nonneg (W_bounds.2 x hx).1] using (W_bounds.2 x hx).2
  · simpa only [abs_of_nonneg (Q_bounds.2 x hx).1] using (Q_bounds.2 x hx).2

#check @small_derivatives
#check @large_derivatives
#print axioms small_derivatives
#print axioms large_derivatives
end WuSource.SrcFourEnclosure
