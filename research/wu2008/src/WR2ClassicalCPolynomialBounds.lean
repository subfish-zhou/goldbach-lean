import WR2ClassicalCPolynomial

noncomputable section
namespace WuPaper.ClassicalCPolynomial
open Real Set Wu08OriginalFirstSteps ClassicalPolynomialLower

private theorem small_product_nonneg {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ logPoly x*reciprocal 2 x :=
  mul_nonneg (logPoly_nonneg hx hx1) (reciprocal_nonneg (by norm_num) (by linarith))

private theorem small_product_le {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    logPoly x*reciprocal 2 x ≤ log (1+x)/(2+x) := by
  have h := mul_le_mul (logPoly_le hx) (reciprocal_le (by norm_num : (0:ℝ)<2) hx)
    (reciprocal_nonneg (by norm_num : (0:ℝ)<2) (by linarith)) (log_nonneg (by linarith : (1:ℝ) ≤ 1+x))
  simpa only [mul_one_div] using h

theorem bPoly_nonneg {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) : 0 ≤ bPoly x := by
  have hm := WuSource.SrcFourEnclosure.monotone_of_derivative
    (fun t (_ht : t ∈ Icc 0 x) => bPoly_deriv t)
    (fun t ht => small_product_nonneg ht.1 (ht.2.trans hx1))
  have h := hm ⟨le_rfl,hx⟩ ⟨hx,le_rfl⟩ hx
  simpa only [bPoly_zero] using h

/-- The first recurrence is bounded below by an explicit degree-eight polynomial. -/
theorem bPoly_le_B {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) : bPoly x ≤ B (3+x) := by
  have hd (t : ℝ) (ht : t ∈ Icc 0 x) :
      HasDerivAt (fun t => B (3+t)-bPoly t)
        (ClassicalB.firstValue (3+t)-logPoly t*reciprocal 2 t) t := by
    have h := ((ClassicalB.B_deriv (by linarith [ht.1] : (3:ℝ) ≤ 3+t)).comp t
      ((hasDerivAt_id t).const_add 3)).sub (bPoly_deriv t)
    convert h using 1 <;> first | rfl | simp only [mul_one]
  have hm := WuSource.SrcFourEnclosure.monotone_of_derivative hd (by
    intro t ht
    apply sub_nonneg.mpr
    have h := small_product_le ht.1 (ht.2.trans hx1)
    change logPoly t*reciprocal 2 t ≤ log (3+t-1-1)/(3+t-1)
    rw [show (3:ℝ)+t-1-1 = 1+t by ring,show (3:ℝ)+t-1 = 2+t by ring]
    exact h)
  have h := hm ⟨le_rfl,hx⟩ ⟨hx,le_rfl⟩ hx
  have h0 : B (3+(0:ℝ)) = 0 := by norm_num [B]
  dsimp only at h
  rw [h0,bPoly_zero] at h
  linarith only [h]

theorem cPoly_nonneg {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) : 0 ≤ cPoly x := by
  have hm := WuSource.SrcFourEnclosure.monotone_of_derivative
    (fun t (_ht : t ∈ Icc 0 x) => cPoly_deriv t)
    (fun t ht => mul_nonneg (bPoly_nonneg ht.1 (ht.2.trans hx1))
      (reciprocal_nonneg (by norm_num : (0:ℝ)<3) (by linarith [ht.2])))
  have h := hm ⟨le_rfl,hx⟩ ⟨hx,le_rfl⟩ hx
  simpa only [cPoly_zero] using h

/-- Two recurrence integrals reduce to one fixed degree-twelve polynomial. -/
theorem cPoly_le_C {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) : cPoly x ≤ C (4+x) := by
  have hd (t : ℝ) (ht : t ∈ Icc 0 x) :
      HasDerivAt (fun t => C (4+t)-cPoly t)
        (ClassicalCWeighted.firstValue (4+t)-bPoly t*reciprocal 3 t) t := by
    have h := ((ClassicalCWeighted.C_deriv (by linarith [ht.1] : (4:ℝ) ≤ 4+t)).comp t
      ((hasDerivAt_id t).const_add 4)).sub (cPoly_deriv t)
    convert h using 1 <;> first | rfl | simp only [mul_one]
  have hm := WuSource.SrcFourEnclosure.monotone_of_derivative hd (by
    intro t ht
    apply sub_nonneg.mpr
    have hb := bPoly_le_B ht.1 (ht.2.trans hx1)
    have hB := (ClassicalB.B_bounds (by linarith [ht.1] : (3:ℝ) ≤ 3+t)
      (by linarith [ht.2] : 3+t ≤ 6)).1
    have h := mul_le_mul hb (reciprocal_le (by norm_num : (0:ℝ)<3) ht.1)
      (reciprocal_nonneg (by norm_num : (0:ℝ)<3) (by linarith [ht.2])) hB
    rw [mul_one_div] at h
    change bPoly t*reciprocal 3 t ≤ B (4+t-1)/(4+t-1)
    rw [show (4:ℝ)+t-1 = 3+t by ring]
    exact h)
  have h := hm ⟨le_rfl,hx⟩ ⟨hx,le_rfl⟩ hx
  have h0 : C (4+(0:ℝ)) = 0 := by norm_num [C]
  dsimp only at h
  rw [h0,cPoly_zero] at h
  linarith only [h]

end WuPaper.ClassicalCPolynomial
#print axioms WuPaper.ClassicalCPolynomial.bPoly_le_B
#print axioms WuPaper.ClassicalCPolynomial.cPoly_le_C
