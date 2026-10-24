import WR2ClassicalMidpointPanels

noncomputable section
namespace WuPaper.ClassicalPolynomialLower
open Real Set

def logPoly (x : ℝ) : ℝ := x-x^2/2+x^3/3-x^4/4
def logPolyD1 (x : ℝ) : ℝ := 1-x+x^2-x^3
def reciprocal (a x : ℝ) : ℝ := 1/a-x/a^2+x^2/a^3-x^3/a^4

theorem logPoly_deriv (x : ℝ) : HasDerivAt logPoly (logPolyD1 x) x := by
  have h := (((hasDerivAt_id x).sub (((hasDerivAt_id x).pow 2).div_const 2)).add
    (((hasDerivAt_id x).pow 3).div_const 3)).sub (((hasDerivAt_id x).pow 4).div_const 4)
  change HasDerivAt logPoly _ x at h
  apply h.congr_deriv
  dsimp [logPolyD1]
  ring

theorem logPoly_nonneg {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) : 0 ≤ logPoly x := by
  have h1 : 0 ≤ 1-x/2 := by linarith
  have h2 : 0 ≤ 1/3-x/4 := by linarith
  have he : logPoly x = x*((1-x/2)+x^2*(1/3-x/4)) := by unfold logPoly; ring
  rw [he]
  exact mul_nonneg hx (add_nonneg h1 (mul_nonneg (sq_nonneg _) h2))

theorem logPoly_le {x : ℝ} (hx : 0 ≤ x) : logPoly x ≤ log (1+x) := by
  have hd (t : ℝ) (ht : t ∈ Icc 0 x) :
      HasDerivAt (fun t => log (1+t)-logPoly t) (t^4/(1+t)) t := by
    have hp : 0 < 1+t := by linarith [ht.1]
    have h := (((hasDerivAt_id t).const_add 1).log hp.ne').sub (logPoly_deriv t)
    apply h.congr_deriv
    dsimp [logPolyD1]
    field_simp [hp.ne']
    ring
  have hm := WuSource.SrcFourEnclosure.monotone_of_derivative hd
    (fun t ht => div_nonneg (pow_nonneg ht.1 4) (by linarith [ht.1]))
  have h := hm ⟨le_rfl,hx⟩ ⟨hx,le_rfl⟩ hx
  simpa [logPoly] using h

theorem reciprocal_nonneg {a x : ℝ} (ha : 0 < a) (hx : x ≤ a) : 0 ≤ reciprocal a x := by
  have he : reciprocal a x = (a-x)*(a^2+x^2)/a^4 := by
    unfold reciprocal
    field_simp [ha.ne']
    ring
  rw [he]
  exact div_nonneg (mul_nonneg (sub_nonneg.mpr hx) (add_nonneg (sq_nonneg _) (sq_nonneg _)))
    (pow_nonneg ha.le 4)

theorem reciprocal_le {a x : ℝ} (ha : 0 < a) (hx : 0 ≤ x) : reciprocal a x ≤ 1/(a+x) := by
  have hp : 0 < a+x := by linarith
  have he : 1/(a+x)-reciprocal a x = x^4/(a^4*(a+x)) := by
    unfold reciprocal
    field_simp [ha.ne',hp.ne']
    ring
  apply sub_nonneg.mp
  rw [he]
  positivity

end WuPaper.ClassicalPolynomialLower
#print axioms WuPaper.ClassicalPolynomialLower.logPoly_le
#print axioms WuPaper.ClassicalPolynomialLower.reciprocal_le
