import OriginalSigmaCubicRestoration

namespace OriginalSigmaCubicRestoration
open Real Set MeasureTheory NodeExtension OriginalSigmaStrength Wu04WholeCollection
open Wu2008DoubleSieve SharpLogRecurrence JointLogTotalComparison
open scoped Interval
noncomputable section

def cubicWeight (t : ℝ) : ℝ := cubicPaid t/t

def cubicOuterPrimitive (t : ℝ) : ℝ :=
  polePrimitive 0 (-1469/759375) (7369/1265625) (-278/84375) t-(4/5625)/(3*t^3)+
  polePrimitive 3 (-112/1215) (64/27) 0 t+
  polePrimitive 5 (2592/3125) (-9072/3125) (2592/625) t+
  polePrimitive (5/3) (-416512/759375) (518144/11390625) (-507904/6834375) t

theorem cubicWeight_laurent {t : ℝ} (ht : 0<t) :
    cubicWeight t =
      poleDensity 0 (-1469/759375) (7369/1265625) (-278/84375) t+(4/5625)/t^4+
      poleDensity 3 (-112/1215) (64/27) 0 t+
      poleDensity 5 (2592/3125) (-9072/3125) (2592/625) t+
      poleDensity (5/3) (-416512/759375) (518144/11390625) (-507904/6834375) t := by
  have h3 : t+3≠0 := by positivity
  have h5 : t+5≠0 := by positivity
  have h1 : t+1≠0 := by positivity
  have h2 : 2*t+2≠0 := by positivity
  have h35 : 3*t+5≠0 := by positivity
  have h53 : t+5/3≠0 := by positivity
  unfold cubicWeight cubicPaid cb ca cc cd V lowerLog upperLog poleDensity
  field_simp
  ring

theorem fourthPole_deriv {t : ℝ} (ht : 0<t) :
    HasDerivAt (fun t : ℝ => -(4/5625)/(3*t^3)) ((4/5625)/t^4) t := by
  have h := (((((hasDerivAt_id t).pow 3).inv (pow_ne_zero 3 ht.ne')).const_mul (-(4/5625))).div_const 3)
  convert h using 1 <;> first | rfl | skip
  · funext x
    simp only [Pi.inv_apply,Pi.pow_apply,id,div_eq_mul_inv,mul_inv_rev]
    ring
  · dsimp only [id,Pi.pow_apply]
    field_simp
    ring

theorem cubicOuterPrimitive_deriv {t : ℝ} (ht : 0<t) :
    HasDerivAt cubicOuterPrimitive (cubicWeight t) t := by
  rw [cubicWeight_laurent ht]
  convert (((((polePrimitive_deriv 0 _ _ _ (by linarith)).add (fourthPole_deriv ht)).add
    (polePrimitive_deriv 3 _ _ _ (by linarith))).add
    (polePrimitive_deriv 5 _ _ _ (by linarith))).add
    (polePrimitive_deriv (5/3) _ _ _ (by linarith))) using 1 <;> first | rfl | skip
  funext x
  unfold cubicOuterPrimitive
  simp only [Pi.add_apply]
  ring

theorem cubicWeight_continuous {a b : ℝ} (ha : 0<a) (hab : a≤b) :
    ContinuousOn cubicWeight (uIcc a b) := by
  rw [uIcc_of_le hab]
  intro t ht
  have ht0 : 0<t := ha.trans_le ht.1
  have he : cubicWeight =ᶠ[nhds t] fun x =>
      poleDensity 0 (-1469/759375) (7369/1265625) (-278/84375) x+(4/5625)/x^4+
      poleDensity 3 (-112/1215) (64/27) 0 x+
      poleDensity 5 (2592/3125) (-9072/3125) (2592/625) x+
      poleDensity (5/3) (-416512/759375) (518144/11390625) (-507904/6834375) x := by
    filter_upwards [eventually_gt_nhds ht0] with x hx
    exact cubicWeight_laurent hx
  apply ContinuousAt.continuousWithinAt
  apply ContinuousAt.congr_of_eventuallyEq _ he
  unfold poleDensity
  fun_prop (disch := positivity)

theorem cubicWeight_integral {a b : ℝ} (ha : 0<a) (hab : a≤b) :
    (∫ t in a..b, cubicWeight t)=cubicOuterPrimitive b-cubicOuterPrimitive a := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro t ht
    rw [uIcc_of_le hab] at ht
    exact cubicOuterPrimitive_deriv (ha.trans_le ht.1)
  · exact (cubicWeight_continuous ha hab).intervalIntegrable

def cubicCellPaid (a b : ℝ) : ℝ :=
  poleCellPaid 0 (-1469/759375) (7369/1265625) (-278/84375) a b-
    (4/5625)/3*(1/b^3-1/a^3)+
  poleCellPaid 3 (-112/1215) (64/27) 0 a b+
  poleCellPaid 5 (2592/3125) (-9072/3125) (2592/625) a b+
  poleCellPaid (5/3) (-416512/759375) (518144/11390625) (-507904/6834375) a b

theorem cubicCellPaid_le {a b : ℝ} (ha : 0<a) (hb : 0<b) :
    cubicCellPaid a b ≤ cubicOuterPrimitive b-cubicOuterPrimitive a := by
  have h0 := poleCellPaid_le 0 (-1469/759375) (7369/1265625) (-278/84375)
    (by linarith : 0<a+0) (by linarith : 0<b+0)
  have h3 := poleCellPaid_le 3 (-112/1215) (64/27) 0 (by linarith : 0<a+3) (by linarith : 0<b+3)
  have h5 := poleCellPaid_le 5 (2592/3125) (-9072/3125) (2592/625)
    (by linarith : 0<a+5) (by linarith : 0<b+5)
  have h53 := poleCellPaid_le (5/3) (-416512/759375) (518144/11390625) (-507904/6834375)
    (by linarith : 0<a+5/3) (by linarith : 0<b+5/3)
  unfold cubicCellPaid cubicOuterPrimitive
  simp only [div_eq_mul_inv,mul_inv_rev]
  linarith only [h0,h3,h5,h53]

end
end OriginalSigmaCubicRestoration
