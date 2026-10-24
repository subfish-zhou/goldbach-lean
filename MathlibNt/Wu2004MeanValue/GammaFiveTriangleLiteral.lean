import MathlibNt.Wu2004MeanValue.GammaFiveTriangleTransport
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Literal nested Gamma₅ integral

This connects the parameterized affine/Fubini transport to the triangular
nested integral. The legal version retains both insertion inequalities.
The interval [1,3] is justified from the transported support, rather than
inserted as an additional cutoff in the source.
-/

namespace Wu2004MeanValue.GammaFiveLossBudget
open MeasureTheory Set
open scoped Classical Interval

private theorem integral_eq_interval {f : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hs : Function.support f ⊆ Icc a b) :
    (∫ x, f x) = ∫ x in a..b, f x := by
  rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
  apply (setIntegral_eq_integral_of_forall_compl_eq_zero ?_).symm
  intro x hx
  by_contra hn
  exact hx (hs hn)

/-- The source mask reduces to the literal insertion gate on each inner interval. -/
theorem triangle_source_inner {S B : ℝ} (hB : B < 1/2)
    (legal : Bool) (H : ℝ → ℝ) {t : ℝ} (ht : t ∈ Icc (1/S) B) :
    (∫ u : ℝ, triangleSource S B legal H t u) =
      ∫ u in t..B,
        if legal = true → 2*u ≤ 1 ∧ u+2*t ≤ 1 then
          H (S*(1-t-u))/(t*u*(1-t-u)) else 0 := by
  have hs : Function.support (triangleSource S B legal H t) ⊆ Icc t B := by
    intro u hu
    by_contra hn
    exact hu (if_neg (fun h => hn ⟨h.2.1,h.2.2.1⟩))
  rw [integral_eq_interval ht.2 hs]
  apply intervalIntegral.integral_congr
  rw [uIcc_of_le ht.2]
  intro u hu
  have hh : 2*u ≤ 1 := by linarith [hu.2]
  simp only [triangleSource, triangleRegion, ht.1, hu.1, hu.2, hh, true_and]

/-- Exact literal triangular integral as an integral on the product space. -/
theorem triangle_literal_product {S B : ℝ} (hS : 0 < S) (hB : B < 1/2)
    (hAB : 1/S ≤ B) (legal : Bool) {H : ℝ → ℝ}
    (hm : Measurable H) (hb : ∀ v, |H v| ≤ 1) :
    (∫ t in (1/S)..B, ∫ u in t..B,
      if legal = true → 2*u ≤ 1 ∧ u+2*t ≤ 1 then
        H (S*(1-t-u))/(t*u*(1-t-u)) else 0) =
      ∫ p : ℝ × ℝ, triangleSource S B legal H p.1 p.2 := by
  have hs : Function.support (fun t => ∫ u, triangleSource S B legal H t u) ⊆
      Icc (1/S) B := by
    intro t ht
    by_contra hn
    apply ht
    have he (u : ℝ) : triangleSource S B legal H t u = 0 := by
      apply if_neg
      exact fun h => hn ⟨h.1,h.2.1.trans h.2.2.1⟩
    simp only [he, integral_zero]
  rw [show (∫ p : ℝ × ℝ, triangleSource S B legal H p.1 p.2) =
    ∫ t, ∫ u, triangleSource S B legal H t u from
      integral_prod _ (triangle_source_integrable hS hB legal hm hb),
    integral_eq_interval hAB hs]
  symm
  apply intervalIntegral.integral_congr
  rw [uIcc_of_le hAB]
  exact fun t ht => triangle_source_inner hB legal H ht

/-- The literal full or legal triangle, after affine substitution and Fubini.
The row hypotheses ensure the entire transported support lies in [1,3]. -/
theorem triangle_literal_transport {S B : ℝ} (hS : 0 < S) (hB : B < 1/2)
    (hAB : 1/S ≤ B) (hleft : 1 ≤ S*(1-2*B)) (hright : S ≤ 5)
    (legal : Bool) {H : ℝ → ℝ} (hm : Measurable H) (hb : ∀ v, |H v| ≤ 1) :
    (∫ t in (1/S)..B, ∫ u in t..B,
      if legal = true → 2*u ≤ 1 ∧ u+2*t ≤ 1 then
        H (S*(1-t-u))/(t*u*(1-t-u)) else 0) =
      ∫ v in (1 : ℝ)..3, ∫ t : ℝ, triangleMasked S B legal H v t := by
  rw [triangle_literal_product hS hB hAB legal hm hb,
    triangle_product_transport hS hB legal hm hb]
  apply integral_eq_interval (by norm_num)
  intro v hv
  by_contra hn
  apply hv
  have he (t : ℝ) : triangleMasked S B legal H v t = 0 := by
    by_contra he
    have hs := (triangle_masked_support hS B legal H (a := (v,t)) he).1
    exact hn ⟨hleft.trans hs.1,by linarith [hs.2]⟩
  simp only [he, integral_zero]

end Wu2004MeanValue.GammaFiveLossBudget
