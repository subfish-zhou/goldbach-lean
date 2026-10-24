import WR2ClassicalUniformMidpoint
import WR2ClassicalFifthSource

noncomputable section
namespace WuPaper.ClassicalFifthQuadrature
open Real Set MeasureTheory Finset
open ClassicalFifthSource ClassicalFifthKernel ClassicalUniformMidpoint

theorem uniform_lower {A A1 A2 L L1 L2 : ℝ → ℝ} {a b : ℝ} {n : ℕ}
    (hn : 0 < n) (ha : lo ≤ a) (hb : b ≤ hi) (hab : a ≤ b)
    (hA : ∀ s ∈ Icc a b, HasDerivAt A (A1 s) s)
    (hA1 : ∀ s ∈ Icc a b, HasDerivAt A1 (A2 s) s)
    (hL : ∀ s ∈ Icc a b, HasDerivAt L (L1 s) s)
    (hL1 : ∀ s ∈ Icc a b, HasDerivAt L1 (L2 s) s)
    (hAb : ∀ s ∈ Icc a b, |A s| ≤ 3 ∧ |A1 s| ≤ 2 ∧ |A2 s| ≤ 2)
    (hLb : ∀ s ∈ Icc a b, |L s| ≤ 1 ∧ |L1 s| ≤ 1 ∧ |L2 s| ≤ 1)
    (q : ℕ → ℝ)
    (hq : ∀ i < n, q i ≤ kernel A L ((point a b n i+point a b n (i+1))/2)) :
    step a b n*(∑ i ∈ range n, q i)-(n:ℝ)*60*(step a b n)^3/24 ≤
      ∫ s in a..b, kernel A L s := by
  have hs3 (s : ℝ) (hs : s ∈ Icc a b) : 3 ≤ s := geometry.1.trans (ha.trans hs.1)
  have hshi (s : ℝ) (hs : s ∈ Icc a b) : s ≤ ClassicalFourth.R-1 := (hs.2.trans hb).trans geometry.2.2.2.2.2
  exact ClassicalUniformMidpoint.uniform_lower hn hab
    (fun s hs => kernel_deriv (by linarith [hs3 s hs]) (by linarith [hshi s hs]) (hA s hs) (hL s hs))
    (fun s hs => first_deriv (by linarith [hs3 s hs]) (by linarith [hshi s hs]) (hA s hs) (hA1 s hs) (hL s hs) (hL1 s hs))
    (fun s hs => second_abs_le (hs3 s hs) (hshi s hs)
      (hAb s hs).1 (hAb s hs).2.1 (hAb s hs).2.2 (hLb s hs).1 (hLb s hs).2.1 (hLb s hs).2.2)
    q hq

end WuPaper.ClassicalFifthQuadrature
#print axioms WuPaper.ClassicalFifthQuadrature.uniform_lower
