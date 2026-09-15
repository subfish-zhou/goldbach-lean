import MathlibNt.Wu2008DoubleSieve.Omega3LayerGeometry

/-!
# Common-layer regrouping before taking any absolute values

A modulus enters only the test and the coprimality restriction. The labels,
their ranks, selected d,p2, coefficients and both profiles are the same for
every modulus. The only triangle inequality is over the fixed layer count.
No analytic distribution estimate is asserted here.
-/

namespace Wu2008DoubleSieve

open Finset
open scoped Classical

theorem omega3Layer_coprime_weighted_sum {i : ℕ} (W : Fin i → Finset ℕ)
    (L : Finset Omega3CofactorIndex) (B : ℕ)
    (hB : ∀ e, (omega3LayerFibre L e).card ≤ B) (q : ℕ)
    (F : Omega3CofactorIndex → ℝ) :
    (∑ c ∈ L.filter (fun c => (omega3CofactorValue c).Coprime q),
      (convolutionCoeff W c.1 : ℝ) * F c) =
      ∑ j ∈ range B, ∑ e ∈ (omega3LayerSupport L j).filter (fun e => e.Coprime q),
        omega3LayerCoefficient W L j e * F (omega3LayerLabel L j e) := by
  have h := omega3Layer_weighted_sum W L B hB
    (fun c => if (omega3CofactorValue c).Coprime q then F c else 0)
  simp only [mul_ite, mul_zero] at h
  rw [sum_filter, h]
  apply sum_congr rfl
  intro j _
  rw [sum_filter]
  apply sum_congr rfl
  intro e he
  rw [(omega3LayerLabel_mem he).2]

/-- The whole signed cofactor sum is grouped exactly first; the number of
subsequent triangle terms is B, not the number of labels or of cofactors. -/
theorem omega3Layer_coprime_abs_sum_le {i : ℕ} (W : Fin i → Finset ℕ)
    (L : Finset Omega3CofactorIndex) (B : ℕ)
    (hB : ∀ e, (omega3LayerFibre L e).card ≤ B) (q : ℕ)
    (F : Omega3CofactorIndex → ℝ) :
    |∑ c ∈ L.filter (fun c => (omega3CofactorValue c).Coprime q),
      (convolutionCoeff W c.1 : ℝ) * F c| ≤
      ∑ j ∈ range B,
        |∑ e ∈ (omega3LayerSupport L j).filter (fun e => e.Coprime q),
          omega3LayerCoefficient W L j e * F (omega3LayerLabel L j e)| := by
  rw [omega3Layer_coprime_weighted_sum W L B hB q F]
  exact abs_sum_le_sum_abs _ _

theorem omega3Layer_modulus_sum_le {i : ℕ} (W : Fin i → Finset ℕ)
    (L : Finset Omega3CofactorIndex) (B : ℕ)
    (hB : ∀ e, (omega3LayerFibre L e).card ≤ B)
    (Q : Finset ℕ) (w : ℕ → ℝ) (hw : ∀ q ∈ Q, 0 ≤ w q)
    (F : ℕ → Omega3CofactorIndex → ℝ) :
    (∑ q ∈ Q, w q *
      |∑ c ∈ L.filter (fun c => (omega3CofactorValue c).Coprime q),
        (convolutionCoeff W c.1 : ℝ) * F q c|) ≤
      ∑ j ∈ range B, ∑ q ∈ Q, w q *
        |∑ e ∈ (omega3LayerSupport L j).filter (fun e => e.Coprime q),
          omega3LayerCoefficient W L j e * F q (omega3LayerLabel L j e)| := by
  rw [sum_comm]
  apply sum_le_sum
  intro q hq
  rw [← mul_sum]
  exact mul_le_mul_of_nonneg_left (omega3Layer_coprime_abs_sum_le W L B hB q (F q))
    (hw q hq)

end Wu2008DoubleSieve
