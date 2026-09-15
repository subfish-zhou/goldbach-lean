import MathlibNt.Wu2008DoubleSieve.SecondFunctionalUnitFiniteKernelUniform
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalContinuousSlab

open scoped BigOperators Classical
namespace SecondFunctionalUnitKernel
open Set MeasureTheory Wu2008DoubleSieve SecondFunctionalUnitFiniteKernel

noncomputable def U {m : ℕ} (phi b : ℝ) (t : Fin (m+1) → ℝ) : ℝ :=
  F (phi - ∑ i, t i) (t (Fin.last m)) b

theorem U_literal {m : ℕ} (phi b : ℝ) (t : Fin (m+1) → ℝ) :
    U phi b t = if t (Fin.last m) < phi - ∑ i, t i ∧ phi - ∑ i, t i < b
      then 1 / (phi - ∑ i, t i) else 0 := rfl

theorem U_prime_coordinates {m : ℕ} {R : ℝ}
    (f : Fin (m+1) → primeSlabPrimes R) (phi b : ℝ) :
    U phi b (SecondFunctionalUnitPrimeFibre.coordinate f) =
      F (phi - ∑ i, Real.log (f i).val / Real.log R)
        (Real.log (f (Fin.last m)).val / Real.log R) b := rfl

noncomputable def dot {n : ℕ} (c t : Fin n → ℝ) : ℝ := ∑ i, c i * t i

def row (s : Bool) (a gamma : ℝ) : Prop := if s then a < gamma else a ≤ gamma

def mask {n r : ℕ} (C : Fin r → Fin n → ℝ) (gamma : Fin r → ℝ)
    (strict : Fin r → Bool) (t : Fin n → ℝ) : Prop :=
  ∀ q, row (strict q) (dot (C q) t) (gamma q)

noncomputable def G {m r : ℕ} (phi b : ℝ) (C : Fin r → Fin (m+1) → ℝ)
    (gamma : Fin r → ℝ) (strict : Fin r → Bool) (t : Fin (m+1) → ℝ) : ℝ :=
  if mask C gamma strict t then U phi b t else 0

theorem U_measurable {m : ℕ} (phi b : ℝ) : Measurable (U (m := m) phi b) := by
  unfold U F
  have hs : MeasurableSet {t : Fin (m+1) → ℝ |
      t (Fin.last m) < phi - ∑ i, t i ∧ phi - ∑ i, t i < b} :=
    by
      have h1 : MeasurableSet {t : Fin (m+1) → ℝ | t (Fin.last m) < phi - ∑ i, t i} :=
        measurableSet_lt (by fun_prop) (by fun_prop)
      have h2 : MeasurableSet {t : Fin (m+1) → ℝ | phi - ∑ i, t i < b} :=
        measurableSet_lt (by fun_prop) measurable_const
      exact h1.inter h2
  exact Measurable.ite hs (by fun_prop) measurable_const

theorem mask_measurable {n r : ℕ} (C : Fin r → Fin n → ℝ)
    (gamma : Fin r → ℝ) (strict : Fin r → Bool) :
    MeasurableSet {t | mask C gamma strict t} := by
  simp only [mask, ofPred_forall]
  apply MeasurableSet.iInter
  intro q
  unfold row
  cases strict q <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · exact measurableSet_le (by unfold dot; fun_prop) measurable_const
  · exact measurableSet_lt (by unfold dot; fun_prop) measurable_const

theorem G_measurable {m r : ℕ} (phi b : ℝ) (C : Fin r → Fin (m+1) → ℝ)
    (gamma : Fin r → ℝ) (strict : Fin r → Bool) : Measurable (G phi b C gamma strict) :=
  (U_measurable phi b).ite (mask_measurable C gamma strict) measurable_const

theorem U_range {m : ℕ} (phi b : ℝ) {t : Fin (m+1) → ℝ}
    (ht : t ∈ continuousCube (m+1)) : 0 ≤ U phi b t ∧ U phi b t ≤ 10 :=
  F_range (ht (Fin.last m) (mem_univ _)).1

theorem G_range {m r : ℕ} (phi b : ℝ) (C : Fin r → Fin (m+1) → ℝ)
    (gamma : Fin r → ℝ) (strict : Fin r → Bool) {t : Fin (m+1) → ℝ}
    (ht : t ∈ continuousCube (m+1)) :
    0 ≤ G phi b C gamma strict t ∧ G phi b C gamma strict t ≤ 10 := by
  unfold G
  split_ifs
  · exact U_range phi b ht
  · norm_num

theorem U_weighted_integrable {m : ℕ} (phi b : ℝ) :
    IntegrableOn (fun t => U phi b t * continuousDensity t) (continuousCube (m+1)) := by
  apply continuousDensity_mul_integrable (U_measurable phi b) (K := 10)
  intro t ht
  rw [Real.norm_eq_abs, abs_of_nonneg (U_range phi b ht).1]
  exact (U_range phi b ht).2

theorem G_weighted_integrable {m r : ℕ} (phi b : ℝ)
    (C : Fin r → Fin (m+1) → ℝ) (gamma : Fin r → ℝ) (strict : Fin r → Bool) :
    IntegrableOn (fun t => G phi b C gamma strict t * continuousDensity t)
      (continuousCube (m+1)) := by
  apply continuousDensity_mul_integrable (G_measurable phi b C gamma strict) (K := 10)
  intro t ht
  rw [Real.norm_eq_abs, abs_of_nonneg (G_range phi b C gamma strict ht).1]
  exact (G_range phi b C gamma strict ht).2

theorem G_empty {m : ℕ} (phi b : ℝ) (C : Fin 0 → Fin (m+1) → ℝ)
    (gamma : Fin 0 → ℝ) (strict : Fin 0 → Bool) (t : Fin (m+1) → ℝ) :
    G phi b C gamma strict t = U phi b t := by
  simp [G, mask]

end SecondFunctionalUnitKernel
