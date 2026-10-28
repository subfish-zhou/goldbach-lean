import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Tactic

/-! # AnalyticNumberTheory.LargeSieve.Additive

## Additive large sieve (Montgomery 1971)

For a `δ`-well-spaced set of points `{x_r}` modulo 1 and any finitely supported
complex sequence `a_n`,

  Σ_r |Σ_{M<n≤M+N} a_n e(n x_r)|² ≤ (N + 1/δ) · Σ_{M<n≤M+N} |a_n|²,

where `e(x) = exp(2πix)`. This is a basic analytic input to the
Bombieri--Vinogradov theorem and the weighted Pan mean-value theorem
(`PanMeanValueUniform`); the multiplicative and arithmetic large sieves are
consequences of it.

This module has three parts:

1. **Representation**: the standard additive character
   `unitChar x = exp(2πix)` on `AddCircle 1` (mathlib's `AddCircle.toCircle`),
   the interval exponential sum `circleCharSum`, and `wellSpaced`
   (`δ`-separation in the distance modulo 1).
2. **Target statements**: `MontgomeryLargeSievePrimal` and
   `MontgomeryLargeSieveDual` are quantified propositions. This module defines
   these targets rather than proving either large-sieve bound.
3. **Duality lemma**: for any finite matrix `A` and constant `C ≥ 0`, the
   primal bound (for every `a`) is equivalent to the dual bound (for every `b`)
   (`largeSieveDuality`). This is the algebraic foundation of the large-sieve
   argument: Montgomery's original proof starts with the dual form
   (geometric-sum bounds and the Schur test), and duality preserves the constant.
   The dual form uses the conjugate transpose (`star (A i j)`); the classical
   `e(nx)` formulation follows equivalently by conjugating `b` and reversing
   the sign of `n`.

References:
  - Montgomery, H.L. (1971), "Topics in Multiplicative Number Theory"
  - Iwaniec & Kowalski, "Analytic Number Theory" (2004), Ch. 7
  - Halberstam & Richert, "Sieve Methods" (1974), Ch. 9-10
-/

namespace AnalyticNumberTheory.LargeSieve

open scoped BigOperators

noncomputable section

/-! ## 1. Additive characters and exponential sums on the circle modulo 1 -/


/-! ## 2. Additive large-sieve target statements -/


/-! ## 3. Duality lemma (the algebraic foundation of the large sieve) -/


/-- **Complex Cauchy--Schwarz** (Finset):
`|Σᵢ xᵢ·conj(yᵢ)| ≤ √(Σ‖xᵢ‖²)·√(Σ‖yᵢ‖²)`, proved using the triangle
inequality and real Cauchy--Schwarz. -/
theorem complexCauchySchwarz {ι : Type*} (s : Finset ι) (x y : ι → ℂ) :
    ‖∑ i ∈ s, x i * star (y i)‖ ≤
      Real.sqrt (∑ i ∈ s, ‖x i‖ ^ 2) * Real.sqrt (∑ i ∈ s, ‖y i‖ ^ 2) := by
  calc
    ‖∑ i ∈ s, x i * star (y i)‖ ≤ ∑ i ∈ s, ‖x i * star (y i)‖ :=
      norm_sum_le s _
    _ = ∑ i ∈ s, ‖x i‖ * ‖y i‖ := by simp only [norm_mul, norm_star]
    _ ≤ Real.sqrt (∑ i ∈ s, ‖x i‖ ^ 2) * Real.sqrt (∑ i ∈ s, ‖y i‖ ^ 2) :=
      Real.sum_mul_le_sqrt_mul_sqrt s (fun i => ‖x i‖) (fun i => ‖y i‖)

/-- **Large-sieve duality lemma** (finite matrices): for any `A : ι → κ → ℂ`
and `C ≥ 0`, the primal bound
`Σᵢ |Σⱼ Aᵢⱼ aⱼ|² ≤ C·Σⱼ |aⱼ|² (∀a)` is equivalent to the
conjugate-transpose dual bound
`Σⱼ |Σᵢ conj(Aᵢⱼ) bᵢ|² ≤ C·Σᵢ |bᵢ|² (∀b)`.

Proof (Montgomery's classical argument): put `v = A*b` (`bStar`). Then
`‖A*b‖² = |⟨b, A A*b⟩| ≤ ‖A A*b‖·‖b‖ ≤ √C·‖A*b‖·‖b‖`.
The primal bound applied to `v` and complex Cauchy--Schwarz give
`‖A*b‖ ≤ √C·‖b‖`. The converse follows symmetrically from `A** = A`
(`star (star A) = A`). -/
theorem largeSieveDuality_primalToDual {ι κ : Type*}
    (s : Finset ι) (t : Finset κ) (A : ι → κ → ℂ) {C : ℝ} (hC : 0 ≤ C)
    (hPrimal : ∀ a : κ → ℂ,
      ∑ i ∈ s, ‖∑ j ∈ t, A i j * a j‖ ^ 2 ≤ C * ∑ j ∈ t, ‖a j‖ ^ 2) :
    ∀ b : ι → ℂ,
      ∑ j ∈ t, ‖∑ i ∈ s, star (A i j) * b i‖ ^ 2 ≤ C * ∑ i ∈ s, ‖b i‖ ^ 2 := by
  intro b
  let bStar : κ → ℂ := fun j => ∑ i ∈ s, star (A i j) * b i
  let AAb : ι → ℂ := fun i => ∑ j ∈ t, A i j * bStar j
  have hsquare : (∑ j ∈ t, ‖bStar j‖ ^ 2) =
      ‖∑ i ∈ s, b i * star (AAb i)‖ := by
    have hnonneg : 0 ≤ (∑ j ∈ t, ‖bStar j‖ ^ 2 : ℝ) :=
      Finset.sum_nonneg (fun j hj => sq_nonneg _)
    symm
    calc
      ‖∑ i ∈ s, b i * star (AAb i)‖
          = ‖∑ i ∈ s, ∑ j ∈ t, b i * star (A i j) * star (bStar j)‖ := by
            congr 1
            apply Finset.sum_congr rfl
            intro i hi
            calc
              b i * star (∑ j ∈ t, A i j * bStar j)
                  = b i * (∑ j ∈ t, star (A i j) * star (bStar j)) := by
                    congr 1
                    exact (map_sum (starRingEnd ℂ) (fun j => A i j * bStar j) t).trans
                      (Finset.sum_congr rfl (fun j hj =>
                        map_mul (starRingEnd ℂ) (A i j) (bStar j)))
              _ = ∑ j ∈ t, b i * (star (A i j) * star (bStar j)) := by
                    rw [Finset.mul_sum]
              _ = ∑ j ∈ t, b i * star (A i j) * star (bStar j) := by
                    apply Finset.sum_congr rfl
                    intro j hj
                    rw [← mul_assoc]
      _ = ‖∑ j ∈ t, ∑ i ∈ s, b i * star (A i j) * star (bStar j)‖ := by
            congr 1
            rw [Finset.sum_comm]
      _ = ‖∑ j ∈ t, (∑ i ∈ s, b i * star (A i j)) * star (bStar j)‖ := by
            congr 1
            apply Finset.sum_congr rfl
            intro j hj
            rw [← Finset.sum_mul]
      _ = ‖∑ j ∈ t, (∑ i ∈ s, star (A i j) * b i) * star (bStar j)‖ := by
            congr 1
            apply Finset.sum_congr rfl
            intro j hj
            simp [mul_comm]
      _ = ‖∑ j ∈ t, bStar j * star (bStar j)‖ := rfl
      _ = ‖((∑ j ∈ t, ‖bStar j‖ ^ 2 : ℝ) : ℂ)‖ := by
            congr 1
            rw [Complex.ofReal_sum]
            apply Finset.sum_congr rfl
            intro j hj
            exact (Complex.mul_conj (bStar j)).trans (by rw [Complex.normSq_eq_norm_sq])
      _ = ∑ j ∈ t, ‖bStar j‖ ^ 2 := by
            rw [Complex.norm_real, Real.norm_of_nonneg hnonneg]
  have hcs : ‖∑ i ∈ s, b i * star (AAb i)‖ ≤
      Real.sqrt (∑ i ∈ s, ‖b i‖ ^ 2) * Real.sqrt (∑ i ∈ s, ‖AAb i‖ ^ 2) := by
    exact complexCauchySchwarz s b AAb
  have hnorm : (∑ i ∈ s, ‖AAb i‖ ^ 2) ≤ C * ∑ j ∈ t, ‖bStar j‖ ^ 2 := by
    simpa [AAb] using hPrimal bStar
  have hchain : (∑ j ∈ t, ‖bStar j‖ ^ 2) ≤
      Real.sqrt (∑ i ∈ s, ‖b i‖ ^ 2) * Real.sqrt (C * ∑ j ∈ t, ‖bStar j‖ ^ 2) := by
    calc
      (∑ j ∈ t, ‖bStar j‖ ^ 2) = ‖∑ i ∈ s, b i * star (AAb i)‖ := hsquare
      _ ≤
          Real.sqrt (∑ i ∈ s, ‖b i‖ ^ 2) * Real.sqrt (∑ i ∈ s, ‖AAb i‖ ^ 2) := hcs
      _ ≤ Real.sqrt (∑ i ∈ s, ‖b i‖ ^ 2) * Real.sqrt (C * ∑ j ∈ t, ‖bStar j‖ ^ 2) := by
            apply mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
            exact Real.sqrt_le_sqrt hnorm
  by_cases hD0 : (∑ j ∈ t, ‖bStar j‖ ^ 2) = 0
  · rw [hD0]
    exact mul_nonneg hC (Finset.sum_nonneg (fun i hi => sq_nonneg _))
  · have hDpos : 0 < (∑ j ∈ t, ‖bStar j‖ ^ 2) :=
      lt_of_le_of_ne (Finset.sum_nonneg (fun j hj => sq_nonneg _)) (Ne.symm hD0)
    have hS : 0 ≤ ∑ i ∈ s, ‖b i‖ ^ 2 := Finset.sum_nonneg (fun i hi => sq_nonneg _)
    have hCD : 0 ≤ C * ∑ j ∈ t, ‖bStar j‖ ^ 2 :=
      mul_nonneg hC (Finset.sum_nonneg (fun j hj => sq_nonneg _))
    -- Square the nonnegative norm bound and cancel the positive dual energy.
    have hsq2 := pow_le_pow_left₀ hDpos.le hchain 2
    rw [mul_pow, Real.sq_sqrt hS, Real.sq_sqrt hCD] at hsq2
    nlinarith

/-- **Large-sieve duality lemma**: equivalence of the primal and dual forms.
For the converse, replace `A` by its conjugate transpose and use
`star (star x) = x` to recover the primal form. -/
theorem largeSieveDuality {ι κ : Type*}
    (s : Finset ι) (t : Finset κ) (A : ι → κ → ℂ) {C : ℝ} (hC : 0 ≤ C) :
    (∀ a : κ → ℂ, ∑ i ∈ s, ‖∑ j ∈ t, A i j * a j‖ ^ 2 ≤ C * ∑ j ∈ t, ‖a j‖ ^ 2) ↔
      (∀ b : ι → ℂ, ∑ j ∈ t, ‖∑ i ∈ s, star (A i j) * b i‖ ^ 2 ≤ C * ∑ i ∈ s, ‖b i‖ ^ 2) := by
  constructor
  · exact largeSieveDuality_primalToDual s t A hC
  · intro hDual a
    have hPrim := largeSieveDuality_primalToDual (s := t) (t := s)
      (A := fun j i => star (A i j)) hC hDual
    simpa [star_star] using hPrim a


end

end AnalyticNumberTheory.LargeSieve
