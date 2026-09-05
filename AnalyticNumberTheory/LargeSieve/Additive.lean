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

/-- `e(x) = exp(2πix)`: the standard additive character on `AddCircle 1`
(mathlib's `AddCircle.toCircle`; see `AddCircle.toCircle_apply_mk`). -/
def unitChar (x : AddCircle (1 : ℝ)) : Circle :=
  AddCircle.toCircle (T := (1 : ℝ)) x

/-- `e(nx) = e(x)^n` (`n : ℤ`): compatibility of the character with integer
multiplication (`AddCircle.toCircle_zsmul`). -/
def charPow (n : ℤ) (x : AddCircle (1 : ℝ)) : Circle :=
  unitChar (n • x)

/-- The weighted exponential sum `Σ_{M<n≤M+N} a_n e(nx)` on `(M, M+N]`. -/
noncomputable def circleCharSum (M : ℤ) (N : ℕ) (a : ℤ → ℂ) (x : AddCircle (1 : ℝ)) : ℂ :=
  ∑ n ∈ Finset.Icc (M + 1) (M + N), a n * (charPow n x : ℂ)

/-- `X ⊆ AddCircle 1` is `δ`-well-spaced: any two distinct points have
distance modulo 1 at least `δ`. -/
noncomputable def wellSpaced (X : Finset (AddCircle (1 : ℝ))) (δ : ℝ) : Prop :=
  ∀ ⦃x : AddCircle (1 : ℝ)⦄, x ∈ X → ∀ ⦃y : AddCircle (1 : ℝ)⦄, y ∈ X → x ≠ y → δ ≤ dist x y

/-! ## 2. Additive large-sieve target statements -/

/-- **Additive large sieve** (Montgomery, primal form): for a `δ`-well-spaced
set `X` and any finitely supported complex sequence `a : ℤ → ℂ`,

  Σ_{x∈X} |Σ_{M<n≤M+N} a_n e(nx)|² ≤ (N + 1/δ) · Σ_{M<n≤M+N} |a_n|².

This is a target proposition, not a bound proved here. The classical proof uses
the dual form, a geometric-sum bound, and the Schur test. -/
def MontgomeryLargeSievePrimal (M : ℤ) (N : ℕ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∀ X : Finset (AddCircle (1 : ℝ)), wellSpaced X δ →
    ∀ a : ℤ → ℂ,
      ∑ x ∈ X, ‖circleCharSum M N a x‖ ^ 2 ≤
        ((N : ℝ) + 1 / δ) * ∑ n ∈ Finset.Icc (M + 1) (M + N), ‖a n‖ ^ 2

/-- **Dual additive large sieve** (defined using the conjugate transpose):

  Σ_{M<n≤M+N} |Σ_{x∈X} conj(e(nx))·b_x|² ≤ (N + 1/δ) · Σ_{x∈X} |b_x|².

In the classical formulation, `conj(e(nx))` is written as `e(-nx)`; conjugating
`b` gives the equivalent form with the opposite sign in the exponential. -/
def MontgomeryLargeSieveDual (M : ℤ) (N : ℕ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∀ X : Finset (AddCircle (1 : ℝ)), wellSpaced X δ →
    ∀ b : AddCircle (1 : ℝ) → ℂ,
      ∑ n ∈ Finset.Icc (M + 1) (M + N),
        ‖∑ x ∈ X, star (charPow n x : ℂ) * b x‖ ^ 2 ≤
        ((N : ℝ) + 1 / δ) * ∑ x ∈ X, ‖b x‖ ^ 2

/-! ## 3. Duality lemma (the algebraic foundation of the large sieve) -/

/-- **Real Cauchy--Schwarz** (Finset): `(Σ aᵢbᵢ)² ≤ (Σ aᵢ²)(Σ bᵢ²)`,
proved via Lagrange's identity
`ΣᵢΣⱼ (aᵢbⱼ − aⱼbᵢ)² = 2(Σa²)(Σb²) − 2(Σab)²`. -/
theorem realCauchySchwarz {ι : Type*} (s : Finset ι) (a b : ι → ℝ) :
    (∑ i ∈ s, a i * b i) ^ 2 ≤ (∑ i ∈ s, a i ^ 2) * (∑ i ∈ s, b i ^ 2) := by
  have hsq : 0 ≤ ∑ i ∈ s, ∑ j ∈ s, (a i * b j - a j * b i) ^ 2 := by
    refine Finset.sum_nonneg ?_
    intro i hi
    exact Finset.sum_nonneg (fun j hj => sq_nonneg _)
  have hsplit : (∑ i ∈ s, ∑ j ∈ s,
        (a i ^ 2 * b j ^ 2 + a j ^ 2 * b i ^ 2 - 2 * ((a i * b j) * (a j * b i)))) =
      (∑ i ∈ s, ∑ j ∈ s, a i ^ 2 * b j ^ 2) +
        (∑ i ∈ s, ∑ j ∈ s, a j ^ 2 * b i ^ 2) -
        (∑ i ∈ s, ∑ j ∈ s, 2 * ((a i * b j) * (a j * b i))) := by
    calc
      (∑ i ∈ s, ∑ j ∈ s,
          (a i ^ 2 * b j ^ 2 + a j ^ 2 * b i ^ 2 - 2 * ((a i * b j) * (a j * b i))))
          = ∑ i ∈ s, ((∑ j ∈ s, a i ^ 2 * b j ^ 2) +
                (∑ j ∈ s, a j ^ 2 * b i ^ 2) - (∑ j ∈ s, 2 * ((a i * b j) * (a j * b i)))) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
      _ = (∑ i ∈ s, ∑ j ∈ s, a i ^ 2 * b j ^ 2) +
            (∑ i ∈ s, ∑ j ∈ s, a j ^ 2 * b i ^ 2) -
            (∑ i ∈ s, ∑ j ∈ s, 2 * ((a i * b j) * (a j * b i))) := by
            rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  have hidsum : (∑ i ∈ s, ∑ j ∈ s, (a i * b j - a j * b i) ^ 2) =
      2 * (∑ i ∈ s, a i ^ 2) * (∑ j ∈ s, b j ^ 2) - 2 * (∑ i ∈ s, a i * b i) ^ 2 := by
    calc
      (∑ i ∈ s, ∑ j ∈ s, (a i * b j - a j * b i) ^ 2)
          = ∑ i ∈ s, ∑ j ∈ s,
              (a i ^ 2 * b j ^ 2 + a j ^ 2 * b i ^ 2 - 2 * ((a i * b j) * (a j * b i))) := by
            apply Finset.sum_congr rfl
            intro i hi
            apply Finset.sum_congr rfl
            intro j hj
            ring
      _ = (∑ i ∈ s, ∑ j ∈ s, a i ^ 2 * b j ^ 2) +
            (∑ i ∈ s, ∑ j ∈ s, a j ^ 2 * b i ^ 2) -
            (∑ i ∈ s, ∑ j ∈ s, 2 * ((a i * b j) * (a j * b i))) := by
            exact hsplit
      _ = (∑ i ∈ s, a i ^ 2) * (∑ j ∈ s, b j ^ 2) +
            (∑ i ∈ s, a i ^ 2) * (∑ j ∈ s, b j ^ 2) -
            2 * (∑ i ∈ s, a i * b i) * (∑ j ∈ s, a j * b j) := by
            have hT1 : (∑ i ∈ s, ∑ j ∈ s, a i ^ 2 * b j ^ 2) =
                (∑ i ∈ s, a i ^ 2) * (∑ j ∈ s, b j ^ 2) := by
              rw [← Finset.sum_mul_sum]
            have hT2 : (∑ i ∈ s, ∑ j ∈ s, a j ^ 2 * b i ^ 2) =
                (∑ i ∈ s, a i ^ 2) * (∑ j ∈ s, b j ^ 2) := by
              rw [Finset.sum_comm]
              rw [← Finset.sum_mul_sum]
            have hT3 : (∑ i ∈ s, ∑ j ∈ s, 2 * ((a i * b j) * (a j * b i))) =
                2 * (∑ i ∈ s, a i * b i) * (∑ j ∈ s, a j * b j) := by
              calc
                (∑ i ∈ s, ∑ j ∈ s, 2 * ((a i * b j) * (a j * b i)))
                    = ∑ i ∈ s, ∑ j ∈ s, (a i * b i) * (2 * (a j * b j)) := by
                      apply Finset.sum_congr rfl
                      intro i hi
                      apply Finset.sum_congr rfl
                      intro j hj
                      ring
                _ = (∑ i ∈ s, a i * b i) * (∑ j ∈ s, 2 * (a j * b j)) := by
                      rw [← Finset.sum_mul_sum]
                _ = (∑ i ∈ s, a i * b i) * (2 * ∑ j ∈ s, a j * b j) := by
                      rw [← Finset.mul_sum]
                _ = 2 * (∑ i ∈ s, a i * b i) * (∑ j ∈ s, a j * b j) := by
                      ring
            rw [hT1, hT2, hT3]
      _ = 2 * (∑ i ∈ s, a i ^ 2) * (∑ j ∈ s, b j ^ 2) - 2 * (∑ i ∈ s, a i * b i) ^ 2 := by
            ring
  nlinarith

/-- **Complex Cauchy--Schwarz** (Finset):
`|Σᵢ xᵢ·conj(yᵢ)| ≤ √(Σ‖xᵢ‖²)·√(Σ‖yᵢ‖²)`, proved using the triangle
inequality and real Cauchy--Schwarz. -/
theorem complexCauchySchwarz {ι : Type*} (s : Finset ι) (x y : ι → ℂ) :
    ‖∑ i ∈ s, x i * star (y i)‖ ≤
      Real.sqrt (∑ i ∈ s, ‖x i‖ ^ 2) * Real.sqrt (∑ i ∈ s, ‖y i‖ ^ 2) := by
  have htri : ‖∑ i ∈ s, x i * star (y i)‖ ≤ ∑ i ∈ s, ‖x i * star (y i)‖ := by
    exact norm_sum_le s (fun i => x i * star (y i))
  have habs : (∑ i ∈ s, ‖x i * star (y i)‖) = ∑ i ∈ s, ‖x i‖ * ‖y i‖ := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [norm_mul, norm_star]
  have hA : 0 ≤ ∑ i ∈ s, ‖x i‖ ^ 2 := Finset.sum_nonneg (fun i hi => sq_nonneg _)
  have hB : 0 ≤ ∑ i ∈ s, ‖y i‖ ^ 2 := Finset.sum_nonneg (fun i hi => sq_nonneg _)
  have hcs : (∑ i ∈ s, ‖x i‖ * ‖y i‖) ^ 2 ≤
      (∑ i ∈ s, ‖x i‖ ^ 2) * (∑ i ∈ s, ‖y i‖ ^ 2) := by
    exact realCauchySchwarz s (fun i => ‖x i‖) (fun i => ‖y i‖)
  have hcs' : (∑ i ∈ s, ‖x i‖ * ‖y i‖) ≤
      Real.sqrt (∑ i ∈ s, ‖x i‖ ^ 2) * Real.sqrt (∑ i ∈ s, ‖y i‖ ^ 2) := by
    have hsq : (∑ i ∈ s, ‖x i‖ * ‖y i‖) ^ 2 ≤
        (Real.sqrt (∑ i ∈ s, ‖x i‖ ^ 2) * Real.sqrt (∑ i ∈ s, ‖y i‖ ^ 2)) ^ 2 := by
      nlinarith [hcs, Real.sq_sqrt hA, Real.sq_sqrt hB]
    have habs := (sq_le_sq).mp hsq
    have hc_nonneg : 0 ≤ ∑ i ∈ s, ‖x i‖ * ‖y i‖ :=
      Finset.sum_nonneg (fun i hi => mul_nonneg (norm_nonneg _) (norm_nonneg _))
    have hu_nonneg : 0 ≤ Real.sqrt (∑ i ∈ s, ‖x i‖ ^ 2) * Real.sqrt (∑ i ∈ s, ‖y i‖ ^ 2) :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    rwa [abs_of_nonneg hc_nonneg, abs_of_nonneg hu_nonneg] at habs
  exact le_trans (le_trans htri (le_of_eq habs)) hcs'

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
            have hCD : 0 ≤ C * ∑ j ∈ t, ‖bStar j‖ ^ 2 :=
              mul_nonneg hC (Finset.sum_nonneg (fun j hj => sq_nonneg _))
            exact (Real.sqrt_le_sqrt_iff hCD).2 hnorm
  by_cases hD0 : (∑ j ∈ t, ‖bStar j‖ ^ 2) = 0
  · rw [hD0]
    exact mul_nonneg hC (Finset.sum_nonneg (fun i hi => sq_nonneg _))
  · have hDpos : 0 < (∑ j ∈ t, ‖bStar j‖ ^ 2) :=
      lt_of_le_of_ne (Finset.sum_nonneg (fun j hj => sq_nonneg _)) (Ne.symm hD0)
    have hS : 0 ≤ ∑ i ∈ s, ‖b i‖ ^ 2 := Finset.sum_nonneg (fun i hi => sq_nonneg _)
    have hCD : 0 ≤ C * ∑ j ∈ t, ‖bStar j‖ ^ 2 :=
      mul_nonneg hC (Finset.sum_nonneg (fun j hj => sq_nonneg _))
    have hsq2 : (∑ j ∈ t, ‖bStar j‖ ^ 2) ^ 2 ≤
        C * (∑ i ∈ s, ‖b i‖ ^ 2) * (∑ j ∈ t, ‖bStar j‖ ^ 2) := by
      have hsq2' : (∑ j ∈ t, ‖bStar j‖ ^ 2) ^ 2 ≤
          (Real.sqrt (∑ i ∈ s, ‖b i‖ ^ 2) * Real.sqrt (C * ∑ j ∈ t, ‖bStar j‖ ^ 2)) ^ 2 := by
        have hD_nonneg : 0 ≤ ∑ j ∈ t, ‖bStar j‖ ^ 2 :=
          Finset.sum_nonneg (fun j hj => sq_nonneg _)
        have hu_nonneg : 0 ≤ Real.sqrt (∑ i ∈ s, ‖b i‖ ^ 2) *
            Real.sqrt (C * ∑ j ∈ t, ‖bStar j‖ ^ 2) :=
          mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
        have habs : |∑ j ∈ t, ‖bStar j‖ ^ 2| ≤
            |Real.sqrt (∑ i ∈ s, ‖b i‖ ^ 2) * Real.sqrt (C * ∑ j ∈ t, ‖bStar j‖ ^ 2)| := by
          rwa [abs_of_nonneg hD_nonneg, abs_of_nonneg hu_nonneg]
        exact (sq_le_sq).mpr habs
      nlinarith [hsq2', Real.sq_sqrt hS, Real.sq_sqrt hCD]
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

/-- **Additive large sieve: primal ⟺ dual**. Apply the general duality lemma
to the character matrix `A x n = e(nx)` with `C = N + 1/δ`. Thus the two
target statements are equivalent: proving either one gives the other. -/
theorem montgomeryDuality (M : ℤ) (N : ℕ) :
    MontgomeryLargeSievePrimal M N ↔ MontgomeryLargeSieveDual M N := by
  have hC : ∀ δ : ℝ, 0 < δ → 0 ≤ (N : ℝ) + 1 / δ := by
    intro δ hδ
    positivity
  constructor
  · intro hprimal δ hδ X hws b
    have hpr : ∀ a : ℤ → ℂ, ∑ x ∈ X,
        ‖∑ n ∈ Finset.Icc (M + 1) (M + N), (charPow n x : ℂ) * a n‖ ^ 2 ≤
          ((N : ℝ) + 1 / δ) * ∑ n ∈ Finset.Icc (M + 1) (M + N), ‖a n‖ ^ 2 := by
      simpa [circleCharSum, mul_comm] using hprimal δ hδ X hws
    have hdual := (largeSieveDuality (s := X) (t := Finset.Icc (M + 1) (M + N))
      (A := fun x n => (charPow n x : ℂ)) (hC δ hδ)).1 hpr
    exact hdual b
  · intro hdual δ hδ X hws a
    have hpr := (largeSieveDuality (s := X) (t := Finset.Icc (M + 1) (M + N))
      (A := fun x n => (charPow n x : ℂ)) (hC δ hδ)).2 (hdual δ hδ X hws)
    simpa [circleCharSum, mul_comm] using hpr a

end

end AnalyticNumberTheory.LargeSieve
