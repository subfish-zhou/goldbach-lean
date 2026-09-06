import AnalyticNumberTheory.LargeSieve.Additive
import AnalyticNumberTheory.LargeSieve.GeomSum
import Mathlib.Tactic

/-! # AnalyticNumberTheory.LargeSieve.Duality

## Dual quadratic-form identity

The central Parseval/tensor-product step in Montgomery's additive large-sieve
proof expands the square sum of `T(n) = Σ_{x∈X} star(e(nx))·b_x`
into a quadratic form with coefficients `b_x·star(b_y)` and kernel
`Σ_n star(e(n(x−y)))`:

  Σ_n |T(n)|² = Σ_x Σ_y b_x·star(b_y)·Σ_n star(e(n(x−y))).

The module proves three levels of this identity:

1. **Finite-matrix expansion** (`dualExpansion`): a purely algebraic identity
   for arbitrary `φ : ι → κ → ℂ` and `b : κ → ℂ`, with no character hypotheses.
2. **Real additive-character version** (`dualQuadraticIdentity`): take
   `φ n x = e(nx)` and use
   `star(e(nx))·e(ny) = star(e(n(x−y)))` to reduce the kernel to
   `Σ_n star(e(n(x−y)))`.
3. **Shifted-interval version** (`dualQuadraticIdentity_Icc`) for
   `n ∈ (M, M+N]`, and **circle version** (`dualQuadraticIdentity_circle`)
   for `charPow n x = e(nx)` on `AddCircle 1`, matching
   `MontgomeryLargeSieveDual`.

The subsequent geometric-sum and Schur-test argument estimates the off-diagonal
kernel entries by `min(N, 1/(2·dist x y))`. These are the kernel estimates used
in the dual large-sieve argument; this module supplies
the identities, not the sharp Montgomery bound.

References: Montgomery, "Topics in Multiplicative Number Theory" (1971), Ch. 1;
Iwaniec & Kowalski, "Analytic Number Theory" (2004), Ch. 7.
-/

namespace AnalyticNumberTheory.LargeSieve

open scoped BigOperators

noncomputable section

/-! ## 1. Finite-matrix expansion -/

/-- Expansion of `|Σ_x c_x|²` as `Σ_x Σ_y c_x·star(c_y)`. -/
theorem normSq_sum_eq_sum_mul_star {ι : Type*} (s : Finset ι) (c : ι → ℂ) :
    (‖∑ x ∈ s, c x‖ : ℂ) ^ 2 = ∑ x ∈ s, ∑ y ∈ s, c x * star (c y) := by
  have hcast : (‖∑ x ∈ s, c x‖ : ℂ) ^ 2 = ((‖∑ x ∈ s, c x‖ ^ 2 : ℝ) : ℂ) :=
    (map_pow (algebraMap ℝ ℂ) (‖∑ x ∈ s, c x‖) 2).symm
  rw [hcast]
  rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]
  change (∑ x ∈ s, c x) * star (∑ x ∈ s, c x) = _
  rw [star_sum, Finset.sum_mul]
  simp only [Finset.mul_sum]

/-- **Dual quadratic-form expansion** (finite matrices): for arbitrary
`φ : ι → κ → ℂ` and `b : κ → ℂ`,

  Σ_n |Σ_x star(φ n x)·b_x|² = Σ_x Σ_y b_x·star(b_y)·(Σ_n star(φ n x)·φ n y).

This is the algebraic foundation of Montgomery's dual large-sieve argument:
the left side sums over `n`, while the right side is regrouped by `x, y`.
The kernel `Σ_n star(φ n x)·φ n y` is the object to be estimated. -/
theorem dualExpansion {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (φ : ι → κ → ℂ) (b : κ → ℂ) :
    (∑ n ∈ s, ‖∑ x ∈ t, star (φ n x) * b x‖ ^ 2) =
      ∑ x ∈ t, ∑ y ∈ t, b x * star (b y) * (∑ n ∈ s, star (φ n x) * φ n y) := by
  let f : ι → κ → κ → ℂ := fun n x y => b x * star (b y) * (star (φ n x) * φ n y)
  calc
    (∑ n ∈ s, ‖∑ x ∈ t, star (φ n x) * b x‖ ^ 2)
        = ∑ n ∈ s, ∑ x ∈ t, ∑ y ∈ t, (star (φ n x) * b x) * star (star (φ n y) * b y) := by
          push_cast
          apply Finset.sum_congr rfl
          intro n hn
          rw [normSq_sum_eq_sum_mul_star]
    _ = ∑ n ∈ s, ∑ x ∈ t, ∑ y ∈ t, f n x y := by
          apply Finset.sum_congr rfl; intro n hn
          apply Finset.sum_congr rfl; intro x hx
          apply Finset.sum_congr rfl; intro y hy
          have hst : star (star (φ n y) * b y) = star (b y) * φ n y := by
            rw [star_mul, star_star]
          rw [hst]
          simp [f]
          ring
    _ = ∑ x ∈ t, ∑ y ∈ t, ∑ n ∈ s, f n x y := by
          calc
            (∑ n ∈ s, ∑ x ∈ t, ∑ y ∈ t, f n x y)
                = ∑ x ∈ t, ∑ n ∈ s, ∑ y ∈ t, f n x y := by
                  rw [Finset.sum_comm]
            _ = ∑ x ∈ t, ∑ y ∈ t, ∑ n ∈ s, f n x y := by
                  apply Finset.sum_congr rfl
                  intro x hx
                  rw [Finset.sum_comm]
    _ = ∑ x ∈ t, ∑ y ∈ t, b x * star (b y) * (∑ n ∈ s, star (φ n x) * φ n y) := by
          apply Finset.sum_congr rfl; intro x hx
          apply Finset.sum_congr rfl; intro y hy
          simp [f]
          rw [← Finset.mul_sum]

/-! ## 2. Real additive-character version -/

/-- Character cross-product identity:
`star(e(nx))·e(ny) = star(e(n(x−y)))` (`n : ℤ`). -/
theorem charReal_cross (n : ℤ) (x y : ℝ) :
    star (charReal ((n : ℝ) * x)) * charReal ((n : ℝ) * y) =
      star (charReal ((n : ℝ) * (x - y))) := by
  rw [mul_sub, charReal_sub, star_mul, star_star, mul_comm]

/-- **Dual quadratic-form identity** (real additive characters):
take `φ n x = e(nx)`.

  Σ_n |Σ_x star(e(nx))·b_x|² = Σ_x Σ_y b_x·star(b_y)·Σ_n star(e(n(x−y))). -/
theorem dualQuadraticIdentity (s : Finset ℤ) (t : Finset ℝ) (b : ℝ → ℂ) :
    (∑ n ∈ s, ‖∑ x ∈ t, star (charReal ((n : ℝ) * x)) * b x‖ ^ 2) =
      ∑ x ∈ t, ∑ y ∈ t, b x * star (b y) *
        (∑ n ∈ s, star (charReal ((n : ℝ) * (x - y)))) := by
  simpa only [charReal_cross] using
    dualExpansion s t (fun n x => charReal ((n : ℝ) * x)) b

/-- **Dual quadratic-form identity (shifted interval)**:
expand the dual form for `n ∈ (M, M+N]`. -/
theorem dualQuadraticIdentity_Icc (M : ℤ) (N : ℕ) (t : Finset ℝ) (b : ℝ → ℂ) :
    (∑ n ∈ Finset.Icc (M + 1) (M + N),
        ‖∑ x ∈ t, star (charReal ((n : ℝ) * x)) * b x‖ ^ 2) =
      ∑ x ∈ t, ∑ y ∈ t, b x * star (b y) *
        (∑ n ∈ Finset.Icc (M + 1) (M + N), star (charReal ((n : ℝ) * (x - y)))) :=
  dualQuadraticIdentity (Finset.Icc (M + 1) (M + N)) t b

/-! ## 3. Circle version (AddCircle 1) -/

/-- Conjugation of a circle character:
`star(e(nx)) = e(−nx)` (n : ℤ, x : AddCircle 1). -/
theorem charPow_star (n : ℤ) (x : AddCircle (1 : ℝ)) :
    star (charPow n x : ℂ) = (charPow (-n) x : ℂ) := by
  dsimp [charPow, unitChar]
  rw [neg_zsmul, AddCircle.toCircle_neg, Circle.coe_inv_eq_conj]

/-- Circle-character product:
`(unitChar (a + b) : ℂ) = (unitChar a : ℂ) * (unitChar b : ℂ)`. -/
theorem unitChar_add (a b : AddCircle (1 : ℝ)) :
    (unitChar (a + b) : ℂ) = (unitChar a : ℂ) * (unitChar b : ℂ) := by
  simpa [unitChar] using congrArg (fun z : Circle => (z : ℂ)) (AddCircle.toCircle_add a b)

/-- Circle-character cross-product identity:
`star(e(nx))·e(ny) = star(e(n(x−y)))` (n : ℤ, x y : AddCircle 1). -/
theorem charPow_cross (n : ℤ) (x y : AddCircle (1 : ℝ)) :
    star (charPow n x : ℂ) * (charPow n y : ℂ) =
      star (charPow n (x - y) : ℂ) := by
  rw [charPow_star, charPow_star]
  change (unitChar ((-n) • x) : ℂ) * (unitChar (n • y) : ℂ) =
    (unitChar ((-n) • (x - y)) : ℂ)
  rw [← unitChar_add]
  congr 2
  simp only [neg_zsmul, zsmul_sub]
  abel

/-- **Dual quadratic-form identity (circle)**: the Parseval expansion
matching `MontgomeryLargeSieveDual`, with kernel `Σ_n star(e(n(x−y)))`. -/
theorem dualQuadraticIdentity_circle (M : ℤ) (N : ℕ)
    (X : Finset (AddCircle (1 : ℝ))) (b : AddCircle (1 : ℝ) → ℂ) :
    (∑ n ∈ Finset.Icc (M + 1) (M + N),
        ‖∑ x ∈ X, star (charPow n x : ℂ) * b x‖ ^ 2) =
      ∑ x ∈ X, ∑ y ∈ X, b x * star (b y) *
        (∑ n ∈ Finset.Icc (M + 1) (M + N), star (charPow n (x - y) : ℂ)) := by
  simpa only [charPow_cross] using
    dualExpansion (Finset.Icc (M + 1) (M + N)) X (fun n x => (charPow n x : ℂ)) b

end

end AnalyticNumberTheory.LargeSieve
