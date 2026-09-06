import MathlibNt.SieveTheory.Arithmetic.PrimeReciprocalLogScale

/-!
# Prime reciprocal sums on fixed logarithmic rectangles

This module defines the reciprocal mass of the ordered prime pairs in

`(N ^ a₀, N ^ a₁] × (N ^ b₀, N ^ b₁]`.

The strict lower and non-strict upper endpoints are retained literally.  The
mass factors exactly into the two one-dimensional interval sums, so the fixed
rectangle limit follows from `PrimeReciprocalLogScale`.  Finite weighted sums
then give a reusable simple-function limit for fixed Darboux grids.

No moving boundary or kernel-weighted transfer is asserted here.
-/

namespace MathlibNt.SieveTheory.PrimeReciprocalLogRectangle

open Filter Real Finset
open scoped Topology
open PrimeReciprocalLogScale

/-- The double reciprocal mass of ordered prime pairs in the fixed logarithmic
rectangle `(N ^ a₀, N ^ a₁] × (N ^ b₀, N ^ b₁]`. -/
noncomputable def primeReciprocalLogRectangle
    (N : ℕ) (a₀ a₁ b₀ b₁ : ℝ) : ℝ :=
  ((Finset.range (rpowFloor N a₁ + 1)).filter fun p₁ : ℕ =>
    p₁.Prime ∧ (N : ℝ) ^ a₀ < (p₁ : ℝ) ∧ (p₁ : ℝ) ≤ (N : ℝ) ^ a₁).sum fun p₁ =>
      ((Finset.range (rpowFloor N b₁ + 1)).filter fun p₂ : ℕ =>
        p₂.Prime ∧ (N : ℝ) ^ b₀ < (p₂ : ℝ) ∧ (p₂ : ℝ) ≤ (N : ℝ) ^ b₁).sum fun p₂ =>
          1 / ((p₁ : ℝ) * (p₂ : ℝ))

/-- The logarithmic mass of the rectangle `(a₀, a₁] × (b₀, b₁]`. -/
noncomputable def logarithmicRectangleMass (a₀ a₁ b₀ b₁ : ℝ) : ℝ :=
  Real.log (a₁ / a₀) * Real.log (b₁ / b₀)

/-- The ordered-pair reciprocal mass factors exactly into its two interval
masses. -/
theorem primeReciprocalLogRectangle_eq_mul (N : ℕ) (a₀ a₁ b₀ b₁ : ℝ) :
    primeReciprocalLogRectangle N a₀ a₁ b₀ b₁ =
      primeReciprocalLogInterval N a₀ a₁ *
        primeReciprocalLogInterval N b₀ b₁ := by
  unfold primeReciprocalLogRectangle primeReciprocalLogInterval
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p₁ hp₁
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p₂ hp₂
  simp only [one_div, mul_inv]

/-- For a fixed positive logarithmic rectangle, its ordered-prime-pair mass
tends to its logarithmic area. -/
theorem tendsto_primeReciprocalLogRectangle {a₀ a₁ b₀ b₁ : ℝ}
    (ha₀ : 0 < a₀) (ha : a₀ < a₁) (hb₀ : 0 < b₀) (hb : b₀ < b₁) :
    Tendsto (fun N : ℕ => primeReciprocalLogRectangle N a₀ a₁ b₀ b₁) atTop
      (nhds (logarithmicRectangleMass a₀ a₁ b₀ b₁)) := by
  simpa only [primeReciprocalLogRectangle_eq_mul, logarithmicRectangleMass] using
    (tendsto_primeReciprocalLogInterval ha₀ ha).mul
      (tendsto_primeReciprocalLogInterval hb₀ hb)

/-- Eventual epsilon form of the fixed logarithmic rectangle limit. -/
theorem eventually_abs_primeReciprocalLogRectangle_sub_lt
    {a₀ a₁ b₀ b₁ ε : ℝ} (ha₀ : 0 < a₀) (ha : a₀ < a₁)
    (hb₀ : 0 < b₀) (hb : b₀ < b₁) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      |primeReciprocalLogRectangle N a₀ a₁ b₀ b₁ -
        logarithmicRectangleMass a₀ a₁ b₀ b₁| < ε := by
  simpa only [Real.dist_eq] using
    (Metric.tendsto_nhds.mp (tendsto_primeReciprocalLogRectangle ha₀ ha hb₀ hb)) ε hε

/-- Threshold form of the fixed logarithmic rectangle limit. -/
theorem exists_abs_primeReciprocalLogRectangle_sub_lt
    {a₀ a₁ b₀ b₁ ε : ℝ} (ha₀ : 0 < a₀) (ha : a₀ < a₁)
    (hb₀ : 0 < b₀) (hb : b₀ < b₁) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      |primeReciprocalLogRectangle N a₀ a₁ b₀ b₁ -
        logarithmicRectangleMass a₀ a₁ b₀ b₁| < ε := by
  simpa only [eventually_atTop] using
    (eventually_abs_primeReciprocalLogRectangle_sub_lt ha₀ ha hb₀ hb hε)

variable {ι : Type*}

/-- A fixed finite weighted sum of logarithmic rectangle masses converges to
the same weighted sum of logarithmic areas. -/
theorem tendsto_weighted_sum_primeReciprocalLogRectangle
    (s : Finset ι) (c a₀ a₁ b₀ b₁ : ι → ℝ)
    (ha₀ : ∀ i ∈ s, 0 < a₀ i) (ha : ∀ i ∈ s, a₀ i < a₁ i)
    (hb₀ : ∀ i ∈ s, 0 < b₀ i) (hb : ∀ i ∈ s, b₀ i < b₁ i) :
    Tendsto
      (fun N : ℕ => ∑ i ∈ s, c i *
        primeReciprocalLogRectangle N (a₀ i) (a₁ i) (b₀ i) (b₁ i))
      atTop
      (nhds (∑ i ∈ s, c i *
        logarithmicRectangleMass (a₀ i) (a₁ i) (b₀ i) (b₁ i))) := by
  refine tendsto_finsetSum s ?_
  intro i hi
  exact (tendsto_primeReciprocalLogRectangle
    (ha₀ i hi) (ha i hi) (hb₀ i hi) (hb i hi)).const_mul (c i)

/-- Eventual epsilon form of finite-grid convergence. -/
theorem eventually_abs_weighted_sum_primeReciprocalLogRectangle_sub_lt
    (s : Finset ι) (c a₀ a₁ b₀ b₁ : ι → ℝ)
    (ha₀ : ∀ i ∈ s, 0 < a₀ i) (ha : ∀ i ∈ s, a₀ i < a₁ i)
    (hb₀ : ∀ i ∈ s, 0 < b₀ i) (hb : ∀ i ∈ s, b₀ i < b₁ i)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      |(∑ i ∈ s, c i *
          primeReciprocalLogRectangle N (a₀ i) (a₁ i) (b₀ i) (b₁ i)) -
        ∑ i ∈ s, c i *
          logarithmicRectangleMass (a₀ i) (a₁ i) (b₀ i) (b₁ i)| < ε := by
  simpa only [Real.dist_eq] using
    (Metric.tendsto_nhds.mp (tendsto_weighted_sum_primeReciprocalLogRectangle
      s c a₀ a₁ b₀ b₁ ha₀ ha hb₀ hb)) ε hε

/-- Threshold form of fixed finite weighted-grid convergence. -/
theorem exists_abs_weighted_sum_primeReciprocalLogRectangle_sub_lt
    (s : Finset ι) (c a₀ a₁ b₀ b₁ : ι → ℝ)
    (ha₀ : ∀ i ∈ s, 0 < a₀ i) (ha : ∀ i ∈ s, a₀ i < a₁ i)
    (hb₀ : ∀ i ∈ s, 0 < b₀ i) (hb : ∀ i ∈ s, b₀ i < b₁ i)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      |(∑ i ∈ s, c i *
          primeReciprocalLogRectangle N (a₀ i) (a₁ i) (b₀ i) (b₁ i)) -
        ∑ i ∈ s, c i *
          logarithmicRectangleMass (a₀ i) (a₁ i) (b₀ i) (b₁ i)| < ε := by
  simpa only [eventually_atTop] using
    (eventually_abs_weighted_sum_primeReciprocalLogRectangle_sub_lt
      s c a₀ a₁ b₀ b₁ ha₀ ha hb₀ hb hε)

end MathlibNt.SieveTheory.PrimeReciprocalLogRectangle
