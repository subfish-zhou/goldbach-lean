import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryRectangle

/-!
# Rectangular partial summation on a finite indexed carrier

The coordinate map need not be injective: repeated coordinates, arithmetic
coefficients, and all support masks stay inside the original carrier sums.
-/

open scoped BigOperators

namespace LiLiuPrereqFouvry.Rectangle

attribute [local instance] Classical.propDecidable

variable {α ι : Type*} [Fintype ι]

/-- A genuine coordinate rectangle cut out of the original finite carrier. -/
noncomputable def coordinatePrefix (s : Finset α) (coord : α → ι → ℕ)
    (a : α → ℂ) (cap : ι → ℕ) : ℂ :=
  ∑ t ∈ s.filter (fun t => ∀ i, coord t i ≤ cap i), a t

/-- The explicitly constructed maximum over all upper corners of the enclosing box. -/
noncomputable def coordinatePrefixMax (lo hi : ι → ℕ) (s : Finset α)
    (coord : α → ι → ℕ) (a : α → ℂ) : ℝ :=
  ((box lo hi).sup (fun cap => ‖coordinatePrefix s coord a cap‖₊) : NNReal)

theorem coordinatePrefix_norm_le_max (lo hi : ι → ℕ) (s : Finset α)
    (coord : α → ι → ℕ) (a : α → ℂ) (cap : ι → ℕ) (hcap : cap ∈ box lo hi) :
    ‖coordinatePrefix s coord a cap‖ ≤ coordinatePrefixMax lo hi s coord a := by
  unfold coordinatePrefixMax
  exact_mod_cast
    (Finset.le_sup (f := fun cap => ‖coordinatePrefix s coord a cap‖₊) hcap)

theorem coordinatePrefixMax_nonneg (lo hi : ι → ℕ) (s : Finset α)
    (coord : α → ι → ℕ) (a : α → ℂ) :
    0 ≤ coordinatePrefixMax lo hi s coord a :=
  NNReal.coe_nonneg _

/-- Finite multivariate summation by parts on the original indexed carrier.
Only the smooth weight is differenced; no injectivity or coefficient bound is used. -/
theorem summation_by_parts_coordinates (lo hi : ι → ℕ) (s : Finset α)
    (coord : α → ι → ℕ) (w : (ι → ℕ) → ℂ) (a : α → ℂ)
    (hcoord : ∀ t ∈ s, coord t ∈ box lo hi) :
    (∑ t ∈ s, w (coord t) * a t) =
      ∑ cap ∈ box lo hi,
        mixedDifference lo hi w cap * coordinatePrefix s coord a cap := by
  classical
  symm
  unfold coordinatePrefix
  simp only [Finset.mul_sum, Finset.sum_filter, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t ht
  have hc := (mem_box lo hi (coord t)).mp (hcoord t ht)
  have hfilter :
      (box lo hi).filter (fun cap => ∀ i, coord t i ≤ cap i) = box (coord t) hi := by
    ext cap
    simp only [Finset.mem_filter, mem_box]
    constructor
    · rintro ⟨hcap, htc⟩ i
      exact ⟨htc i, (hcap i).2⟩
    · intro hcap
      exact ⟨fun i => ⟨(hc i).1.trans (hcap i).1, (hcap i).2⟩,
        fun i => (hcap i).1⟩
  calc
    (∑ cap ∈ box lo hi,
        if ∀ i, coord t i ≤ cap i then mixedDifference lo hi w cap * a t else 0) =
        (∑ cap ∈ (box lo hi).filter (fun cap => ∀ i, coord t i ≤ cap i),
          mixedDifference lo hi w cap) * a t := by
      rw [Finset.sum_mul, Finset.sum_filter]
    _ = w (coord t) * a t := by
      rw [hfilter, reconstruct lo hi w (coord t) (hcoord t ht)]

/-- A uniform bound for the arithmetic rectangular prefixes can be applied
directly, without first reasoning about the finite maximum. -/
theorem norm_coordinate_sum_le_of_prefix_bound (lo hi : ι → ℕ) (s : Finset α)
    (coord : α → ι → ℕ) (w : (ι → ℕ) → ℂ) (a : α → ℂ)
    (hcoord : ∀ t ∈ s, coord t ∈ box lo hi) (B : ℝ)
    (hB : ∀ cap ∈ box lo hi, ‖coordinatePrefix s coord a cap‖ ≤ B) :
    ‖∑ t ∈ s, w (coord t) * a t‖ ≤ variation lo hi w * B := by
  rw [summation_by_parts_coordinates lo hi s coord w a hcoord]
  calc
    ‖∑ cap ∈ box lo hi,
        mixedDifference lo hi w cap * coordinatePrefix s coord a cap‖ ≤
        ∑ cap ∈ box lo hi,
          ‖mixedDifference lo hi w cap * coordinatePrefix s coord a cap‖ :=
      norm_sum_le _ _
    _ ≤ ∑ cap ∈ box lo hi, ‖mixedDifference lo hi w cap‖ * B := by
      apply Finset.sum_le_sum
      intro cap hcap
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hB cap hcap) (norm_nonneg _)
    _ = variation lo hi w * B := by rw [variation, Finset.sum_mul]

/-- Rectangle-prefix maximum inequality, retaining the original indexed carrier. -/
theorem norm_coordinate_sum_le_variation_mul_max (lo hi : ι → ℕ) (s : Finset α)
    (coord : α → ι → ℕ) (w : (ι → ℕ) → ℂ) (a : α → ℂ)
    (hcoord : ∀ t ∈ s, coord t ∈ box lo hi) :
    ‖∑ t ∈ s, w (coord t) * a t‖ ≤
      variation lo hi w * coordinatePrefixMax lo hi s coord a :=
  norm_coordinate_sum_le_of_prefix_bound lo hi s coord w a hcoord _
    (coordinatePrefix_norm_le_max lo hi s coord a)

/-- Five-coordinate finite-carrier version used by the extracted dispersion phase. -/
theorem norm_coordinate_sum_five_le (lo hi : Fin 5 → ℕ) (s : Finset α)
    (coord : α → Fin 5 → ℕ) (w : (Fin 5 → ℕ) → ℂ) (a : α → ℂ)
    (hcoord : ∀ t ∈ s, ∀ i, lo i ≤ coord t i ∧ coord t i ≤ hi i) :
    ‖∑ t ∈ s, w (coord t) * a t‖ ≤
      variation lo hi w * coordinatePrefixMax lo hi s coord a :=
  norm_coordinate_sum_le_variation_mul_max lo hi s coord w a
    (fun t ht => (mem_box lo hi (coord t)).mpr (hcoord t ht))

end LiLiuPrereqFouvry.Rectangle
