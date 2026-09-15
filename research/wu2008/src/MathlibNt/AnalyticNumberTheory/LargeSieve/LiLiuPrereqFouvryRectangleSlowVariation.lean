import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryRectangleCoordinates
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvrySlowFactorDifference

/-!
# Cardinality-free partial summation for the coupled five-variable weight

The corner stencil is identified with the genuine mixed increments of the
concrete normalized weight. Interior grid widths telescope, and upper faces
contribute one endpoint mass per inactive coordinate. The final factor is at
most `2^5`; no arithmetic coefficient or mask is differentiated.
-/

open scoped BigOperators

namespace LiLiuPrereqFouvry.Rectangle

attribute [local instance] Classical.propDecidable

private theorem sum_bool_succ (n : ℕ) [Fintype (Fin (n + 1) → Bool)]
    (F : (Fin (n + 1) → Bool) → ℂ) :
    (∑ e, F e) = ∑ b : Bool, ∑ e : Fin n → Bool, F (Fin.cons b e) := by
  calc
    (∑ e, F e) = ∑ p : Bool × (Fin n → Bool), F (Fin.cons p.1 p.2) :=
      (Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (n + 1) => Bool))
        (fun p => F (Fin.cons p.1 p.2)) F (fun _ => rfl)).symm
    _ = _ := Fintype.sum_prod_type _

private theorem sum_bool_five [Fintype (Fin 5 → Bool)] (F : (Fin 5 → Bool) → ℂ) :
    (∑ e, F e) =
      ∑ b0 : Bool, ∑ b1 : Bool, ∑ b2 : Bool, ∑ b3 : Bool, ∑ b4 : Bool,
        F ![b0, b1, b2, b3, b4] := by
  simp only [sum_bool_succ, Fintype.sum_unique]
  rfl

private theorem update_point (x : Fin 5 → ℝ) (i : Fin 5) (v : ℝ) :
    Function.update x i v =
      ![if 0 = i then v else x 0, if 1 = i then v else x 1,
        if 2 = i then v else x 2, if 3 = i then v else x 3,
        if 4 = i then v else x 4] := by
  apply funext
  simp [Fin.forall_fin_succ, Function.update]

def activeCoordinates (b : Fin 5 → Bool) : List (Fin 5) :=
  [0, 1, 2, 3, 4].filter b

def endpointDifference (b : Bool) (l h : ℝ) (f : ℝ → ℂ) : ℂ :=
  if b then f l - f h else f l

def endpointCube (b : Fin 5 → Bool) (l h : Fin 5 → ℝ)
    (f : (Fin 5 → ℝ) → ℂ) : ℂ :=
  endpointDifference (b 0) (l 0) (h 0) fun x0 =>
  endpointDifference (b 1) (l 1) (h 1) fun x1 =>
  endpointDifference (b 2) (l 2) (h 2) fun x2 =>
  endpointDifference (b 3) (l 3) (h 3) fun x3 =>
  endpointDifference (b 4) (l 4) (h 4) fun x4 =>
    f ![x0, x1, x2, x3, x4]

private theorem point_eq_vector (x : Fin 5 → ℝ) :
    x = ![x 0, x 1, x 2, x 3, x 4] := by
  apply funext
  simp [Fin.forall_fin_succ]

set_option maxHeartbeats 2000000 in
theorem endpointCube_eq_boxDiff (b : Fin 5 → Bool) (l h : Fin 5 → ℝ)
    (f : (Fin 5 → ℝ) → ℂ) :
    endpointCube b l h f =
      (-1 : ℂ) ^ (activeCoordinates b).length *
        SlowFactor.boxDiff (activeCoordinates b) l h f l := by
  cases h0 : b 0 <;> cases h1 : b 1 <;> cases h2 : b 2 <;>
    cases h3 : b 3 <;> cases h4 : b 4 <;>
    simp [endpointCube, endpointDifference, activeCoordinates, h0, h1, h2, h3, h4,
      SlowFactor.boxDiff, update_point]
  all_goals rw [point_eq_vector l]
  all_goals simp
  all_goals ring

theorem activeCoordinates_nodup (b : Fin 5 → Bool) :
    (activeCoordinates b).Nodup :=
  List.Nodup.filter b (by decide)

theorem norm_endpointCube_eq (b : Fin 5 → Bool) (l h : Fin 5 → ℝ)
    (f : (Fin 5 → ℝ) → ℂ) :
    ‖endpointCube b l h f‖ =
      ‖SlowFactor.boxDiff (activeCoordinates b) l h f l‖ := by
  rw [endpointCube_eq_boxDiff, norm_mul]
  simp

def gridPoint (g : Fin 5 → ℕ → ℝ) (t : Fin 5 → ℕ) : Fin 5 → ℝ :=
  fun i => g i (t i)

private theorem gridPoint_vector (g : Fin 5 → ℕ → ℝ) (t : Fin 5 → ℕ) :
    gridPoint g t = ![g 0 (t 0), g 1 (t 1), g 2 (t 2), g 3 (t 3), g 4 (t 4)] :=
  point_eq_vector _

set_option maxHeartbeats 4000000 in
/-- Exact identification of all boundary-anchored differences with the local
mixed increment; upper boundary coordinates are inactive. -/
theorem mixedDifference_eq_endpointCube (lo hi t : Fin 5 → ℕ)
    (ht : t ∈ box lo hi) (g : Fin 5 → ℕ → ℝ) (f : (Fin 5 → ℝ) → ℂ) :
    mixedDifference lo hi (fun u => f (gridPoint g u)) t =
      endpointCube (fun i => decide (t i < hi i)) (gridPoint g t)
        (gridPoint g (fun i => min (t i + 1) (hi i))) f := by
  let : DecidableEq (Fin 5) := fun a b => Classical.propDecidable (a = b)
  have hl (i : Fin 5) : lo i ≤ t i := ((mem_box lo hi t).mp ht i).1
  have hu (i : Fin 5) : t i ≤ hi i := ((mem_box lo hi t).mp ht i).2
  have hls (i : Fin 5) : lo i ≤ t i + 1 := (hl i).trans (Nat.le_succ _)
  rw [mixedDifference_eq_corners]
  rw [@sum_bool_five _ _]
  by_cases h0 : t 0 < hi 0 <;> by_cases h1 : t 1 < hi 1 <;>
    by_cases h2 : t 2 < hi 2 <;> by_cases h3 : t 3 < hi 3 <;>
    by_cases h4 : t 4 < hi 4
  all_goals
    simp [cornerSign, Fin.prod_univ_succ, extendWeight, mem_box,
      Fin.forall_fin_succ, corner, gridPoint_vector, endpointCube, endpointDifference,
      gridPoint, hl, hu, hls, h0, h1, h2, h3, h4]
  all_goals ring

private theorem prod_filter_map (js : List (Fin 5)) (b : Fin 5 → Bool)
    (r : Fin 5 → ℝ) :
    ((js.filter b).map r).prod = (js.map (fun i => if b i then r i else 1)).prod := by
  induction js with
  | nil => simp
  | cons i js ih =>
    cases hb : b i <;> simp [hb, ih]

theorem sideProduct_activeCoordinates (b : Fin 5 → Bool) (l h : Fin 5 → ℝ) :
    SlowFactor.sideProduct (activeCoordinates b) l h =
      ∏ i, if b i then h i - l i else 1 := by
  unfold SlowFactor.sideProduct activeCoordinates
  rw [prod_filter_map]
  simp [Fin.prod_univ_succ]

/-- The endpoint has mass one; each interior cell has its actual grid width. -/
def cellMass (hi : ℕ) (g : ℕ → ℝ) (t : ℕ) : ℝ :=
  if t < hi then g (t + 1) - g t else 1

theorem sum_cellMass (lo hi : ℕ) (h : lo ≤ hi) (g : ℕ → ℝ) :
    (∑ t ∈ Finset.Icc lo hi, cellMass hi g t) = 1 + g hi - g lo := by
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_succ_top h]
  have hs : (∑ t ∈ Finset.Ico lo hi, cellMass hi g t) =
      ∑ t ∈ Finset.Ico lo hi, (g (t + 1) - g t) := by
    apply Finset.sum_congr rfl
    intro t ht
    simp [cellMass, (Finset.mem_Ico.mp ht).2]
  rw [hs, Finset.sum_Ico_sub g h]
  simp [cellMass]
  ring

/-- The concrete coupled smooth weight satisfies the local anchored-difference
estimate, with no regularity imposed on arithmetic coefficients. -/
theorem norm_mixedDifference_normalizedWeight_le
    (A B V : ℝ) (hV : |A| + |B| ≤ V) (lo hi t : Fin 5 → ℕ)
    (ht : t ∈ box lo hi) (g : Fin 5 → ℕ → ℝ)
    (hg : ∀ i, Monotone (g i))
    (hlo : ∀ i, 1 ≤ g i (lo i)) (hhi : ∀ i, g i (hi i) ≤ 2) :
    ‖mixedDifference lo hi (fun u => SlowFactor.normalizedWeight A B (gridPoint g u)) t‖ ≤
      (64 * (6 + 2 * Real.pi) ^ 5 * (1 + V) ^ 5) *
        ∏ i, cellMass (hi i) (g i) (t i) := by
  have htl (i : Fin 5) : lo i ≤ t i := ((mem_box lo hi t).mp ht i).1
  have hth (i : Fin 5) : t i ≤ hi i := ((mem_box lo hi t).mp ht i).2
  have htn (i : Fin 5) : t i ≤ min (t i + 1) (hi i) :=
    le_min (Nat.le_succ _) (hth i)
  have hlohi : ∀ i, 1 ≤ gridPoint g t i ∧
      gridPoint g t i ≤ gridPoint g (fun i => min (t i + 1) (hi i)) i ∧
      gridPoint g (fun i => min (t i + 1) (hi i)) i ≤ 2 := by
    intro i
    exact ⟨(hlo i).trans (hg i (htl i)), hg i (htn i),
      (hg i (min_le_right _ _)).trans (hhi i)⟩
  have hx : ∀ i, 1 ≤ gridPoint g t i ∧ gridPoint g t i ≤ 2 :=
    fun i => ⟨(hlohi i).1, (hg i (hth i)).trans (hhi i)⟩
  rw [mixedDifference_eq_endpointCube lo hi t ht g, norm_endpointCube_eq]
  have h := SlowFactor.norm_boxDiff_normalizedWeight_le A B V hV
    (activeCoordinates (fun i => decide (t i < hi i))) (activeCoordinates_nodup _)
    (gridPoint g t) (gridPoint g (fun i => min (t i + 1) (hi i)))
    (gridPoint g t) hlohi hx
  rw [sideProduct_activeCoordinates] at h
  convert h using 2
  apply Finset.prod_congr rfl
  intro i _
  by_cases hti : t i < hi i
  · simp [cellMass, hti, gridPoint]
  · simp [cellMass, hti]

/-- Summing the genuine mixed derivative bounds over every cell and every upper
face costs at most `2^5`, independently of the number of integer grid points. -/
theorem variation_normalizedWeight_le
    (A B V : ℝ) (hV : |A| + |B| ≤ V) (lo hi : Fin 5 → ℕ)
    (hbox : ∀ i, lo i ≤ hi i) (g : Fin 5 → ℕ → ℝ)
    (hg : ∀ i, Monotone (g i))
    (hlo : ∀ i, 1 ≤ g i (lo i)) (hhi : ∀ i, g i (hi i) ≤ 2) :
    variation lo hi (fun u => SlowFactor.normalizedWeight A B (gridPoint g u)) ≤
      2048 * (6 + 2 * Real.pi) ^ 5 * (1 + V) ^ 5 := by
  let : DecidableEq (Fin 5) := fun a b => Classical.propDecidable (a = b)
  let C : ℝ := 64 * (6 + 2 * Real.pi) ^ 5 * (1 + V) ^ 5
  have hV0 : 0 ≤ V := (add_nonneg (abs_nonneg A) (abs_nonneg B)).trans hV
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hp :
      (∏ i : Fin 5, (1 + g i (hi i) - g i (lo i))) ≤ (32 : ℝ) := by
    calc
      (∏ i : Fin 5, (1 + g i (hi i) - g i (lo i))) ≤ ∏ _i : Fin 5, (2 : ℝ) := by
        apply Finset.prod_le_prod
        · intro i _
          have := hg i (hbox i)
          linarith
        · intro i _
          linarith [hlo i, hhi i]
      _ = 32 := by norm_num
  calc
    variation lo hi (fun u => SlowFactor.normalizedWeight A B (gridPoint g u)) ≤
        ∑ t ∈ box lo hi, C * ∏ i, cellMass (hi i) (g i) (t i) := by
      apply Finset.sum_le_sum
      intro t ht
      exact norm_mixedDifference_normalizedWeight_le A B V hV lo hi t ht g hg hlo hhi
    _ = C * ∏ i, (1 + g i (hi i) - g i (lo i)) := by
      rw [← Finset.mul_sum, box,
        ← Finset.prod_univ_sum (fun i => Finset.Icc (lo i) (hi i))
          (fun i t => cellMass (hi i) (g i) t)]
      simp_rw [sum_cellMass _ _ (hbox _)]
    _ ≤ C * 32 := mul_le_mul_of_nonneg_left hp hC
    _ = 2048 * (6 + 2 * Real.pi) ^ 5 * (1 + V) ^ 5 := by dsimp [C]; ring

/-- Positive-reference normalization, convenient for actual dyadic rectangles. -/
theorem variation_normalizedWeight_div_le
    (A B V : ℝ) (hV : |A| + |B| ≤ V) (lo hi : Fin 5 → ℕ)
    (hbox : ∀ i, lo i ≤ hi i) (R : Fin 5 → ℝ) (hR : ∀ i, 0 < R i)
    (hlo : ∀ i, R i ≤ (lo i : ℝ)) (hhi : ∀ i, (hi i : ℝ) ≤ 2 * R i) :
    variation lo hi (fun u => SlowFactor.normalizedWeight A B (fun i => (u i : ℝ) / R i)) ≤
      2048 * (6 + 2 * Real.pi) ^ 5 * (1 + V) ^ 5 := by
  apply variation_normalizedWeight_le A B V hV lo hi hbox
    (fun i n => (n : ℝ) / R i)
  · intro i m n hmn
    exact div_le_div_of_nonneg_right (by exact_mod_cast hmn) (hR i).le
  · intro i
    exact (le_div_iff₀ (hR i)).mpr (by simpa using hlo i)
  · intro i
    exact (div_le_iff₀ (hR i)).mpr (hhi i)

theorem variation_singleton (x : Fin 5 → ℕ) (w : (Fin 5 → ℕ) → ℂ) :
    variation x x w = ‖w x‖ := by
  have h := reconstruct x x w x (by simp)
  simp only [box_self, Finset.sum_singleton] at h
  simp [variation, h]

theorem variation_eq_zero_of_box_empty (lo hi : Fin 5 → ℕ)
    (w : (Fin 5 → ℕ) → ℂ) (h : box lo hi = ∅) :
    variation lo hi w = 0 := by
  simp [variation, h]

/-- The concrete arithmetic-grid estimate also covers empty boxes, without an
endpoint-order premise. Singleton sides contribute their endpoint mass only. -/
theorem variation_normalizedWeight_div_le_all
    (A B V : ℝ) (hV : |A| + |B| ≤ V) (lo hi : Fin 5 → ℕ)
    (R : Fin 5 → ℝ) (hR : ∀ i, 0 < R i)
    (hlo : ∀ i, R i ≤ (lo i : ℝ)) (hhi : ∀ i, (hi i : ℝ) ≤ 2 * R i) :
    variation lo hi (fun u => SlowFactor.normalizedWeight A B (fun i => (u i : ℝ) / R i)) ≤
      2048 * (6 + 2 * Real.pi) ^ 5 * (1 + V) ^ 5 := by
  by_cases hbox : ∀ i, lo i ≤ hi i
  · exact variation_normalizedWeight_div_le A B V hV lo hi hbox R hR hlo hhi
  · have hempty : box lo hi = ∅ := by
      apply (box_eq_empty_iff lo hi).mpr
      push Not at hbox
      exact hbox
    rw [variation_eq_zero_of_box_empty lo hi _ hempty]
    have hV0 : 0 ≤ V := (add_nonneg (abs_nonneg A) (abs_nonneg B)).trans hV
    positivity

/-- Complete smooth-weight removal on an arbitrary finite carrier. All repeated
coordinates, signs, support masks, and arithmetic phases remain in `a`. -/
theorem norm_coordinate_sum_normalizedWeight_le {α : Type*}
    (A B V : ℝ) (hV : |A| + |B| ≤ V) (lo hi : Fin 5 → ℕ)
    (hbox : ∀ i, lo i ≤ hi i) (g : Fin 5 → ℕ → ℝ)
    (hg : ∀ i, Monotone (g i))
    (hlo : ∀ i, 1 ≤ g i (lo i)) (hhi : ∀ i, g i (hi i) ≤ 2)
    (s : Finset α) (coord : α → Fin 5 → ℕ) (a : α → ℂ)
    (hcoord : ∀ t ∈ s, coord t ∈ box lo hi) :
    ‖∑ t ∈ s, SlowFactor.normalizedWeight A B (gridPoint g (coord t)) * a t‖ ≤
      (2048 * (6 + 2 * Real.pi) ^ 5 * (1 + V) ^ 5) *
        coordinatePrefixMax lo hi s coord a :=
  (norm_coordinate_sum_le_variation_mul_max lo hi s coord
    (fun u => SlowFactor.normalizedWeight A B (gridPoint g u)) a hcoord).trans
      (mul_le_mul_of_nonneg_right
        (variation_normalizedWeight_le A B V hV lo hi hbox g hg hlo hhi)
        (coordinatePrefixMax_nonneg lo hi s coord a))

/-- Dyadic-reference version of complete smooth-weight removal. -/
theorem norm_coordinate_sum_normalizedWeight_div_le {α : Type*}
    (A B V : ℝ) (hV : |A| + |B| ≤ V) (lo hi : Fin 5 → ℕ)
    (hbox : ∀ i, lo i ≤ hi i) (R : Fin 5 → ℝ) (hR : ∀ i, 0 < R i)
    (hlo : ∀ i, R i ≤ (lo i : ℝ)) (hhi : ∀ i, (hi i : ℝ) ≤ 2 * R i)
    (s : Finset α) (coord : α → Fin 5 → ℕ) (a : α → ℂ)
    (hcoord : ∀ t ∈ s, coord t ∈ box lo hi) :
    ‖∑ t ∈ s, SlowFactor.normalizedWeight A B (fun i => (coord t i : ℝ) / R i) * a t‖ ≤
      (2048 * (6 + 2 * Real.pi) ^ 5 * (1 + V) ^ 5) *
        coordinatePrefixMax lo hi s coord a :=
  (norm_coordinate_sum_le_variation_mul_max lo hi s coord
    (fun u => SlowFactor.normalizedWeight A B (fun i => (u i : ℝ) / R i)) a hcoord).trans
      (mul_le_mul_of_nonneg_right
        (variation_normalizedWeight_div_le A B V hV lo hi hbox R hR hlo hhi)
        (coordinatePrefixMax_nonneg lo hi s coord a))

/-- Empty-box-safe finite-carrier version of the concrete weight-removal theorem. -/
theorem norm_coordinate_sum_normalizedWeight_div_le_all {α : Type*}
    (A B V : ℝ) (hV : |A| + |B| ≤ V) (lo hi : Fin 5 → ℕ)
    (R : Fin 5 → ℝ) (hR : ∀ i, 0 < R i)
    (hlo : ∀ i, R i ≤ (lo i : ℝ)) (hhi : ∀ i, (hi i : ℝ) ≤ 2 * R i)
    (s : Finset α) (coord : α → Fin 5 → ℕ) (a : α → ℂ)
    (hcoord : ∀ t ∈ s, coord t ∈ box lo hi) :
    ‖∑ t ∈ s, SlowFactor.normalizedWeight A B (fun i => (coord t i : ℝ) / R i) * a t‖ ≤
      (2048 * (6 + 2 * Real.pi) ^ 5 * (1 + V) ^ 5) *
        coordinatePrefixMax lo hi s coord a :=
  (norm_coordinate_sum_le_variation_mul_max lo hi s coord
    (fun u => SlowFactor.normalizedWeight A B (fun i => (u i : ℝ) / R i)) a hcoord).trans
      (mul_le_mul_of_nonneg_right
        (variation_normalizedWeight_div_le_all A B V hV lo hi R hR hlo hhi)
        (coordinatePrefixMax_nonneg lo hi s coord a))

end LiLiuPrereqFouvry.Rectangle
