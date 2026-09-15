import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighSections
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Data.Finset.Sort

open scoped BigOperators Classical
open MeasureTheory
namespace Wu2008DoubleSieve.HighUnit

/-- The actual graph chart has the prescribed total coordinate sum. -/
theorem append_sum {n : ℕ} (phi : ℝ) (t : Fin n → ℝ) :
    ∑ i, append phi t i = phi := by
  simp [append, Fin.sum_univ_castSucc]

/-- Recover an arbitrary point on the sum hyperplane using the actual chart. -/
theorem append_init {n : ℕ} (phi : ℝ) (x : Fin (n+1) → ℝ)
    (hx : ∑ i, x i = phi) : append phi (fun i => x i.castSucc) = x := by
  have hs := Fin.sum_univ_castSucc x
  ext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [append, Fin.snoc_last]
    linarith
  · simp [append]

/-- The induced permutation in the free graph coordinates. -/
noncomputable def graphPerm {n : ℕ} (phi : ℝ) (p : Equiv.Perm (Fin (n+1)))
    (t : Fin n → ℝ) : Fin n → ℝ := fun i => append phi t (p i.castSucc)

/-- The graph action includes the omitted coordinate, not just free-coordinate relabeling. -/
theorem append_graphPerm {n : ℕ} (phi : ℝ) (p : Equiv.Perm (Fin (n+1)))
    (t : Fin n → ℝ) : append phi (graphPerm phi p t) = fun i => append phi t (p i) := by
  apply append_init phi (fun i => append phi t (p i))
  rw [Equiv.sum_comp p]
  exact append_sum phi t

/-- The graph action is a right action: coordinate pullback reverses composition. -/
theorem graphPerm_mul {n : ℕ} (phi : ℝ) (p q : Equiv.Perm (Fin (n+1)))
    (t : Fin n → ℝ) : graphPerm phi (p * q) t = graphPerm phi q (graphPerm phi p t) := by
  ext i
  exact (congrFun (append_graphPerm phi p t) (q i.castSucc)).symm

theorem graphPerm_one {n : ℕ} (phi : ℝ) (t : Fin n → ℝ) :
    graphPerm phi 1 t = t := by
  ext i
  simp [graphPerm, append]

/-- The linear part of the actual graph action. -/
noncomputable def graphLinear {n : ℕ} (p : Equiv.Perm (Fin (n+1))) :
    (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) where
  toFun := graphPerm 0 p
  map_add' x y := by
    funext i
    change graphPerm 0 p (x+y) i = graphPerm 0 p x i + graphPerm 0 p y i
    unfold graphPerm append
    generalize p i.castSucc = j
    refine Fin.lastCases ?_ (fun k => ?_) j
    · simp [Finset.sum_add_distrib]; ring
    · simp
  map_smul' c x := by
    funext i
    change graphPerm 0 p (c • x) i = c * graphPerm 0 p x i
    unfold graphPerm append
    generalize p i.castSucc = j
    refine Fin.lastCases ?_ (fun k => ?_) j
    · simp [Finset.mul_sum]
    · simp

theorem graphLinear_one {n : ℕ} : graphLinear (1 : Equiv.Perm (Fin (n+1))) = 1 := by
  apply LinearMap.ext
  intro t
  exact graphPerm_one 0 t

theorem graphLinear_mul {n : ℕ} (p q : Equiv.Perm (Fin (n+1))) :
    graphLinear (p*q) = graphLinear q * graphLinear p := by
  apply LinearMap.ext
  intro t
  exact graphPerm_mul 0 p q t

theorem graphLinear_pow {n : ℕ} (p : Equiv.Perm (Fin (n+1))) (k : ℕ) :
    graphLinear (p^k) = graphLinear p ^ k := by
  induction k with
  | zero => simp [graphLinear_one]
  | succ k ih => rw [pow_succ', graphLinear_mul, ih, pow_succ]

/-- Finite-order linear actions have unit absolute determinant. No permutation enumeration is used. -/
theorem graphLinear_abs_det {n : ℕ} (p : Equiv.Perm (Fin (n+1))) :
    |LinearMap.det (graphLinear p)| = 1 := by
  have hp : graphLinear p ^ Fintype.card (Equiv.Perm (Fin (n+1))) = 1 := by
    rw [← graphLinear_pow, pow_card_eq_one, graphLinear_one]
  have hd := congrArg LinearMap.det hp
  rw [map_pow, map_one] at hd
  apply (abs_pow_eq_one _ (ne_of_gt (Fintype.card_pos (α := Equiv.Perm (Fin (n+1)))))).mp
  rw [hd, abs_one]

/-- The actual graph action preserves ordinary free-coordinate Lebesgue measure. -/
theorem graphLinear_measurePreserving {n : ℕ} (p : Equiv.Perm (Fin (n+1))) :
    MeasurePreserving (graphLinear p) volume volume := by
  have hd := graphLinear_abs_det p
  refine ⟨(graphLinear p).continuous_on_pi.measurable, ?_⟩
  have hn : LinearMap.det (graphLinear p) ≠ 0 := by
    intro h
    rw [h, abs_zero] at hd
    exact zero_ne_one hd
  rw [Real.map_linearMap_volume_pi_eq_smul_volume_pi hn, abs_inv, hd]
  simp

theorem graphPerm_affine {n : ℕ} (phi : ℝ) (p : Equiv.Perm (Fin (n+1)))
    (t : Fin n → ℝ) : graphPerm phi p t = graphLinear p t + graphPerm phi p 0 := by
  funext i
  change append phi t (p i.castSucc) =
    append 0 t (p i.castSucc) + append phi 0 (p i.castSucc)
  unfold append
  generalize p i.castSucc = j
  refine Fin.lastCases ?_ (fun k => ?_) j
  · simp; ring
  · simp

/-- This is the graph-chart volume, not Hausdorff area; the result is uniform in phi. -/
theorem graphPerm_measurePreserving {n : ℕ} (phi : ℝ) (p : Equiv.Perm (Fin (n+1))) :
    MeasurePreserving (graphPerm phi p) volume volume := by
  have h := (measurePreserving_add_right volume (graphPerm phi p 0)).comp
    (graphLinear_measurePreserving p)
  convert h using 1
  funext t
  exact graphPerm_affine phi p t

theorem graphPerm_continuous {n : ℕ} (phi : ℝ) (p : Equiv.Perm (Fin (n+1))) :
    Continuous (graphPerm phi p) := by
  have he : graphPerm phi p = fun t => graphLinear p t + graphPerm phi p 0 := by
    funext t
    exact graphPerm_affine phi p t
  rw [he]
  exact (graphLinear p).continuous_on_pi.add continuous_const

/-- An explicit inverse, using the inverse permutation, for exact integral transport. -/
noncomputable def graphHomeomorph {n : ℕ} (phi : ℝ) (p : Equiv.Perm (Fin (n+1))) :
    (Fin n → ℝ) ≃ₜ (Fin n → ℝ) where
  toFun := graphPerm phi p
  invFun := graphPerm phi p⁻¹
  left_inv t := by rw [← graphPerm_mul, mul_inv_cancel, graphPerm_one]
  right_inv t := by rw [← graphPerm_mul, inv_mul_cancel, graphPerm_one]
  continuous_toFun := graphPerm_continuous phi p
  continuous_invFun := graphPerm_continuous phi p⁻¹

theorem integral_graphPerm {n : ℕ} (phi : ℝ) (p : Equiv.Perm (Fin (n+1)))
    (f : (Fin n → ℝ) → ℝ) :
    (∫ t, f (graphPerm phi p t)) = ∫ t, f t := by
  exact (graphPerm_measurePreserving phi p).integral_comp
    (graphHomeomorph phi p).toMeasurableEquiv.measurableEmbedding f

/-- Full reciprocal density is invariant before discarding the omitted reciprocal. -/
theorem graphPerm_reciprocal {n : ℕ} (phi : ℝ) (p : Equiv.Perm (Fin (n+1)))
    (t : Fin n → ℝ) :
    1 / (∏ i, append phi (graphPerm phi p t) i) = 1 / (∏ i, append phi t i) := by
  rw [append_graphPerm, Equiv.prod_comp p]

/-- Unsorted full-coordinate carrier: all coordinates, including the omitted one, are gated. -/
def graphBox {n : ℕ} (A B : Fin (n+1) → ℝ) (phi : ℝ) (t : Fin n → ℝ) : Prop :=
  ∀ i, A i ≤ append phi t i ∧ append phi t i ≤ B i

/-- The full zero-extended reciprocal, before any upper bounding operation. -/
noncomputable def graphWeight {n : ℕ} (A B : Fin (n+1) → ℝ) (phi : ℝ)
    (t : Fin n → ℝ) : ℝ :=
  if graphBox A B phi t then 1 / (∏ i, append phi t i) else 0

theorem graphBox_perm {n : ℕ} (A B : Fin (n+1) → ℝ) (phi : ℝ)
    (p : Equiv.Perm (Fin (n+1))) (hA : ∀ i, A (p i) = A i) (hB : ∀ i, B (p i) = B i)
    (t : Fin n → ℝ) : graphBox A B phi (graphPerm phi p t) ↔ graphBox A B phi t := by
  unfold graphBox
  rw [append_graphPerm]
  constructor
  · intro h i
    obtain ⟨j, rfl⟩ := p.surjective i
    simpa only [hA, hB] using h j
  · intro h i
    simpa only [hA, hB] using h (p i)

theorem graphWeight_perm {n : ℕ} (A B : Fin (n+1) → ℝ) (phi : ℝ)
    (p : Equiv.Perm (Fin (n+1))) (hA : ∀ i, A (p i) = A i) (hB : ∀ i, B (p i) = B i)
    (t : Fin n → ℝ) : graphWeight A B phi (graphPerm phi p t) = graphWeight A B phi t := by
  unfold graphWeight
  rw [graphBox_perm A B phi p hA hB, graphPerm_reciprocal]

/-- The full symmetric S6 action, with no omitted-coordinate exception. -/
theorem graphWeight21_perm (a b phi : ℝ) (p : Equiv.Perm (Fin 6)) (t : Fin 5 → ℝ) :
    graphWeight (fun _ => a) (fun _ => b) phi (graphPerm phi p t) =
      graphWeight (fun _ => a) (fun _ => b) phi t :=
  graphWeight_perm _ _ phi p (fun _ => rfl) (fun _ => rfl) t

/-- Lift the complete high-coordinate group while fixing the low coordinate literally. -/
def fixLow {r : ℕ} (p : Equiv.Perm (Fin r)) : Equiv.Perm (Fin (r+1)) where
  toFun := Fin.cases 0 (fun j => (p j).succ)
  invFun := Fin.cases 0 (fun j => (p⁻¹ j).succ)
  left_inv i := by refine Fin.cases ?_ (fun j => ?_) i <;> simp
  right_inv i := by refine Fin.cases ?_ (fun j => ?_) i <;> simp

@[simp] theorem fixLow_zero {r : ℕ} (p : Equiv.Perm (Fin r)) : fixLow p 0 = 0 := rfl
@[simp] theorem fixLow_succ {r : ℕ} (p : Equiv.Perm (Fin r)) (j : Fin r) :
    fixLow p j.succ = (p j).succ := rfl

/-- S4 fixes the low coordinate and permutes all four highs, including the omitted high. -/
theorem graphWeight20_perm (a2 a b phi : ℝ) (p : Equiv.Perm (Fin 4)) (t : Fin 4 → ℝ) :
    graphWeight (Fin.cons a2 (fun _ => a)) (Fin.cons a (fun _ => b)) phi
      (graphPerm phi (fixLow p) t) =
    graphWeight (Fin.cons a2 (fun _ => a)) (Fin.cons a (fun _ => b)) phi t := by
  apply graphWeight_perm
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp

/-- Weighted change of variables for any test function, with the whole density retained. -/
theorem integral_graphWeight_perm {n : ℕ} (A B : Fin (n+1) → ℝ) (phi : ℝ)
    (p : Equiv.Perm (Fin (n+1))) (hA : ∀ i, A (p i) = A i) (hB : ∀ i, B (p i) = B i)
    (f : (Fin n → ℝ) → ℝ) :
    (∫ t, graphWeight A B phi t * f (graphPerm phi p t)) =
      ∫ t, graphWeight A B phi t * f t := by
  calc
    _ = ∫ t, graphWeight A B phi (graphPerm phi p t) * f (graphPerm phi p t) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun t =>
        congrArg (fun w => w * f (graphPerm phi p t)) (graphWeight_perm A B phi p hA hB t).symm)
    _ = _ := integral_graphPerm phi p (fun t => graphWeight A B phi t * f t)

end Wu2008DoubleSieve.HighUnit
