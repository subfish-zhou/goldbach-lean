import MathlibNt.Wu2008DoubleSieve.SecondFunctionalPrimeRectangleIntegral
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalContinuousSlab

namespace Wu2008DoubleSieve
open Set MeasureTheory
open scoped BigOperators

noncomputable def gridWidth (k : ℕ) : ℝ := (2 / 5 : ℝ) / (k + 1)
noncomputable def gridNode (k j : ℕ) : ℝ := 1 / 10 + j * gridWidth k
abbrev GridIndex (n k : ℕ) := Fin n → Fin (k + 1)
/-- First interval is closed; all later intervals are left-open, right-closed. -/
def gridInterval (k : ℕ) (j : Fin (k + 1)) : Set ℝ :=
  {x | gridNode k j ≤ x ∧ x ≤ gridNode k (j.val + 1) ∧
    (j.val = 0 ∨ gridNode k j < x)}
def gridCell {n k : ℕ} (a : GridIndex n k) : Set (Fin n → ℝ) :=
  Set.pi Set.univ (fun i => gridInterval k (a i))
noncomputable def gridLower {n k : ℕ} (a : GridIndex n k) (i : Fin n) : ℝ :=
  gridNode k (a i)
noncomputable def gridUpper {n k : ℕ} (a : GridIndex n k) (i : Fin n) : ℝ :=
  gridNode k ((a i).val + 1)
noncomputable def gridCenter {n k : ℕ} (a : GridIndex n k) (i : Fin n) : ℝ :=
  (gridLower a i + gridUpper a i) / 2

theorem gridWidth_pos (k : ℕ) : 0 < gridWidth k := by
  unfold gridWidth
  positivity

theorem gridNode_zero (k : ℕ) : gridNode k 0 = 1 / 10 := by simp [gridNode]
theorem gridNode_last (k : ℕ) : gridNode k (k + 1) = 1 / 2 := by
  have h : (k : ℝ) + 1 ≠ 0 := by positivity
  simp only [gridNode, gridWidth, Nat.cast_add, Nat.cast_one]
  field_simp
  ring

theorem gridNode_strictMono (k : ℕ) : StrictMono (gridNode k) := by
  intro i j hij
  exact add_lt_add_right (mul_lt_mul_of_pos_right (show (i : ℝ) < (j : ℝ) by exact_mod_cast hij)
    (gridWidth_pos k)) _

theorem gridNode_step (k j : ℕ) : gridNode k (j + 1) = gridNode k j + gridWidth k := by
  simp only [gridNode, Nat.cast_add, Nat.cast_one]
  ring

theorem gridLower_bounds {n k : ℕ} (a : GridIndex n k) (i : Fin n) :
    1 / 10 ≤ gridLower a i ∧ gridLower a i < gridUpper a i ∧ gridUpper a i ≤ 1 / 2 := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [gridLower, gridNode_zero] using (gridNode_strictMono k).monotone (Nat.zero_le (a i).val)
  · exact gridNode_strictMono k (Nat.lt_succ_self _)
  · simpa [gridUpper, gridNode_last] using (gridNode_strictMono k).monotone (a i).isLt

theorem gridInterval_measurable (k : ℕ) (j : Fin (k + 1)) : MeasurableSet (gridInterval k j) := by
  by_cases hj : j.val = 0
  · have : gridInterval k j = Icc (gridNode k j) (gridNode k (j.val + 1)) := by
      ext x; simp [gridInterval, hj]
    rw [this]; exact measurableSet_Icc
  · have : gridInterval k j = Ioc (gridNode k j) (gridNode k (j.val + 1)) := by
      ext x; simp only [gridInterval, mem_ofPred_eq, hj, false_or, mem_Ioc]
      exact ⟨fun h => ⟨h.2.2, h.2.1⟩, fun h => ⟨h.1.le, h.2, h.1⟩⟩
    rw [this]; exact measurableSet_Ioc

theorem gridCell_measurable {n k : ℕ} (a : GridIndex n k) : MeasurableSet (gridCell a) :=
  MeasurableSet.pi Set.countable_univ (fun i _ => gridInterval_measurable k (a i))

theorem gridCell_subset_closed {n k : ℕ} (a : GridIndex n k) :
    gridCell a ⊆ continuousRectangle (gridLower a) (gridUpper a) := by
  intro t ht i hi
  exact ⟨(ht i hi).1, (ht i hi).2.1⟩

theorem gridClosed_subset_cube {n k : ℕ} (a : GridIndex n k) :
    continuousRectangle (gridLower a) (gridUpper a) ⊆ continuousCube n := by
  intro t ht i hi
  exact ⟨(gridLower_bounds a i).1.trans (ht i hi).1,
    (ht i hi).2.trans (gridLower_bounds a i).2.2⟩

theorem gridInterval_exists (k : ℕ) {x : ℝ} (hx : x ∈ Icc (1 / 10 : ℝ) (1 / 2)) :
    ∃ j : Fin (k + 1), x ∈ gridInterval k j := by
  have he : ∃ j : ℕ, x ≤ gridNode k (j + 1) := ⟨k, by simpa [gridNode_last] using hx.2⟩
  let j := Nat.find he
  have hu : x ≤ gridNode k (j + 1) := Nat.find_spec he
  have hj : j ≤ k := Nat.find_min' he (by simpa [gridNode_last] using hx.2)
  refine ⟨⟨j, by omega⟩, ?_⟩
  change gridNode k j ≤ x ∧ x ≤ gridNode k (j + 1) ∧ (j = 0 ∨ gridNode k j < x)
  by_cases hz : j = 0
  · exact ⟨by simpa [hz, gridNode_zero] using hx.1, hu, Or.inl hz⟩
  · have hl : gridNode k j < x := by
      have hm := Nat.find_min he (show j - 1 < j by omega)
      have hjj : j - 1 + 1 = j := by omega
      rw [hjj] at hm
      exact lt_of_not_ge hm
    exact ⟨hl.le, hu, Or.inr hl⟩

theorem gridInterval_unique {k : ℕ} {a b : Fin (k + 1)} {x : ℝ}
    (ha : x ∈ gridInterval k a) (hb : x ∈ gridInterval k b) : a = b := by
  suffices h : ¬ a.val < b.val by
    have h' : ¬ b.val < a.val := by
      intro hba
      have hnode := (gridNode_strictMono k).monotone (show b.val + 1 ≤ a.val by omega)
      have hstrict : gridNode k a < x := ha.2.2.resolve_left (by omega)
      linarith [hb.2.1]
    exact Fin.ext (by omega)
  intro hab
  have hnode := (gridNode_strictMono k).monotone (show a.val + 1 ≤ b.val by omega)
  have hstrict : gridNode k b < x := hb.2.2.resolve_left (by omega)
  linarith [ha.2.1]

theorem gridCell_partition {n k : ℕ} {t : Fin n → ℝ} :
    t ∈ continuousCube n ↔ ∃! a : GridIndex n k, t ∈ gridCell a := by
  constructor
  · intro ht
    choose a ha using fun i => gridInterval_exists k (ht i (mem_univ i))
    refine ⟨a, fun i _ => ha i, ?_⟩
    intro b hb
    funext i
    exact gridInterval_unique (hb i (mem_univ i)) (ha i)
  · rintro ⟨a, ha, _⟩
    exact gridClosed_subset_cube a (gridCell_subset_closed a ha)

theorem gridCell_disjoint {n k : ℕ} {a b : GridIndex n k} (hab : a ≠ b) :
    Disjoint (gridCell a) (gridCell b) := by
  rw [Set.disjoint_left]
  intro t ha hb
  apply hab
  funext i
  exact gridInterval_unique (ha i (mem_univ i)) (hb i (mem_univ i))

theorem gridCenter_mem {n k : ℕ} (a : GridIndex n k) : gridCenter a ∈ gridCell a := by
  intro i _
  have h := (gridLower_bounds a i).2.1
  change gridLower a i ≤ (gridLower a i + gridUpper a i) / 2 ∧
    (gridLower a i + gridUpper a i) / 2 ≤ gridUpper a i ∧
    ((a i).val = 0 ∨ gridLower a i < (gridLower a i + gridUpper a i) / 2)
  exact ⟨by linarith, by linarith, Or.inr (by linarith)⟩

theorem gridCell_oscillation {n k : ℕ} {a : GridIndex n k} {s t : Fin n → ℝ}
    (hs : s ∈ gridCell a) (ht : t ∈ gridCell a) (i : Fin n) : |s i - t i| ≤ gridWidth k := by
  have hsi := hs i (mem_univ i)
  have hti := ht i (mem_univ i)
  have hw := gridNode_step k (a i).val
  rw [abs_le]
  constructor <;> linarith [hsi.1, hsi.2.1, hti.1, hti.2.1]

theorem gridCell_zero_dim (k : ℕ) (a : GridIndex 0 k) : gridCell a = Set.univ := by
  ext t
  simp [gridCell, Set.mem_pi]

theorem gridCell_zero_mesh {n : ℕ} (a : GridIndex n 0) : gridCell a = continuousCube n := by
  apply Set.Subset.antisymm (fun _ ht => gridClosed_subset_cube a (gridCell_subset_closed a ht))
  intro t ht i hi
  have ha : (a i).val = 0 := by have := (a i).isLt; omega
  have hh := ht i hi
  change _ ≤ _ ∧ _ ≤ _ ∧ _
  norm_num [gridNode, gridWidth, ha] at *
  exact hh

theorem gridIndex_card (n k : ℕ) : Fintype.card (GridIndex n k) = (k + 1) ^ n := by
  simp [GridIndex]

theorem gridWidth_arbitrarily_small {ε : ℝ} (hε : 0 < ε) :
    ∃ k : ℕ, gridWidth k < ε := by
  obtain ⟨k, hk⟩ := exists_nat_gt ((2 / 5 : ℝ) / ε)
  refine ⟨k, ?_⟩
  unfold gridWidth
  apply (div_lt_iff₀ (by positivity : (0 : ℝ) < k + 1)).mpr
  have hh := (div_lt_iff₀ hε).mp hk
  nlinarith

theorem gridCell_left_endpoint (n k : ℕ) :
    (fun _ : Fin n => (1 / 10 : ℝ)) ∈ gridCell (fun _ => (0 : Fin (k + 1))) := by
  intro i _
  change gridNode k 0 ≤ 1 / 10 ∧ 1 / 10 ≤ gridNode k 1 ∧ (0 = 0 ∨ _)
  rw [gridNode_zero]
  exact ⟨le_refl _, (by simpa [gridNode_zero] using (gridNode_strictMono k).monotone (Nat.zero_le 1)), Or.inl rfl⟩

theorem gridCell_right_endpoint (n k : ℕ) :
    (fun _ : Fin n => (1 / 2 : ℝ)) ∈ gridCell (fun _ => Fin.last k) := by
  intro i _
  change gridNode k k ≤ 1 / 2 ∧ 1 / 2 ≤ gridNode k (k + 1) ∧ (k = 0 ∨ gridNode k k < 1 / 2)
  have hh : gridNode k k < 1 / 2 := by
    simpa [gridNode_last] using gridNode_strictMono k (Nat.lt_succ_self k)
  exact ⟨hh.le, by rw [gridNode_last], Or.inr hh⟩

end Wu2008DoubleSieve
